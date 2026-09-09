# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Windows desktop app (PySide6/Qt) that reconciles daily sales cashier reports for two independent business flows, referred to everywhere in code/UI as **EH** and **MVA**:

- **EH** (Eletrônica Horizonte): fully automated. Logs into the Zweb portal to pull `Pedidos importados`, `Fechamento de caixa`, and `Fiscal > NFC-e`, then reconciles against Caixa/Azulzinha card+PIX payment reports (downloaded via browser automation or read from local files).
- **MVA**: PDF-import based. User imports DAV/Orçamento/Fechamento PDFs (or the app reads them straight from the Clipp Firebird database via `clipp_mva.py`), then reconciles against Caixa/Azulzinha and, as a fallback, Cielo payment reports, plus fiscal checks against `Minhas Notas`.

Both flows produce a sectioned `Fechamento de Caixa` report (on-screen tables + A4 print/PDF export) showing matched payments, pending/unmatched items, and cancelled coupons.

A second, independent entry point (`agente_relatorios.py`) runs the same EH/MVA report generation **headless** (no Qt UI) on a schedule via Windows Task Scheduler, for unattended report generation to `Desktop\Relatorios`.

## Commands

```powershell
# Setup
python -m venv .venv64
.\.venv64\Scripts\Activate.ps1
pip install -r requirements.txt

# Run the desktop app
python main.py

# Build the packaged .exe (PyInstaller, onedir) + zip it for release
.\.venv64\Scripts\python.exe .\build.py

# Tests (plain pytest, no pytest.ini — tests/conftest.py puts repo root on sys.path)
.\.venv64\Scripts\python.exe -m pytest
.\.venv64\Scripts\python.exe -m pytest tests/test_utils.py::test_parse_number   # single test
.\.venv64\Scripts\python.exe -m pytest tests/test_clipp_mva.py                  # single file

# Headless report agent (used by the scheduled tasks, see below)
.\.venv64\Scripts\python.exe agente_relatorios.py --scope morning|afternoon [--date DD/MM/AAAA]
```

There is no linter/formatter config in this repo — don't invent one.

## Architecture

- `main.py` — trivial entry point, calls `qt_vendas.run_app()`.
- `qt_vendas.py` (~5.8k lines) — the entire Qt UI: `MainWindow`, all dialogs (`CaixaReportDialog`, `CaixaScopeDialog`, `CaixaSettingsDialog`, loading/status dialogs), table models, A4 printing, chart widgets. Imports business logic from `utils.py`/`clipp_mva.py` and calls it from Qt worker threads.
- `utils.py` (~19k lines) — the actual domain logic monolith: Zweb HTML scraping/parsing, Caixa/Azulzinha and Cielo browser automation (raw CDP over a launched Chromium process, not Selenium), Gmail OAuth + token-email polling (for Azulzinha/Cielo 2FA codes), PIX/card report parsing (CSV/XLSX/PDF, with XML/ZIP fallback parsers for malformed XLSX), EH/MVA bank reconciliation (`_comparar_caixa_fechamento_mva_com_pagamentos`, `_comparar_caixa_resumo_nfce_eh`, etc.), and report-scope filtering (morning/afternoon/full-day windows). New backend logic almost always belongs here or in a new module imported by it — check for an existing `_helper` before adding one, this file already has near-duplicate helpers for EH vs MVA in several places.
- `pdf_parser.py` — MVA PDF text/table extraction (pdfplumber) for DAV/Orçamento/Fechamento PDFs; re-exports many private helpers from `utils.py`.
- `clipp_mva.py` — reads MVA closing/payment data directly from the Clipp Firebird database (`firebirdsql`) as an alternative to importing PDFs. Connection is opt-in via `PDFREADER_CLIPP_PASSWORD` env var (see README env var list); returns `None`/no-op when unset.
- `models.py` — Pydantic models (`RelatorioCaixa`, `ItemCaixa`, `RelatorioResumoNFCE`, etc.) used for structured caixa report data.
- `global_vars.py` — mutable module-level app state (`APP_VERSION`, `LAST_MVA`/`LAST_EH`, `results_by_source`, compiled regexes) plus hardcoded service credentials; treat as legacy global state, not a config module to extend.
- `qt_adapters.py`, `ui_dialogs.py`, `library.py` — smaller shared UI/helper glue.
- `agente_relatorios.py` — headless CLI variant of the EH/MVA report pipeline (imports functions straight from `utils.py`/`clipp_mva.py`, no Qt). Writes final PDFs to `PDFREADER_REPORTS_DIR` (default `Desktop\Relatorios`), keeps a JSON execution-state audit trail under `.agent_execution_state/` and retry state under `.agent_retry_state/`, and stages intermediate downloads in a temp dir that gets cleaned up. Driven by `agente_relatorios.ps1` from Windows scheduled tasks (`Relatorios - Agente tarde 08h`, `... manha 13h30`, `... sabado 13h`) — schedule logic (no Sunday, no Monday morning) lives in `_scheduled_run_is_skipped`.
- `agendador_pdfreader.ps1` — separate scheduler script that just launches the packaged UI exe if not already running (different purpose than `agente_relatorios.ps1`).
- `build.py` / `versionfile_generator.py` — PyInstaller build; reads `APP_VERSION` from `global_vars.py`, bundles `data/`, `mapping.json`, icons, and zips `dist/Relatorio de Clientes` into `dist/RelatorioClientes-{version}.zip` for GitHub releases (the app self-updates from the GitHub releases ZIP).

### Automation/portal integration notes

- Portal automation (Zweb, Azulzinha/Caixa, Cielo) drives a real Chromium process launched via subprocess + raw DevTools Protocol (see `_launch_browser_process`, `_wait_for_devtools_ready` in `utils.py`), not a webdriver library. Each run uses a fresh temp browser profile.
- Azulzinha/Caixa and Cielo logins may require a token/2FA code; these are fetched by polling Gmail (OAuth, `_fetch_fiserv_token_from_gmail` / `_fetch_cielo_token_from_gmail`) rather than any SMS/manual flow, except Cielo CAPTCHA which always requires manual human resolution in a visible browser window.
- Portal state is tracked as an explicit state machine (`login`, `device`, `token`, `sales`) rather than inferred from URL alone — URL-only checks have caused false positives/negatives before; prefer visible-UI checks when touching this code.
- Azulzinha/Caixa currently serves two different "Vendas" screen layouts depending on the session (mid-migration on their end, with a "Novo Extrato / Versão anterior" toggle) — `utils.py` detects and handles both. The old layout is tab-based (`header[role="tablist"]`, separate PIX/Histórico tabs, one export per tab per establishment). The new layout is a single `MinhasVendas?Router=0` page identified by stable `data-testid` attributes (`vendas-btn-exportar`, `vendas-periodo-*`, `historico-vendas-gerar-arquivo`, etc.) whose one "Exportar relatório" action downloads ONE unified XLSX with PIX + card sales together across all establishments; `_write_azulzinha_unified_report_files` splits that back into the legacy-shaped card XLSX / PIX CSV so the rest of the pipeline (`_build_card_reports_from_caixa_xlsx`, `_build_pix_report_from_caixa_csv`) doesn't need to know the difference. A first-run onboarding tour can cover the new screen on a fresh browser profile and must be dismissed before clicking Exportar.
- Local payment report files follow naming conventions the reconciliation code depends on: `..._eh_auto` / `..._mva_auto` (company-bound, never cross-reused) and `..._est<N>` (per-establishment Azulzinha exports — the consolidated `_mva_auto.xlsx` is preferred over these). Card XLSX reports must be deduplicated by (establishment, authorization, time, product, value) to avoid double-counting.
- Set `PDFREADER_SHOW_BROWSER=1` (or drop a `mostrar_navegador.txt` next to the exe) to keep automation browser windows visible for debugging; portal automation runs off-screen/minimized by default.

## Sensitive/local files (gitignored, do not commit)

`credenciais.txt`, `gmail_oauth_client.json`, `gmail_oauth_token.json`, `data/credenciaisAPI.json`, `data/credenciaisDB.json`, browser profile dirs (`azulzinha_browser/`, `cielo_browser/`), and `AGENTS.md` are all local-only per `.gitignore`. Generated reports (PDF/CSV/XLSX matching the bank-report naming patterns) and most debug artifacts are also gitignored — the app deletes its own generated/downloaded artifacts on close to keep the workspace clean between runs.

`global_vars.py`, however, **is** tracked and currently hardcodes real service passwords — be careful when editing/displaying it, and don't add further plaintext credentials to tracked files.

## Repo-local agent rules

An `AGENTS.md` file exists in this repo (local-only, gitignored) with machine/session-specific rules — e.g. never push without explicit approval, update `README.md` for user-facing changes, center UI text by default, fix PT-BR mojibake with `ftfy`, and treat `D:\pdfReader` as the only canonical worktree (not the `C:\Users\...\Desktop\pdfReader` copies). Follow it if present.

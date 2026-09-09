import json
import os
import sys
import threading
import time
import zipfile
from datetime import date, datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import pytest
import agente_relatorios
import utils
from utils import (
    _active_report_dir,
    _azulzinha_sales_period_shortcut,
    _is_azulzinha_captcha_page,
    parse_number,
    format_number_br,
    _build_card_reports_from_cielo,
    _classify_caixa_document,
    _find_eh_local_payment_reports,
    _filter_zweb_fechamento_to_sales_date,
    get_gmail_oauth_status,
    _is_eh_counter_client,
    _merge_card_machine_report,
    _project_base_dir,
    _mva_caixa_reports_refresh_needs,
    _mva_cielo_pending_card_count,
    _mva_cielo_needed_card_keys,
    _normalize_fiscal_number,
    _refresh_mva_caixa_reports_if_needed,
    _run_gmail_oauth_local_server,
    _wait_for_cielo_downloaded_report,
    _zweb_fechamento_has_sales_outside_date,
    analisar_pdf_fechamento_caixa_mva_clipp,
    aplicar_escopo_relatorio_caixa,
    criar_relatorio_orcamentos_mva_vazio,
    describe_closing_scope,
)

def test_parse_number():
    assert parse_number("R$ 1.500,20") == 1500.20
    assert parse_number("1.500,20") == 1500.20
    assert parse_number("1,500.20") == 1500.20
    assert parse_number("20,50") == 20.50
    assert parse_number("100.00") == 100.00


def test_azulzinha_login_rejected_message_points_to_credentials_file():
    message = utils._format_azulzinha_login_rejected_message("Usuario ou senha incorretos.", "EH")

    assert "Credenciais mudaram?" in message
    assert "credenciais.txt" in message
    assert "CONTA AZULZINHA / CAIXA" in message
    assert "Usuario ou senha incorretos." in message


def test_azulzinha_captcha_page_is_detected_by_radware_url():
    assert _is_azulzinha_captcha_page(
        "https://validate.perfdrive.com/challenge?return=https%3A%2F%2Fportal.azulzinhadacaixa.com.br%2FMinhasVendas",
        "",
        "",
        (),
    ) is True


def test_azulzinha_captcha_page_is_detected_by_hcaptcha_frame():
    assert _is_azulzinha_captcha_page(
        "https://portal.azulzinhadacaixa.com.br/Home",
        "Portal AZULZINHA",
        "Verificação de segurança",
        ("https://newassets.hcaptcha.com/captcha/v1/123.html",),
    ) is True


def test_azulzinha_home_without_captcha_is_not_flagged():
    assert _is_azulzinha_captcha_page(
        "https://portal.azulzinhadacaixa.com.br/Home",
        "Portal AZULZINHA",
        "Vendas hoje",
        (),
    ) is False


def test_azulzinha_sales_period_shortcut_uses_ontem_only_for_previous_day():
    assert _azulzinha_sales_period_shortcut("20/08/2026", reference_date=date(2026, 8, 21)) == "ontem"
    assert _azulzinha_sales_period_shortcut("21/08/2026", reference_date=date(2026, 8, 21)) is None


def test_azulzinha_sales_period_shortcut_rejects_invalid_or_older_dates():
    assert _azulzinha_sales_period_shortcut("19/08/2026", reference_date=date(2026, 8, 21)) is None
    assert _azulzinha_sales_period_shortcut("data invalida", reference_date=date(2026, 8, 21)) is None


def test_load_zweb_credentials_selects_the_horizonte_account_by_index(tmp_path, monkeypatch):
    credentials_file = tmp_path / "credenciais.txt"
    credentials_file.write_text(
        "\n".join(
            [
                "CONTA ZWEB:",
                "mva@example.test",
                "mva-password",
                "https://mva.example.test",
                "CONTA ZWEB:",
                "horizonte@example.test",
                "horizonte-password",
                "https://horizonte.example.test",
            ]
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(utils, "_runtime_file_path", lambda _filename: credentials_file)

    credentials = utils._load_zweb_credentials(account_index=1)

    assert credentials is not None
    assert credentials["username"] == "horizonte@example.test"
    assert credentials["base_url"] == "https://horizonte.example.test"


def test_zweb_fechamento_caixa_html_parser_handles_current_section_layout():
    html = """
    <html><body>
      <div class="mt-4">
        <div class="d-flex justify-content-between">
          <div class="fw-bolder fs-6">Caixa 001 | Cartão de Débito</div>
          <div>
            <span class="fw-bolder">Abertura: </span>07/07/2026 07:58:05
            <span class="fw-bolder">Fechamento: </span>07/07/2026 13:58:22
          </div>
        </div>
      </div>
      <table class="striped-table mt-2">
        <tr><th>Nota Fiscal</th><th>Data</th><th>Total R$</th></tr>
        <tr><td>00106855</td><td>07/07/26</td><td class="text-end"><div>R$ 58,01</div></td></tr>
        <tr><td>00106857</td><td>07/07/26</td><td class="text-end"><div>R$ 29,20</div></td></tr>
      </table>
      <div class="totalizer-footer"><div class="footer-content">Total R$ 87,21</div></div>
      <table class="striped-table totalizers-table">
        <tr><th>Descricao</th><th>Total</th></tr>
        <tr><td>Cartão de Débito</td><td>R$ 87,21</td></tr>
        <tr><td>Abertura</td><td>R$ 500,00</td></tr>
        <tr><td>Sangria</td><td>R$ 0,00</td></tr>
        <tr><td>Total geral</td><td>R$ 587,21</td></tr>
      </table>
    </body></html>
    """

    report = utils._analisar_html_fechamento_caixa_eh(html)

    assert report["quantidade_nfce"] == 2
    assert report["total_nfce"] == 87.21
    assert report["total_geral"] == 587.21
    assert report["fechamento_janelas"] == [
        {"abertura": "07/07/2026 07:58:05", "fechamento": "07/07/2026 13:58:22"}
    ]
    debit = report["relatorios_pagamento"]["cartao_debito"]
    assert debit["quantidade_autorizados"] == 2
    assert debit["total_autorizado"] == 87.21
    assert debit["consistente"] is True


def test_cleanup_generated_auto_reports_removes_runtime_artifacts(tmp_path, monkeypatch):
    monkeypatch.setattr(utils, "CIELO_DEBUG_LOGS_ENABLED", False)
    should_delete = [
        "body_email.txt",
        "debug_zweb.html",
        "azulzinha_login_wait_state.json",
        "azulzinha_export_debug_pix.html",
        "cielo_mva_debug_26052026_120000.log",
        "cielo_snapshot_26052026_login.html",
        "Relatorio_de_Vendas_Pix_26-05-2026_eh_auto.csv",
        "Historico_Simplificado_de_vendas_26-05-2026_mva_auto.xlsx",
        "Pedidos_importados_26-05-2026_eh_zweb_auto.html",
    ]
    should_keep = [
        "credenciais.txt",
        "gmail_oauth_token.json",
        "relatorio_final_usuario.pdf",
    ]
    for name in should_delete + should_keep:
        (tmp_path / name).write_text("x", encoding="utf-8")
    for dirname in ("azulzinha_browser", "cielo_browser"):
        (tmp_path / dirname / "run_x").mkdir(parents=True)

    utils.cleanup_generated_auto_reports(tmp_path)

    assert all(not (tmp_path / name).exists() for name in should_delete)
    assert all((tmp_path / name).exists() for name in should_keep)
    assert not (tmp_path / "azulzinha_browser").exists()
    assert not (tmp_path / "cielo_browser").exists()


def test_cleanup_generated_auto_reports_preserves_cielo_debug_when_enabled(tmp_path, monkeypatch):
    monkeypatch.setattr(utils, "CIELO_DEBUG_LOGS_ENABLED", True)
    debug_log = tmp_path / "cielo_mva_debug_26052026_120000.log"
    snapshot = tmp_path / "cielo_snapshot_26052026_login.html"
    debug_log.write_text("x", encoding="utf-8")
    snapshot.write_text("x", encoding="utf-8")

    utils.cleanup_generated_auto_reports(tmp_path)

    assert debug_log.exists()
    assert not snapshot.exists()


def test_find_local_payment_reports_suppresses_wrong_date_warning_when_valid_file_exists(tmp_path, monkeypatch):
    old_report = tmp_path / "Relatorio_de_Vendas_Pix_07-07-2026_eh_auto.csv"
    current_report = tmp_path / "Relatorio_de_Vendas_Pix_08-07-2026_eh_auto.csv"
    old_report.write_text("Data da venda;Valor bruto\n07/07/2026;10,00\n", encoding="utf-8")
    current_report.write_text("Data da venda;Valor bruto\n08/07/2026;20,00\n", encoding="utf-8")
    monkeypatch.setattr(utils, "_candidate_local_report_dirs", lambda: [tmp_path])

    found = _find_eh_local_payment_reports("08/07/2026", company="EH")

    assert found["pix"] == str(current_report)
    assert found["avisos"] == []


def test_wait_for_downloaded_report_also_checks_active_report_dir(tmp_path, monkeypatch):
    browser_dir = tmp_path / "browser_downloads"
    active_dir = tmp_path / "app"
    browser_dir.mkdir()
    active_dir.mkdir()
    report = active_dir / "Historico_Simplificado_de_vendas_26-05-2026_eh_auto.csv"
    report.write_text(
        "\n".join(
            [
                "Data da venda;Produto;Status;Valor bruto",
                "26/05/2026 as 08:10;Credito;Aprovada;100,00",
            ]
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(utils, "_active_report_dir", lambda: str(active_dir))

    found = utils._wait_for_downloaded_report(
        str(browser_dir),
        "26/05/2026",
        "cartoes",
        report.stat().st_mtime - 1,
        timeout=0.0,
    )

    assert found == str(report)


def test_wait_for_downloaded_report_ignores_mtime_skew_in_primary_download_dir(tmp_path):
    browser_dir = tmp_path / "browser_downloads"
    browser_dir.mkdir()
    report = browser_dir / "Relatorio_Simplificado_de_Vendas_Historico_de_Vendas_26-05-2026_0930.xlsx"
    report.write_text(
        "\n".join(
            [
                "Relatório de vendas_Histórico de vendas",
                "Período de Venda:  25/05/2026 à 25/05/2026",
                "Data da venda;Cód. de autorização;Produto;Parcelas;Bandeira;Valor bruto;Status",
                "25/05/2026 08:10:00;ABC123;Crédito à vista;-;Mastercard;100,00;Aprovada",
            ]
        ),
        encoding="utf-8",
    )

    found = utils._wait_for_downloaded_report(
        str(browser_dir),
        "25/05/2026",
        "cartoes",
        report.stat().st_mtime + 600,
        timeout=0.0,
    )

    assert found == str(report)


def test_wait_for_downloaded_report_does_not_accept_pix_as_card(tmp_path):
    browser_dir = tmp_path / "browser_downloads"
    browser_dir.mkdir()
    pix = browser_dir / "Relatorio_de_Vendas_Pix_26-05-2026_0930.xlsx"
    pix.write_text(
        "\n".join(
            [
                "Relatório de Vendas Pix",
                "Período de Venda:  25/05/2026 à 25/05/2026",
                "Data da venda;Cód. de autorização;Valor bruto;Terminal;Status",
                "25/05/2026 às 08:10;SE001;100,00;APT36A49;Aprovada",
            ]
        ),
        encoding="utf-8",
    )

    found = utils._wait_for_downloaded_report(
        str(browser_dir),
        "25/05/2026",
        "cartoes",
        pix.stat().st_mtime - 1,
        timeout=0.0,
    )

    assert found is None


def test_extract_local_report_date_prefers_sales_period_over_emission_date():
    text = "\n".join(
        [
            "Relatorio de Vendas Pix",
            "Emitido em: 26/05/2026 09:33:10",
            "Periodo de Venda: 25/05/2026 ate 25/05/2026",
            "Valor total de vendas finalizadas: R$ 1.234,56",
        ]
    )

    assert utils._extract_local_report_date_br(text) == "25/05/2026"


def test_wait_for_downloaded_report_accepts_pix_xlsx_named_by_download_date(tmp_path):
    pd = pytest.importorskip("pandas")
    browser_dir = tmp_path / "browser_downloads"
    browser_dir.mkdir()
    report = browser_dir / "Relatorio_de_Vendas_Pix_26-05-2026_0933.xlsx"
    pd.DataFrame(
        [
            ["Relatorio de Vendas Pix"],
            ["Emitido em: 26/05/2026 09:33:10"],
            ["Periodo de Venda: 25/05/2026 ate 25/05/2026"],
            ["Valor total de vendas finalizadas: R$ 1.234,56"],
        ]
    ).to_excel(report, index=False, header=False)

    found = utils._wait_for_downloaded_report(str(browser_dir), "25/05/2026", "pix", time.time() - 5, timeout=0.1)

    assert found is not None
    assert Path(found).suffix == ".csv"


def test_caixa_card_report_reads_xls_tabular_text(tmp_path):
    report = tmp_path / "Historico_Simplificado_de_vendas_26-05-2026_eh_auto.xls"
    report.write_text(
        "\n".join(
            [
                "Data da venda;Cód. de autorização;Produto;Status;Valor bruto",
                "26/05/2026 às 08:10;ABC123;Crédito;Aprovada;100,00",
                "26/05/2026 às 08:12;DEF456;Débito;Autorizada;50,00",
            ]
        ),
        encoding="utf-8",
    )

    result = utils._build_card_reports_from_caixa(str(report), "26/05/2026")

    assert result["cartao_credito_caixa"]["total_autorizado"] == 100.0
    assert result["cartao_debito_caixa"]["total_autorizado"] == 50.0
    assert parse_number(15.5) == 15.5
    assert parse_number(None) == 0.0
    assert parse_number(" ") == 0.0


def test_caixa_card_report_deduplicates_same_authorization_across_establishments(tmp_path):
    openpyxl = pytest.importorskip("openpyxl")
    report = tmp_path / "Historico_Simplificado_de_vendas_08-06-2026_mva_auto.xlsx"
    workbook = openpyxl.Workbook()
    sheet = workbook.active
    sheet.append(
        [
            "Data da venda",
            "Cód. de autorização",
            "Comprovante da venda",
            "Produto",
            "Parcelado",
            "Bandeira",
            "Canal",
            "Terminal",
            "Valor bruto",
            "Status",
            "Número do estabelecimento",
        ]
    )
    sheet.append(["08/06/2026 às 08:25", "ABC123", "ABC123", "Crédito", "-", "", "", "", 100.0, "Autorizada", "91111977"])
    sheet.append(["08/06/2026 às 08:25", "ABC123", "ABC123", "Crédito", "-", "", "", "", 100.0, "Autorizada", "91119212"])
    sheet.append(["08/06/2026 às 08:30", "DEF456", "DEF456", "Débito", "-", "", "", "", 50.0, "Autorizada", "91111977"])
    workbook.save(report)

    result = utils._build_card_reports_from_caixa(str(report), "08/06/2026")

    assert result["cartao_credito_caixa"]["quantidade_autorizados"] == 1
    assert result["cartao_credito_caixa"]["total_autorizado"] == 100.0
    assert result["cartao_debito_caixa"]["quantidade_autorizados"] == 1
    assert result["cartao_debito_caixa"]["total_autorizado"] == 50.0


def test_format_number_br():
    assert format_number_br(1500.2) == "1.500,20"
    assert format_number_br(20.5) == "20,50"
    assert format_number_br(0.0) == "0,00"

def test_classify_caixa_document():
    assert _classify_caixa_document("Venda  ") == "Venda"
    assert _classify_caixa_document("Nota Fiscal  Eletrônica") == "Nota Fiscal Eletronica"
    assert _classify_caixa_document("NFC-e") == "NFC-e"

def test_is_eh_counter_client():
    assert _is_eh_counter_client("CLIENTE BALCÃO") is True
    assert _is_eh_counter_client("Cliente Joao") is False

def test_normalize_fiscal_number():
    assert _normalize_fiscal_number("1234") == "000001234"
    assert _normalize_fiscal_number("0001234") == "000001234"


def test_active_report_dir_prefers_frozen_executable_folder(tmp_path, monkeypatch):
    app_dir = tmp_path / "dist" / "Relatorio de Clientes"
    app_dir.mkdir(parents=True)
    exe_path = app_dir / "Relatorio de Clientes.exe"
    exe_path.write_text("", encoding="utf-8")

    monkeypatch.setattr("sys.frozen", True, raising=False)
    monkeypatch.setattr("sys.executable", str(exe_path))

    assert _active_report_dir() == str(app_dir)


def test_project_base_dir_prefers_frozen_executable_folder(tmp_path, monkeypatch):
    app_dir = tmp_path / "dist" / "Relatorio de Clientes"
    app_dir.mkdir(parents=True)
    exe_path = app_dir / "Relatorio de Clientes.exe"
    exe_path.write_text("", encoding="utf-8")

    monkeypatch.setattr("sys.frozen", True, raising=False)
    monkeypatch.setattr("sys.executable", str(exe_path))

    assert _project_base_dir() == str(app_dir)


def test_gmail_oauth_server_honors_pre_cancelled_event():
    cancel_event = threading.Event()
    cancel_event.set()

    with pytest.raises(RuntimeError, match="__cancelled__"):
        _run_gmail_oauth_local_server(object(), cancel_event=cancel_event)


def test_zweb_browser_profile_uses_the_pdfreader_runtime_not_appdata(tmp_path, monkeypatch):
    runtime_dir = tmp_path / "pdfReader"
    runtime_dir.mkdir()
    monkeypatch.setattr(utils, "_canonical_runtime_dir", lambda: runtime_dir)
    monkeypatch.setenv("LOCALAPPDATA", r"C:\Users\TI\AppData\Local")
    monkeypatch.setenv("APPDATA", r"C:\Users\TI\AppData\Roaming")

    profile_dir = utils._zweb_browser_profile_dir()

    assert Path(profile_dir) == runtime_dir / "runtime" / "zweb_browser_profile"
    assert Path(profile_dir).is_dir()


def test_zweb_debug_keeps_browser_open_only_when_the_visible_mode_is_enabled(monkeypatch):
    monkeypatch.setenv("PDFREADER_SHOW_BROWSER", "1")
    monkeypatch.setenv("PDFREADER_KEEP_BROWSER_OPEN", "true")
    assert utils._browser_debug_keep_open_enabled() is True

    monkeypatch.setenv("PDFREADER_SHOW_BROWSER", "0")
    assert utils._browser_debug_keep_open_enabled() is False


def test_gmail_oauth_status_reports_missing_token(tmp_path, monkeypatch):
    (tmp_path / "gmail_oauth_client.json").write_text(
        json.dumps({"installed": {"client_id": "client", "client_secret": "secret"}}),
        encoding="utf-8",
    )
    monkeypatch.setenv("GMAIL_OAUTH_CLIENT_ID", "")
    monkeypatch.setenv("GMAIL_OAUTH_CLIENT_SECRET", "")
    monkeypatch.setattr(utils, "_canonical_runtime_dir", lambda: tmp_path)
    monkeypatch.setattr(utils, "_runtime_user_dir", lambda: str(tmp_path))
    monkeypatch.setattr(utils, "_active_report_dir", lambda: str(tmp_path))

    status = get_gmail_oauth_status()

    assert status["needs_auth"] is True
    assert status["status"] == "missing_token"


def test_gmail_oauth_status_finds_client_in_canonical_runtime_dir(tmp_path, monkeypatch):
    canonical_dir = tmp_path / "pdfReader"
    app_dir = canonical_dir / "dist" / "Relatorio de Clientes"
    canonical_dir.mkdir()
    app_dir.mkdir(parents=True)
    (canonical_dir / "gmail_oauth_client.json").write_text(
        json.dumps({"installed": {"client_id": "client", "client_secret": "secret"}}),
        encoding="utf-8",
    )

    monkeypatch.setenv("GMAIL_OAUTH_CLIENT_ID", "")
    monkeypatch.setenv("GMAIL_OAUTH_CLIENT_SECRET", "")
    monkeypatch.setattr(utils, "_canonical_runtime_dir", lambda: canonical_dir)
    monkeypatch.setattr(utils, "_runtime_user_dir", lambda: str(app_dir))
    monkeypatch.setattr(utils, "_active_report_dir", lambda: str(app_dir))

    status = get_gmail_oauth_status()

    assert status["needs_auth"] is True
    assert status["status"] == "missing_token"
    assert status["client_path"] == str(canonical_dir / "gmail_oauth_client.json")
    assert status["token_path"] == str(canonical_dir / "gmail_oauth_token.json")


def test_cielo_gmail_token_uses_recent_fallback_when_timestamp_filter_misses(monkeypatch):
    class FakeResponse:
        status_code = 200

        def __init__(self, payload):
            self._payload = payload

        def json(self):
            return self._payload

        def raise_for_status(self):
            return None

    class FakeSession:
        def get(self, url, params=None, timeout=None):
            if url.endswith("/messages"):
                return FakeResponse({"messages": [{"id": "msg_new"}, {"id": "msg_old"}]})
            msg_id = url.rsplit("/", 1)[-1]
            fmt = (params or {}).get("format")
            if fmt == "metadata":
                internal_date = "100000" if msg_id == "msg_new" else "90000"
                return FakeResponse(
                    {
                        "id": msg_id,
                        "internalDate": internal_date,
                        "payload": {
                            "headers": [
                                {"name": "Subject", "value": "Cielo | Confirmação de e-mail"},
                                {"name": "From", "value": "Cielo <cielo@comunica.cielo.com.br>"},
                            ]
                        },
                    }
                )
            token = "903863" if msg_id == "msg_new" else "751036"
            return FakeResponse(
                {
                    "id": msg_id,
                    "internalDate": "100000" if msg_id == "msg_new" else "90000",
                    "payload": {},
                    "snippet": f"Para sua segurança, use o código de verificação abaixo: {token}",
                }
            )

    monkeypatch.setattr(utils, "_cielo_gmail_session", lambda **_kwargs: FakeSession())
    debug_info = {}

    token = utils._fetch_cielo_token_from_gmail(
        timeout=0.1,
        min_internal_ts=100.5,
        debug_info=debug_info,
    )

    assert token == "903863"
    assert debug_info["candidate_count"] == 0
    assert debug_info["fallback_candidate_count"] == 2
    assert debug_info["selected_lookup_mode"] == "latest_recent"


def test_cielo_gmail_token_does_not_use_stale_fallback(monkeypatch):
    class FakeResponse:
        status_code = 200

        def __init__(self, payload):
            self._payload = payload

        def json(self):
            return self._payload

        def raise_for_status(self):
            return None

    class FakeSession:
        def get(self, url, params=None, timeout=None):
            if url.endswith("/messages"):
                return FakeResponse({"messages": [{"id": "msg_old"}]})
            msg_id = url.rsplit("/", 1)[-1]
            fmt = (params or {}).get("format")
            if fmt == "metadata":
                return FakeResponse(
                    {
                        "id": msg_id,
                        "internalDate": "100000",
                        "payload": {
                            "headers": [
                                {"name": "Subject", "value": "Cielo | Confirmação de e-mail"},
                                {"name": "From", "value": "Cielo <cielo@comunica.cielo.com.br>"},
                            ]
                        },
                    }
                )
            return FakeResponse(
                {
                    "id": msg_id,
                    "internalDate": "100000",
                    "payload": {},
                    "snippet": "Para sua segurança, use o código de verificação abaixo: 903863",
                }
            )

    monkeypatch.setattr(utils, "_cielo_gmail_session", lambda **_kwargs: FakeSession())
    monkeypatch.setattr(utils, "_sleep_with_cancel", lambda *_args, **_kwargs: None)
    debug_info = {}

    token = utils._fetch_cielo_token_from_gmail(
        timeout=0.1,
        min_internal_ts=500.0,
        debug_info=debug_info,
    )

    assert token is None
    assert debug_info["candidate_count"] == 0
    assert debug_info["fallback_candidate_count"] == 0


def test_build_card_reports_from_cielo_csv(tmp_path):
    caminho = tmp_path / "relatorio_cielo.csv"
    caminho.write_text(
        "\n".join(
            [
                "Relatorio Cielo",
                "Data da venda;Hora;Forma de pagamento;Status;Valor da venda;Codigo de autorizacao",
                "05/05/2026;13:45;Credito a vista;Aprovada;R$ 100,50;000123",
                "05/05/2026;14:10;Debito;Autorizada;50,00;000124",
                "05/05/2026;15:00;Credito;Cancelada;70,00;000125",
                "04/05/2026;16:00;Credito;Aprovada;20,00;000126",
            ]
        ),
        encoding="utf-8",
    )

    reports = _build_card_reports_from_cielo(str(caminho), "05/05/2026")

    assert reports["cartao_credito_caixa"]["quantidade_autorizados"] == 1
    assert reports["cartao_credito_caixa"]["total_autorizado"] == 100.50
    assert reports["cartao_debito_caixa"]["quantidade_autorizados"] == 1
    assert reports["cartao_debito_caixa"]["total_autorizado"] == 50.00


def test_mva_cielo_fallback_can_be_disabled(monkeypatch):
    def fail_if_called(*_args, **_kwargs):
        raise AssertionError("Cielo should not be consulted")

    monkeypatch.setattr(utils, "_find_local_cielo_card_report", fail_if_called)
    monkeypatch.setattr(utils, "baixar_relatorio_cielo_mva", fail_if_called)

    fechamento = {
        "relatorios_pagamento": {
            "cartao_credito": {
                "total_autorizado": 100.0,
                "itens_autorizados": [{"valor_bruto": 100.0}],
            },
            "cartao_credito_caixa": {
                "total_autorizado": 0.0,
                "itens_autorizados": [],
            },
        }
    }

    result, avisos = utils._integrate_cielo_card_reports_if_needed(
        fechamento,
        "09/06/2026",
        auto_download_missing=True,
        allow_cielo_fallback=False,
    )

    assert result is fechamento
    assert avisos == []


def test_empty_mva_budget_report_combines_without_changing_davs():
    davs = {
        "arquivo": "dav.pdf",
        "caixa_modelo": "MVA",
        "arquivo_tipo": "exportacao_dados_mva",
        "periodo": "25/05/2026 - 25/05/2026",
        "pedidos_total": 1,
        "pedidos_caixa": 1,
        "pedidos_excluidos": 0,
        "pedidos_editando": 0,
        "pedidos_outros_status": 0,
        "total_documento": 10.0,
        "total_excluido": 0.0,
        "total_caixa": 10.0,
        "itens_caixa": [{"pedido": "123456", "valor": 10.0, "ordem": "2026-05-25 08:00:00"}],
        "itens_excluidos": [],
    }

    combined = utils.combinar_relatorios_caixa_mva([davs, criar_relatorio_orcamentos_mva_vazio(davs["periodo"])])

    assert combined["pedidos_total"] == 1
    assert combined["total_caixa"] == 10.0
    assert combined["periodo"] == "25/05/2026 - 25/05/2026"


def test_build_card_reports_from_cielo_csv_prefers_transaction_header(tmp_path):
    caminho = tmp_path / "relatorio_cielo_detalhado.csv"
    caminho.write_text(
        "\n".join(
            [
                "Consolidado de vendas Cielo",
                "Formas de pagamento;Quantidade de vendas;Valor bruto;Taxa/tarifa;Valor liquido",
                "Credito a vista;43;2.013,25;-72,74;1.940,51",
                "Data da venda;Forma de pagamento;Quantidade de vendas;Valor bruto;Valor Taxa/Tarifa;Valor liquido",
                "30/04/2026;Credito a vista;43;2.013,25;-72,74;1.940,51",
                "Detalhamento de vendas Cielo",
                "Data da venda;Hora;Forma de pagamento;Status;Valor bruto;Codigo de autorizacao",
                "30/04/2026;10:20;Credito a vista;Aprovada;R$ 90,00;123456",
                "30/04/2026;11:15;Debito;Autorizada;R$ 40,00;123457",
            ]
        ),
        encoding="utf-8",
    )

    reports = _build_card_reports_from_cielo(str(caminho), "30/04/2026")

    assert reports["cartao_credito_caixa"]["quantidade_autorizados"] == 1
    assert reports["cartao_credito_caixa"]["total_autorizado"] == 90.00
    assert reports["cartao_debito_caixa"]["quantidade_autorizados"] == 1
    assert reports["cartao_debito_caixa"]["total_autorizado"] == 40.00


def test_wait_for_cielo_downloaded_report_accepts_requested_date_filename(tmp_path):
    caminho = tmp_path / "Vendas_Cielo_historico_resumo-20260430-20260430-1-1-csv.csv"
    caminho.write_text("arquivo resumido aguardando processamento\n", encoding="utf-8")

    found = _wait_for_cielo_downloaded_report(str(tmp_path), "30/04/2026", time.time() - 5, timeout=0.1)

    assert found == str(caminho)


def test_cielo_reports_tab_defers_to_its_single_native_click():
    source = Path(utils.__file__).read_text(encoding="utf-8")
    reports_tab_start = source.index("async def click_cielo_sales_reports_tab")
    reports_tab_end = source.index("async def click_cielo_sales_detail_tab", reports_tab_start)
    reports_tab_source = source[reports_tab_start:reports_tab_end]

    assert "chosen.e.click();" not in reports_tab_source


def test_cielo_report_download_uses_the_table_cell_when_the_icon_has_no_click_area():
    source = Path(utils.__file__).read_text(encoding="utf-8")
    download_start = source.index("async def click_cielo_ready_report_download")
    download_end = source.index("async def click_cielo_sales_reports_tab", download_start)
    download_source = source[download_start:download_end]

    assert "icon.closest('td')" in download_source


def test_cielo_report_download_targets_the_last_cell_of_the_matching_table_row():
    source = Path(utils.__file__).read_text(encoding="utf-8")
    download_start = source.index("async def click_cielo_ready_report_download")
    download_end = source.index("async def click_cielo_sales_reports_tab", download_start)
    download_source = source[download_start:download_end]

    assert "row.querySelector('td:last-child')" in download_source
    assert "matching_report_row_last_cell" in download_source


def test_cielo_historical_date_validation_accepts_start_and_end_in_separate_inputs():
    source = Path(utils.__file__).read_text(encoding="utf-8")
    date_selector_start = source.index("async def select_cielo_historical_sale_date")
    date_selector_end = source.index("async def dismiss_cielo_overlays", date_selector_start)
    date_selector_source = source[date_selector_start:date_selector_end]

    assert "allVisibleDateValues" in date_selector_source
    assert "sameDateOccurrences >= 2" in date_selector_source


def test_mva_cielo_reuses_a_complete_local_report_even_during_payment_refresh(monkeypatch):
    closing = {
        "relatorios_pagamento": {
            "cartao_credito": {"total_autorizado": 100.0, "itens_autorizados": [{"valor_bruto": 100.0}]},
            "cartao_credito_caixa": {"total_autorizado": 0.0, "itens_autorizados": []},
        }
    }
    cielo_report = {
        "cartao_credito_caixa": {
            "total_autorizado": 100.0,
            "itens_autorizados": [{"valor_bruto": 100.0}],
        }
    }

    monkeypatch.setattr(utils, "_find_local_cielo_card_report", lambda *_args, **_kwargs: {"cartoes": "local.csv", "avisos": []})
    monkeypatch.setattr(utils, "_build_card_reports_from_cielo", lambda *_args, **_kwargs: cielo_report)
    monkeypatch.setattr(utils, "_report_scope_windows", lambda _closing: [])
    monkeypatch.setattr(utils, "_filter_payment_report_to_scope", lambda report, _scope: report)
    monkeypatch.setattr(utils, "baixar_relatorio_cielo_mva", lambda *_args, **_kwargs: pytest.fail("A Cielo não deve reabrir quando o CSV local já cobre o fechamento."))

    result, warnings = utils._integrate_cielo_card_reports_if_needed(
        closing,
        "29/08/2026",
        auto_download_missing=True,
        force_refresh_payments=True,
        company="MVA",
    )

    assert warnings == []
    assert result["relatorios_pagamento"]["cartao_credito_caixa"]["total_autorizado"] == 100.0


def test_wait_for_cielo_downloaded_report_requires_detailed_when_requested(tmp_path):
    resumo = tmp_path / "Vendas_Cielo_historico_resumo-20260430-20260430-1-1-csv.csv"
    resumo.write_text(
        "\n".join(
            [
                "Consolidado de vendas Cielo",
                "Data da venda;Forma de pagamento;Quantidade de vendas;Valor bruto",
                "30/04/2026;Credito a vista;1;90,00",
            ]
        ),
        encoding="utf-8",
    )

    found = _wait_for_cielo_downloaded_report(str(tmp_path), "30/04/2026", time.time() - 5, timeout=0.1, require_detailed=True)

    assert found is None


def test_wait_for_cielo_downloaded_report_accepts_detailed_when_required(tmp_path):
    detalhado = tmp_path / "Vendas_cielo_historico_detalhe-20260430-20260430-1-1-csv.csv"
    detalhado.write_text(
        "\n".join(
            [
                "Detalhado de vendas Cielo",
                "Data da venda;Hora da venda;Forma de pagamento;Status da venda;Valor bruto;Código de autorização",
                "30/04/2026;10:20;Crédito à vista;Aprovada;90,00;123456",
            ]
        ),
        encoding="utf-8",
    )

    found = _wait_for_cielo_downloaded_report(str(tmp_path), "30/04/2026", time.time() - 5, timeout=0.1, require_detailed=True)

    assert found == str(detalhado)


def test_wait_for_cielo_downloaded_report_accepts_requested_rows_in_multi_day_range(tmp_path):
    detalhado = tmp_path / "Vendas_cielo_hoje_detalhe-20260618-20260619-1-1-csv.csv"
    detalhado.write_text(
        "\n".join(
            [
                "Detalhado de vendas Cielo",
                "Data da venda: 18/06/2026 a 19/06/2026",
                "Data da venda;Hora da venda;Forma de pagamento;Status da venda;Valor bruto;Codigo de autorizacao",
                "19/06/2026;14:20;Credito a vista;Aprovada;90,00;123456",
            ]
        ),
        encoding="utf-8",
    )

    found = _wait_for_cielo_downloaded_report(str(tmp_path), "19/06/2026", time.time() - 5, timeout=0.1, require_detailed=True)

    assert found == str(detalhado)


def test_find_local_cielo_card_report_accepts_requested_rows_in_multi_day_range(tmp_path, monkeypatch):
    detalhado = tmp_path / "cielo_cartoes_19062026_mva_auto.csv"
    detalhado.write_text(
        "\n".join(
            [
                "Detalhado de vendas Cielo",
                "Data da venda: 18/06/2026 a 19/06/2026",
                "Data da venda;Hora da venda;Forma de pagamento;Status da venda;Valor bruto;Codigo de autorizacao",
                "19/06/2026;14:20;Credito a vista;Aprovada;90,00;123456",
            ]
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(utils, "_candidate_local_report_dirs", lambda: [tmp_path])

    found = utils._find_local_cielo_card_report("19/06/2026", company="MVA")

    assert found["cartoes"]
    assert any("foi usado" in aviso for aviso in found["avisos"])


def _write_caixa_pix_xlsx_with_invalid_styles(path: Path) -> None:
    strings = [
        "Relatorio de Vendas Pix",
        "Data da venda",
        "Cod. de autorizacao",
        "Valor bruto",
        "Terminal",
        "Numero do estabelecimento",
        "Status",
        "23/05/2026 as 10:01",
        "ABC123",
        "10,50",
        "POS1",
        "91111977",
        "APROVADA",
    ]
    shared_items = "".join(f"<si><t>{value}</t></si>" for value in strings)
    sheet_rows = "\n".join(
        [
            '<row r="1"><c r="A1" t="s"><v>0</v></c></row>',
            (
                '<row r="2">'
                '<c r="A2" t="s"><v>1</v></c>'
                '<c r="B2" t="s"><v>2</v></c>'
                '<c r="C2" t="s"><v>3</v></c>'
                '<c r="D2" t="s"><v>4</v></c>'
                '<c r="E2" t="s"><v>5</v></c>'
                '<c r="F2" t="s"><v>6</v></c>'
                "</row>"
            ),
            (
                '<row r="3">'
                '<c r="A3" t="s"><v>7</v></c>'
                '<c r="B3" t="s"><v>8</v></c>'
                '<c r="C3" t="s"><v>9</v></c>'
                '<c r="D3" t="s"><v>10</v></c>'
                '<c r="E3" t="s"><v>11</v></c>'
                '<c r="F3" t="s"><v>12</v></c>'
                "</row>"
            ),
        ]
    )
    with zipfile.ZipFile(path, "w") as archive:
        archive.writestr(
            "[Content_Types].xml",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                '<Default Extension="xml" ContentType="application/xml"/>'
                '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
                '<Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>'
                '<Override PartName="/xl/sharedStrings.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sharedStrings+xml"/>'
                '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>'
                "</Types>"
            ),
        )
        archive.writestr(
            "_rels/.rels",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
                "</Relationships>"
            ),
        )
        archive.writestr(
            "xl/workbook.xml",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
                'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
                '<sheets><sheet name="Pix" sheetId="1" r:id="rId1"/></sheets>'
                "</workbook>"
            ),
        )
        archive.writestr(
            "xl/_rels/workbook.xml.rels",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
                '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/>'
                '<Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/sharedStrings" Target="sharedStrings.xml"/>'
                '<Relationship Id="rId3" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>'
                "</Relationships>"
            ),
        )
        archive.writestr(
            "xl/sharedStrings.xml",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                f'<sst xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" count="{len(strings)}" uniqueCount="{len(strings)}">'
                f"{shared_items}</sst>"
            ),
        )
        archive.writestr(
            "xl/worksheets/sheet1.xml",
            (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
                f"<sheetData>{sheet_rows}</sheetData></worksheet>"
            ),
        )
        archive.writestr("xl/styles.xml", "<styleSheet><broken></styleSheet>")


def test_wait_for_downloaded_report_accepts_pix_xlsx_with_invalid_styles(tmp_path):
    caminho = tmp_path / "Relatorio_de_Vendas_Pix_23-05-2026_1033.xlsx"
    _write_caixa_pix_xlsx_with_invalid_styles(caminho)

    found = utils._wait_for_downloaded_report(str(tmp_path), "23/05/2026", "pix", time.time() - 5, timeout=0.1)

    assert found is not None
    assert Path(found).suffix == ".csv"
    assert "23/05/2026 as 10:01" in Path(found).read_text(encoding="utf-8-sig")


def test_find_local_payment_reports_accepts_pix_xlsx_with_invalid_styles(tmp_path, monkeypatch):
    caminho = tmp_path / "Relatorio_de_Vendas_Pix_23-05-2026_eh_auto.xlsx"
    _write_caixa_pix_xlsx_with_invalid_styles(caminho)
    monkeypatch.setattr(utils, "_candidate_local_report_dirs", lambda: [tmp_path])

    found = _find_eh_local_payment_reports("23/05/2026", company="EH")

    assert found["pix"] == str(caminho)


def test_find_local_payment_reports_prefers_consolidated_company_card_xlsx(tmp_path, monkeypatch):
    pd = pytest.importorskip("pandas")
    data_br = "10/05/2026"
    rows = [
        {
            "Data da venda": "10/05/2026 08:04:31",
            "Cód. de autorização": "123456",
            "Produto": "Débito",
            "Valor bruto": "31.00",
            "Status": "Aprovada",
        }
    ]
    consolidated = tmp_path / "Historico_Simplificado_de_vendas_10-05-2026_mva_auto.xlsx"
    establishment = tmp_path / "Historico_Simplificado_de_vendas_10-05-2026_mva_auto_est91119212.xlsx"
    pd.DataFrame(rows).to_excel(consolidated, index=False)
    pd.DataFrame(rows).to_excel(establishment, index=False)

    now = time.time()
    # The per-establishment file may be newer, but the consolidated file covers all terminals.
    import os

    os.utime(consolidated, (now - 10, now - 10))
    os.utime(establishment, (now, now))
    monkeypatch.chdir(tmp_path)

    found = _find_eh_local_payment_reports(data_br, company="MVA")

    assert found["cartoes"] == str(consolidated)


def test_find_local_payment_reports_ignores_cielo_files(tmp_path, monkeypatch):
    cielo = tmp_path / "cielo_cartoes_05062026_mva_auto.csv"
    cielo.write_text(
        "\n".join(
            [
                "Detalhado de vendas Cielo",
                "Data da venda;Hora da venda;Forma de pagamento;Status da venda;Valor bruto;Codigo de autorizacao",
                "05/06/2026;10:20;Credito a vista;Aprovada;100,00;123456",
            ]
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(utils, "_candidate_local_report_dirs", lambda: [tmp_path])

    found = _find_eh_local_payment_reports("05/06/2026", company="MVA")

    assert found["pix"] is None
    assert found["cartoes"] is None
    assert found["avisos"] == []


def test_mva_cielo_gap_and_merge_card_machine_report():
    fechamento = {
        "relatorios_pagamento": {
            "cartao_credito": {"total_autorizado": 150.0},
            "cartao_credito_caixa": {"total_autorizado": 100.0},
            "cartao_debito": {"total_autorizado": 50.0},
            "cartao_debito_caixa": {"total_autorizado": 50.0},
        }
    }
    assert _mva_cielo_needed_card_keys(fechamento) == ["cartao_credito_caixa"]
    assert _mva_cielo_pending_card_count(fechamento) == 1

    merged = _merge_card_machine_report(
        {
            "categoria": "cartao_credito_caixa",
            "arquivo": "caixa.xlsx",
            "caminho": "caixa.xlsx",
            "itens_autorizados": [{"numero": "1", "data_venda": "05/05/2026 às 10:00", "valor_bruto": 100.0}],
        },
        {
            "categoria": "cartao_credito_caixa",
            "arquivo": "cielo.csv",
            "caminho": "cielo.csv",
            "itens_autorizados": [{"numero": "2", "data_venda": "05/05/2026 às 11:00", "valor_bruto": 50.0}],
        },
    )

    assert merged["total_autorizado"] == 150.0
    assert merged["quantidade_autorizados"] == 2
    assert merged["origem"] == "caixa_cielo_cartoes"


def test_mva_cielo_merge_only_closing_gap():
    relatorios = {
        "cartao_credito": {
            "total_autorizado": 150.0,
            "itens_autorizados": [
                {"valor_bruto": 100.0},
                {"valor_bruto": 50.0},
            ],
        },
        "cartao_credito_caixa": {
            "categoria": "cartao_credito_caixa",
            "arquivo": "caixa.xlsx",
            "caminho": "caixa.xlsx",
            "total_autorizado": 100.0,
            "itens_autorizados": [
                {"numero": "1", "data_venda": "05/05/2026 as 10:00", "valor_bruto": 100.0},
            ],
        },
    }
    cielo_reports = {
        "cartao_credito_caixa": {
            "categoria": "cartao_credito_caixa",
            "arquivo": "cielo.csv",
            "caminho": "cielo.csv",
            "itens_autorizados": [
                {"numero": "2", "data_venda": "05/05/2026 as 11:00", "valor_bruto": 50.0},
                {"numero": "3", "data_venda": "05/05/2026 as 12:00", "valor_bruto": 70.0},
            ],
        }
    }

    assert utils._merge_cielo_reports_into_payment_reports(relatorios, cielo_reports) is True

    merged = relatorios["cartao_credito_caixa"]
    assert merged["total_autorizado"] == 150.0
    assert merged["quantidade_autorizados"] == 2
    assert [item["valor_bruto"] for item in merged["itens_autorizados"]] == [100.0, 50.0]


def test_mva_cielo_pending_card_count_uses_unmatched_closing_items():
    fechamento = {
        "relatorios_pagamento": {
            "cartao_credito": {
                "total_autorizado": 180.0,
                "quantidade_autorizados": 3,
                "itens_autorizados": [
                    {"valor_bruto": 50.0},
                    {"valor_bruto": 60.0},
                    {"valor_bruto": 70.0},
                ],
            },
            "cartao_credito_caixa": {
                "total_autorizado": 50.0,
                "quantidade_autorizados": 1,
                "itens_autorizados": [{"valor_bruto": 50.0}],
            },
            "cartao_debito": {"total_autorizado": 0.0, "itens_autorizados": []},
            "cartao_debito_caixa": {"total_autorizado": 0.0, "itens_autorizados": []},
        }
    }

    assert _mva_cielo_pending_card_count(fechamento) == 2


def test_mva_cielo_same_day_threshold_triggers_download(tmp_path, monkeypatch):
    data_br = utils.datetime.now().strftime("%d/%m/%Y")
    calls = []
    fechamento = {
        "relatorios_pagamento": {
            "cartao_credito": {
                "total_autorizado": 1600.0,
                "itens_autorizados": [{"valor_bruto": float(valor)} for valor in range(1, 41)],
            },
            "cartao_credito_caixa": {
                "total_autorizado": 0.0,
                "itens_autorizados": [],
            },
        }
    }

    monkeypatch.setattr(utils, "_find_local_cielo_card_report", lambda data, company="MVA": {"cartoes": None, "avisos": []})
    monkeypatch.setattr(utils, "_new_cielo_debug_log_path", lambda data, company="MVA": tmp_path / "cielo.log")

    def fake_baixar(data, **kwargs):
        calls.append(data)
        return {"cartoes": None, "avisos": [], "debug_log": str(tmp_path / "download.log")}

    monkeypatch.setattr(utils, "baixar_relatorio_cielo_mva", fake_baixar)

    _result, avisos = utils._integrate_cielo_card_reports_if_needed(
        fechamento,
        data_br,
        auto_download_missing=True,
        company="MVA",
    )

    assert calls == [data_br]
    assert avisos == []


def test_mva_cielo_local_report_skips_download(tmp_path, monkeypatch):
    data_br = "09/05/2026"
    local_cielo = tmp_path / "cielo_cartoes_09052026_mva_auto.csv"
    local_cielo.write_text(
        "\n".join(
            [
                "Data da venda: 09/05/2026 a 09/05/2026",
                "Data da venda;Hora da venda;Produto;Status;Valor bruto;Codigo de autorizacao",
                "09/05/2026;10:15;Credito;Aprovada;100,00;ABC123",
            ]
        ),
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(utils, "_candidate_local_report_dirs", lambda: [tmp_path])

    def fail_download(*args, **kwargs):
        raise AssertionError("Cielo download should not run when a local valid report exists")

    monkeypatch.setattr(utils, "baixar_relatorio_cielo_mva", fail_download)
    fechamento = {
        "relatorios_pagamento": {
            "cartao_credito": {
                "total_autorizado": 100.0,
                "itens_autorizados": [{"valor_bruto": 100.0}],
            },
            "cartao_credito_caixa": {
                "total_autorizado": 0.0,
                "itens_autorizados": [],
            },
        }
    }

    result, avisos = utils._integrate_cielo_card_reports_if_needed(
        fechamento,
        data_br,
        auto_download_missing=True,
        company="MVA",
    )

    assert avisos == []
    assert result["relatorios_pagamento"]["cartao_credito_caixa"]["total_autorizado"] == 100.0
    assert _mva_cielo_needed_card_keys(result) == []


def test_mva_refresh_needs_detects_low_caixa_reports_after_cielo():
    fechamento = {
        "relatorios_pagamento": {
            "pix_fechamento": {"total_autorizado": 250.0},
            "pix_caixa": {"total_autorizado": 20.0},
            "cartao_credito": {"total_autorizado": 300.0},
            "cartao_credito_caixa": {"total_autorizado": 100.0},
            "cartao_debito": {"total_autorizado": 80.0},
            "cartao_debito_caixa": {"total_autorizado": 80.0},
        }
    }

    needs = _mva_caixa_reports_refresh_needs(fechamento)

    assert needs["need_cartoes"] is True
    assert needs["need_pix"] is True
    assert any("cartao_credito" in reason for reason in needs["reasons"])
    assert any("pix" in reason for reason in needs["reasons"])


def test_mva_refresh_retries_zero_pix_without_cielo(monkeypatch):
    calls = []
    fechamento = {
        "relatorios_pagamento": {
            "pix_fechamento": {"total_autorizado": 250.0},
            "pix_caixa": {"total_autorizado": 0.0},
            "cartao_credito": {"total_autorizado": 20.0},
            "cartao_credito_caixa": {"total_autorizado": 20.0},
            "cartao_debito": {"total_autorizado": 30.0},
            "cartao_debito_caixa": {"total_autorizado": 30.0},
        }
    }

    def fake_baixar(data_br, **kwargs):
        calls.append(
            {
                "data_br": data_br,
                "need_pix": kwargs.get("need_pix"),
                "need_cartoes": kwargs.get("need_cartoes"),
            }
        )
        return {"avisos": []}

    def fake_integrate(report, data_br, **kwargs):
        report = dict(report)
        relatorios = dict(report.get("relatorios_pagamento") or {})
        relatorios["pix_caixa"] = {"total_autorizado": 250.0}
        report["relatorios_pagamento"] = relatorios
        return report, relatorios["pix_caixa"], []

    monkeypatch.setattr(utils, "baixar_relatorios_caixa_eh_azulzinha", fake_baixar)
    monkeypatch.setattr(utils, "_integrate_local_payment_reports", fake_integrate)

    result, avisos, refreshed = _refresh_mva_caixa_reports_if_needed(
        fechamento,
        "08/05/2026",
        auto_download_missing=True,
        company="MVA",
    )

    assert refreshed is True
    assert avisos == []
    assert calls == [{"data_br": "08/05/2026", "need_pix": True, "need_cartoes": False}]
    assert result["relatorios_pagamento"]["pix_caixa"]["total_autorizado"] == 250.0


def test_mva_clipp_scope_is_applied_before_payment_refresh(monkeypatch):
    texto = """
    MVA COMERCIO
    FECHAMENTO DE CAIXA
    DOCUMENTOS GERADOS
    PERIODO ANALISADO, DE 06/05/2026 ATE 06/05/2026
    1 - Abertura : 06/05/2026 08:00:00 - Fechamento : 06/05/2026 13:00:00
    2 - Abertura : 06/05/2026 13:00:01 - Fechamento : 06/05/2026 18:00:00
    CARTAO DE DEBITO: 1100,00
    PAGAMENTO INSTANTANEO (PIX): 0,00
    000001 NFCE 09:00:00 CLIENTE A CARTAO DE DEBITO 1000,00
    000002 NFCE 14:00:00 CLIENTE B CARTAO DE DEBITO 100,00
    """
    download_calls = []

    def fake_find_reports(data_br, **kwargs):
        return {"pix": "pix.csv", "cartoes": "card.xlsx", "avisos": []}

    def fake_integrate(report, data_br, **kwargs):
        assert report["relatorios_pagamento"]["cartao_debito"]["total_autorizado"] == 100.0
        report = dict(report)
        relatorios = dict(report.get("relatorios_pagamento") or {})
        relatorios["cartao_debito_caixa"] = {"total_autorizado": 100.0}
        report["relatorios_pagamento"] = relatorios
        return report, None, []

    def fail_download(*args, **kwargs):
        download_calls.append((args, kwargs))
        raise AssertionError("payment download should not run after scoped totals match")

    monkeypatch.setattr(utils, "_read_pdf_text", lambda _path: texto)
    monkeypatch.setattr(utils, "_find_eh_local_payment_reports", fake_find_reports)
    monkeypatch.setattr(utils, "_integrate_local_payment_reports", fake_integrate)
    monkeypatch.setattr(utils, "_find_local_cielo_card_report", lambda *args, **kwargs: {"cartoes": None, "avisos": []})
    monkeypatch.setattr(utils, "baixar_relatorios_caixa_eh_azulzinha", fail_download)
    monkeypatch.setattr(utils, "baixar_relatorio_cielo_mva", fail_download)

    report = analisar_pdf_fechamento_caixa_mva_clipp(
        "fechamento.pdf",
        auto_download_missing=True,
        scope_mode="afternoon",
    )

    assert report["relatorios_pagamento"]["cartao_debito"]["total_autorizado"] == 100.0
    assert report["relatorios_pagamento"]["cartao_debito_caixa"]["total_autorizado"] == 100.0
    assert _mva_caixa_reports_refresh_needs(report)["need_cartoes"] is False
    assert describe_closing_scope(report)["has_afternoon_only"] is True
    assert download_calls == []


def test_mva_afternoon_scope_ignores_short_operational_opening_window():
    relatorio_caixa = {
        "caixa_modelo": "MVA",
        "periodo": "05/06/2026 - 05/06/2026",
        "itens_caixa": [
            {"pedido": "000001", "valor": 10.0, "ordem": "2026-06-05 08:00:00"},
            {"pedido": "000002", "valor": 20.0, "ordem": "2026-06-05 14:00:00"},
        ],
        "itens_excluidos": [],
    }
    fechamento = {
        "caixa_modelo": "MVA",
        "periodo": "05/06/2026 - 05/06/2026",
        "fechamento_janelas": [
            {"abertura": "05/06/2026 07:52:16", "fechamento": "05/06/2026 07:52:44"},
            {"abertura": "05/06/2026 07:53:18", "fechamento": "05/06/2026 13:26:12"},
            {"abertura": "05/06/2026 13:26:53", "fechamento": "05/06/2026 17:31:14"},
        ],
        "nfces": [
            {
                "numero": "000001",
                "data_venda": "05/06/2026 08:00:00",
                "valor": 10.0,
            },
            {
                "numero": "000002",
                "data_venda": "05/06/2026 14:00:00",
                "valor": 20.0,
            },
        ],
        "relatorios_pagamento": {
            "dinheiro": {
                "categoria": "dinheiro",
                "total_autorizado": 30.0,
                "quantidade_autorizados": 2,
                "itens_autorizados": [
                    {"numero": "000001", "data_venda": "05/06/2026 08:00:00", "valor_bruto": 10.0},
                    {"numero": "000002", "data_venda": "05/06/2026 14:00:00", "valor_bruto": 20.0},
                ],
            }
        },
    }

    relatorio_tarde, fechamento_tarde, _ = aplicar_escopo_relatorio_caixa(
        relatorio_caixa,
        fechamento,
        None,
        scope_mode="afternoon",
    )

    assert [item["pedido"] for item in relatorio_tarde["itens_caixa"]] == ["000002"]
    assert [item["numero"] for item in fechamento_tarde["nfces"]] == ["000002"]
    assert fechamento_tarde["relatorios_pagamento"]["dinheiro"]["total_autorizado"] == 20.0
    assert fechamento_tarde["fechamento_janelas"] == [
        {"abertura": "05/06/2026 13:26:53", "fechamento": "05/06/2026 17:31:14"}
    ]

    relatorio_manha, fechamento_manha, _ = aplicar_escopo_relatorio_caixa(
        relatorio_caixa,
        fechamento,
        None,
        scope_mode="morning",
    )

    assert [item["pedido"] for item in relatorio_manha["itens_caixa"]] == ["000001"]
    assert [item["numero"] for item in fechamento_manha["nfces"]] == ["000001"]
    assert fechamento_manha["relatorios_pagamento"]["dinheiro"]["total_autorizado"] == 10.0
    assert fechamento_manha["fechamento_janelas"] == [
        {"abertura": "05/06/2026 07:53:18", "fechamento": "05/06/2026 13:26:12"}
    ]


def test_morning_scope_does_not_reuse_afternoon_only_window():
    windows = [{"abertura": "05/06/2026 13:26:53", "fechamento": "05/06/2026 17:31:14"}]

    assert utils._scope_windows_for_mode(windows, "morning") == []
    assert utils._scope_windows_for_mode(windows, "afternoon") == windows


def test_mva_next_day_closing_filter_keeps_target_opening_date(monkeypatch):
    texto = """
    MVA COMERCIO
    FECHAMENTO DE CAIXA
    DOCUMENTOS GERADOS
    PERIODO ANALISADO, DE 14/05/2026 ATE 14/05/2026
    1 - Abertura : 13/05/2026 13:27:54 - Fechamento : 14/05/2026 08:00:30
    2 - Abertura : 14/05/2026 08:02:09 - Fechamento : 14/05/2026 13:26:29
    CARTAO DE DEBITO: 300,00
    PAGAMENTO INSTANTANEO (PIX): 0,00
    000001 NFCE 07:50:00 CLIENTE A CARTAO DE DEBITO 100,00
    000002 NFCE 09:00:00 CLIENTE B CARTAO DE DEBITO 200,00
    """
    monkeypatch.setattr(utils, "_read_pdf_text", lambda _path: texto)

    report = analisar_pdf_fechamento_caixa_mva_clipp(
        "fechamento.pdf",
        auto_download_missing=False,
        filter_opening_date_br="14/05/2026",
    )

    assert report["periodo"] == "14/05/2026 - 14/05/2026"
    assert report["quantidade_nfce"] == 1
    assert report["total_nfce"] == 200.0
    assert report["fechamento_janelas"] == [
        {"abertura": "14/05/2026 08:02:09", "fechamento": "14/05/2026 13:26:29"}
    ]
    assert report["relatorios_pagamento"]["cartao_debito"]["total_autorizado"] == 200.0


def test_eh_next_day_closing_filter_keeps_target_sales_and_afternoon_scope():
    fechamento = {
        "periodo": "13/05/2026 - 14/05/2026",
        "fechamento_janelas": [
            {"abertura": "13/05/2026 08:00:00", "fechamento": "13/05/2026 12:00:00"},
            {"abertura": "13/05/2026 18:00:00", "fechamento": "14/05/2026 08:00:00"},
            {"abertura": "14/05/2026 08:00:00", "fechamento": "14/05/2026 12:00:00"},
        ],
        "nfces": [
            {
                "numero": "000001",
                "data_venda": "13/05/2026",
                "valor": 10.0,
                "scope_abertura": "13/05/2026 08:00:00",
                "scope_fechamento": "13/05/2026 12:00:00",
            },
            {
                "numero": "000002",
                "data_venda": "13/05/2026",
                "valor": 20.0,
                "scope_abertura": "13/05/2026 18:00:00",
                "scope_fechamento": "14/05/2026 08:00:00",
            },
            {
                "numero": "000003",
                "data_venda": "14/05/2026",
                "valor": 30.0,
                "scope_abertura": "14/05/2026 08:00:00",
                "scope_fechamento": "14/05/2026 12:00:00",
            },
        ],
        "relatorios_pagamento": {
            "pix_fechamento": {
                "forma_pagamento": "PIX",
                "summary_label": "PIX",
                "itens_autorizados": [
                    {
                        "numero": "000001",
                        "data_venda": "13/05/2026",
                        "valor_bruto": 10.0,
                        "scope_abertura": "13/05/2026 08:00:00",
                        "scope_fechamento": "13/05/2026 12:00:00",
                    },
                    {
                        "numero": "000002",
                        "data_venda": "13/05/2026",
                        "valor_bruto": 20.0,
                        "scope_abertura": "13/05/2026 18:00:00",
                        "scope_fechamento": "14/05/2026 08:00:00",
                    },
                    {
                        "numero": "000003",
                        "data_venda": "14/05/2026",
                        "valor_bruto": 30.0,
                        "scope_abertura": "14/05/2026 08:00:00",
                        "scope_fechamento": "14/05/2026 12:00:00",
                    },
                ],
            }
        },
    }
    relatorio_caixa = {
        "caixa_modelo": "EH",
        "periodo": "13/05/2026 - 13/05/2026",
        "itens_caixa": [
            {"pedido": "000001", "valor": 10.0, "cliente": "BALCAO"},
            {"pedido": "000002", "valor": 20.0, "cliente": "BALCAO"},
            {"pedido": "000003", "valor": 30.0, "cliente": "BALCAO"},
        ],
        "itens_excluidos": [],
    }

    filtrado = _filter_zweb_fechamento_to_sales_date(fechamento, "13/05/2026")

    assert filtrado["periodo"] == "13/05/2026 - 13/05/2026"
    assert [item["numero"] for item in filtrado["nfces"]] == ["000001", "000002"]
    assert len(filtrado["fechamento_janelas"]) == 2
    assert describe_closing_scope(filtrado)["has_full_day"] is True
    assert filtrado["relatorios_pagamento"]["pix_fechamento"]["total_autorizado"] == 30.0

    relatorio_tarde, fechamento_tarde, _ = aplicar_escopo_relatorio_caixa(
        relatorio_caixa,
        filtrado,
        None,
        scope_mode="afternoon",
    )

    assert [item["pedido"] for item in relatorio_tarde["itens_caixa"]] == ["000002"]
    assert [item["numero"] for item in fechamento_tarde["nfces"]] == ["000002"]

    relatorio_manha, fechamento_manha, _ = aplicar_escopo_relatorio_caixa(
        relatorio_caixa,
        filtrado,
        None,
        scope_mode="morning",
    )

    assert [item["pedido"] for item in relatorio_manha["itens_caixa"]] == ["000001"]
    assert [item["numero"] for item in fechamento_manha["nfces"]] == ["000001"]

    somente_tarde = _filter_zweb_fechamento_to_sales_date(
        {**fechamento, "nfces": [fechamento["nfces"][1]], "relatorios_pagamento": {}},
        "13/05/2026",
    )
    assert describe_closing_scope(somente_tarde)["has_afternoon_only"] is True


def test_eh_same_day_closing_filter_drops_previous_day_overnight_values():
    fechamento = {
        "periodo": "14/05/2026 - 14/05/2026",
        "fechamento_janelas": [
            {"abertura": "13/05/2026 13:27:54", "fechamento": "14/05/2026 08:00:30"},
            {"abertura": "14/05/2026 08:02:09", "fechamento": "14/05/2026 13:26:29"},
        ],
        "nfces": [
            {
                "numero": "000001",
                "data_venda": "13/05/2026",
                "valor": 100.0,
                "scope_abertura": "13/05/2026 13:27:54",
                "scope_fechamento": "14/05/2026 08:00:30",
            },
            {
                "numero": "000002",
                "data_venda": "14/05/2026",
                "valor": 200.0,
                "scope_abertura": "14/05/2026 08:02:09",
                "scope_fechamento": "14/05/2026 13:26:29",
            },
        ],
        "relatorios_pagamento": {
            "pix_fechamento": {
                "forma_pagamento": "PIX",
                "summary_label": "PIX",
                "itens_autorizados": [
                    {
                        "numero": "000001",
                        "data_venda": "13/05/2026",
                        "valor_bruto": 100.0,
                        "scope_abertura": "13/05/2026 13:27:54",
                        "scope_fechamento": "14/05/2026 08:00:30",
                    },
                    {
                        "numero": "000002",
                        "data_venda": "14/05/2026",
                        "valor_bruto": 200.0,
                        "scope_abertura": "14/05/2026 08:02:09",
                        "scope_fechamento": "14/05/2026 13:26:29",
                    },
                ],
            }
        },
    }

    assert _zweb_fechamento_has_sales_outside_date(fechamento, "14/05/2026") is True

    filtrado = _filter_zweb_fechamento_to_sales_date(fechamento, "14/05/2026")

    assert [item["numero"] for item in filtrado["nfces"]] == ["000002"]
    assert filtrado["total_nfce"] == 200.0
    assert filtrado["relatorios_pagamento"]["pix_fechamento"]["total_autorizado"] == 200.0
    assert filtrado["fechamento_janelas"] == [
        {"abertura": "14/05/2026 08:02:09", "fechamento": "14/05/2026 13:26:29"}
    ]
    assert describe_closing_scope(filtrado)["has_morning_only"] is True


def test_eh_cancelled_fiscal_coupons_absent_from_orders_are_visible():
    relatorio = {
        "caixa_modelo": "EH",
        "periodo": "14/05/2026 - 14/05/2026",
        "pedidos_caixa": 2,
        "pedidos_excluidos": 0,
        "pedidos_excluidos_cancelados": 0,
        "total_documento": 150.0,
        "total_excluido": 0.0,
        "total_excluido_cancelados": 0.0,
        "total_caixa": 150.0,
        "itens_caixa": [
            {"pedido": "000103230", "cliente": "CLIENTE BALCÃO", "documento": "NFC-e", "valor": 50.0},
            {"pedido": "000103244", "cliente": "CLIENTE BALCÃO", "documento": "NFC-e", "valor": 100.0},
        ],
        "itens_excluidos": [],
    }
    fiscal_status_map = {
        "000103230": {"cancelada": True, "valor": 50.0},
        "000103231": {"cancelada": True, "valor": 12.5},
        "000103244": {"cancelada": False, "valor": 100.0},
    }

    filtrado = utils._aplicar_filtro_canceladas_pedidos_eh(relatorio, fiscal_status_map)

    assert filtrado["pedidos_caixa"] == 1
    assert filtrado["pedidos_excluidos"] == 2
    assert filtrado["pedidos_excluidos_cancelados"] == 2
    assert filtrado["total_caixa"] == 100.0
    assert filtrado["total_excluido"] == 62.5
    assert filtrado["total_excluido_cancelados"] == 62.5
    assert filtrado["total_documento"] == 162.5
    assert [item["pedido"] for item in filtrado["itens_caixa"]] == ["000103244"]
    assert {item["pedido"] for item in filtrado["itens_excluidos"]} == {"000103230", "000103231"}


def test_eh_scope_filter_recalculates_cancelled_coupon_totals():
    window = {"abertura": "14/05/2026 08:02:09", "fechamento": "14/05/2026 13:26:29"}
    relatorio_caixa = {
        "caixa_modelo": "EH",
        "periodo": "14/05/2026 - 14/05/2026",
        "itens_caixa": [
            {"pedido": "000103231", "cliente": "CLIENTE BALCÃO", "valor": 100.0},
        ],
        "itens_excluidos": [
            {
                "pedido": "000103230",
                "cliente": "CLIENTE BALCÃO",
                "documento": "NFC-e cancelada",
                "motivo": "Cupom cancelado",
                "valor": 50.0,
            },
            {
                "pedido": "000103260",
                "cliente": "CLIENTE BALCÃO",
                "documento": "NFC-e cancelada",
                "motivo": "Cupom cancelado",
                "valor": 10.0,
            },
        ],
    }
    relatorio_fechamento = {
        "nfces": [
            {"numero": "000103229", "scope_abertura": window["abertura"], "scope_fechamento": window["fechamento"]},
            {"numero": "000103231", "scope_abertura": window["abertura"], "scope_fechamento": window["fechamento"]},
        ],
    }

    filtrado = utils._filter_eh_caixa_report_to_scope(relatorio_caixa, relatorio_fechamento, [window])

    assert filtrado["pedidos_excluidos_cancelados"] == 1
    assert filtrado["total_excluido_cancelados"] == 50.0
    assert [item["pedido"] for item in filtrado["itens_excluidos"]] == ["000103230"]


def test_eh_conciliation_report_exists_when_everything_matches():
    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "caixa_modelo": "EH",
            "periodo": "19/06/2026 - 19/06/2026",
            "total_caixa": 300.0,
            "itens_caixa": [
                {"pedido": "000103230", "cliente": "CLIENTE BALCAO", "valor": 100.0},
                {"pedido": "000103231", "cliente": "CLIENTE BALCAO", "valor": 200.0},
            ],
            "itens_excluidos": [],
        },
        {
            "resumo_modelo": "EH",
            "periodo": "19/06/2026 - 19/06/2026",
            "total_nfce": 300.0,
            "nfces": [
                {"numero": "000103230", "numero_exibicao": "103230", "valor": 100.0},
                {"numero": "000103231", "numero_exibicao": "103231", "valor": 200.0},
            ],
            "relatorios_pagamento": {
                "pix_fechamento": {
                    "categoria": "pix_fechamento",
                    "total_autorizado": 100.0,
                    "itens_autorizados": [
                        {"numero": "000103230", "numero_exibicao": "103230", "valor_bruto": 100.0},
                    ],
                },
                "pix_caixa": {
                    "categoria": "pix_caixa",
                    "total_autorizado": 100.0,
                    "itens_autorizados": [
                        {"data_venda": "19/06/2026 14:00:00", "valor_bruto": 100.0},
                    ],
                },
                "cartao_credito": {
                    "categoria": "cartao_credito",
                    "total_autorizado": 200.0,
                    "itens_autorizados": [
                        {"numero": "000103231", "numero_exibicao": "103231", "valor_bruto": 200.0},
                    ],
                },
                "cartao_credito_caixa": {
                    "categoria": "cartao_credito_caixa",
                    "total_autorizado": 200.0,
                    "itens_autorizados": [
                        {"data_venda": "19/06/2026 14:05:00", "valor_bruto": 200.0},
                    ],
                },
            },
        },
    )

    alertas = fechamento["relatorios_pagamento"]["alertas_eh"]

    assert fechamento["status"] == "Confere"
    assert fechamento["alertas_count"] == 0
    assert alertas["hidden_in_menu"] is True
    assert alertas["correlacao_rows"] == [
        ("Dinheiro", "R$ 0,00", "-", "Interno"),
        ("PIX", "R$ 100,00", "R$ 100,00", "Finalizado"),
        ("Cartão Crédito", "R$ 200,00", "R$ 200,00", "Finalizado"),
    ]


def test_mva_clipp_cancelled_cash_coupons_are_visible(monkeypatch):
    status_map = {
        "000388060": {
            "numero": "000388060",
            "numero_exibicao": "388060",
            "valor": 5.70,
            "cancelada": True,
        },
        "000388072": {
            "numero": "000388072",
            "numero_exibicao": "388072",
            "valor": 63.90,
            "cancelada": True,
        },
        "000388166": {
            "numero": "000388166",
            "numero_exibicao": "388166",
            "valor": 1.30,
            "cancelada": True,
        },
    }
    monkeypatch.setattr(
        utils,
        "_load_minhas_notas_mva_context",
        lambda periodo: ([], status_map, None),
    )

    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "periodo": "07/05/2026 - 07/05/2026",
            "caixa_modelo": "MVA",
            "itens_caixa": [{"pedido": "000110220", "valor": 76.80}],
            "total_caixa": 0.0,
        },
        {
            "arquivo_tipo": "fechamento_caixa_clipp_mva",
            "periodo": "07/05/2026 - 07/05/2026",
            "total_nfce": 70.90,
            "nfces": [{"numero": numero} for numero in status_map],
            "relatorios_pagamento": {
                "dinheiro": {
                    "categoria": "dinheiro",
                    "total_autorizado": 70.90,
                    "itens_autorizados": [
                        {
                            "numero": numero,
                            "numero_exibicao": dados["numero_exibicao"],
                            "valor_bruto": dados["valor"],
                        }
                        for numero, dados in status_map.items()
                    ],
                }
            },
        },
    )

    alertas = fechamento["relatorios_pagamento"]["alertas_eh"]

    assert fechamento["cupons_cancelados_count"] == 3
    assert fechamento["cupons_cancelados_valor"] == 70.90
    assert fechamento["valor_faltantes"] == 0.0
    assert fechamento["alertas_count"] == 0
    assert fechamento["status"] == "Confere"
    assert alertas["quantidade_relatorio"] == 0
    assert alertas["total_relatorio"] == 0.0
    assert alertas["cancelados_rows"] == [
        ("CF 388060", "R$ 5,70"),
        ("CF 388072", "R$ 63,90"),
        ("CF 388166", "R$ 1,30"),
    ]


def test_mva_uses_clipp_cancelled_coupons_when_minhas_notas_returns_empty(monkeypatch):
    def minhas_notas_must_not_be_called(periodo):
        raise AssertionError("O fechamento da MVA deve usar o status do Clipp quando ele estiver disponível.")

    monkeypatch.setattr(utils, "_load_minhas_notas_mva_context", minhas_notas_must_not_be_called)

    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "periodo": "02/09/2026 - 02/09/2026",
            "caixa_modelo": "MVA",
            "itens_caixa": [{"pedido": "000110220", "valor": 76.80}],
            "total_caixa": 0.0,
        },
        {
            "arquivo_tipo": "fechamento_caixa_clipp_mva",
            "periodo": "02/09/2026 - 02/09/2026",
            "total_nfce": 250.0,
            "nfces": [{"numero": "000399974"}],
            "fiscal_status_map": {
                "000399973": {
                    "numero": "000399973",
                    "numero_exibicao": "399973",
                    "valor": 111.0,
                    "cancelada": True,
                    "status_codigo": 135,
                },
                "000399988": {
                    "numero": "000399988",
                    "numero_exibicao": "399988",
                    "valor": 19.75,
                    "cancelada": True,
                    "status_codigo": 135,
                },
            },
            "fiscal_status_source": "clipp_movements",
            "relatorios_pagamento": {},
        },
    )

    assert fechamento["cupons_cancelados_count"] == 2
    assert fechamento["cupons_cancelados_valor"] == 130.75
    assert fechamento["total_resumo_nfce"] == 250.0
    assert fechamento["subtitle"] == "Cupons cancelados identificados no Clipp: 2."
    assert fechamento["relatorios_pagamento"]["alertas_eh"]["cancelados_rows"] == [
        ("CF 399973", "R$ 111,00"),
        ("CF 399988", "R$ 19,75"),
    ]


def test_mva_keeps_azulzinha_payments_visible_without_clipp_payment_rows(monkeypatch):
    monkeypatch.setattr(utils, "_load_minhas_notas_mva_context", lambda periodo: ([], {}, None))

    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "periodo": "10/08/2026 - 10/08/2026",
            "caixa_modelo": "MVA",
            "itens_caixa": [],
            "total_caixa": 0.0,
        },
        {
            "arquivo_tipo": "fechamento_caixa_clipp_mva",
            "periodo": "10/08/2026 - 10/08/2026",
            "total_nfce": 0.0,
            "nfces": [],
            "relatorios_pagamento": {
                "pix_caixa": {
                    "categoria": "pix_caixa",
                    "total_autorizado": 867.30,
                    "itens_autorizados": [{"data_venda": "10/08/2026 às 08:07", "valor_bruto": 867.30}],
                },
                "cartao_credito_caixa": {
                    "categoria": "cartao_credito_caixa",
                    "total_autorizado": 597.50,
                    "itens_autorizados": [{"data_venda": "10/08/2026 às 08:08", "valor_bruto": 597.50}],
                },
                "cartao_debito_caixa": {
                    "categoria": "cartao_debito_caixa",
                    "total_autorizado": 959.15,
                    "itens_autorizados": [{"data_venda": "10/08/2026 às 08:05", "valor_bruto": 959.15}],
                },
            },
        },
    )

    alertas = fechamento["relatorios_pagamento"]["alertas_eh"]

    assert alertas["correlacao_rows"] == [
        ("Dinheiro", "R$ 0,00", "-", "Interno"),
        ("PIX", "R$ 0,00", "R$ 867,30", "Divergente"),
        ("Cartão Crédito", "R$ 0,00", "R$ 597,50", "Divergente"),
        ("Cartão Débito", "R$ 0,00", "R$ 959,15", "Divergente"),
    ]
    assert alertas["pix_maquina_rows"] == [("PIX", "10/08/2026 às 08:07", "R$ 867,30")]
    assert alertas["cartao_maquina_rows"] == [
        ("Cartão Crédito", "10/08/2026 às 08:08", "R$ 597,50"),
        ("Cartão Débito", "10/08/2026 às 08:05", "R$ 959,15"),
    ]


def test_mva_agent_limits_azulzinha_payments_to_the_closed_clipp_window():
    prepared = agente_relatorios._prepare_mva_closing_for_comparison(
        {
            "fechamento_janelas": [
                {"abertura": "10/08/2026 07:52:15", "fechamento": "10/08/2026 14:16:45"}
            ],
            "relatorios_pagamento": {},
        },
        {
            "pix_caixa": {
                "total_autorizado": 83.70,
                "quantidade_autorizados": 4,
                "itens_autorizados": [
                    {"data_venda": "10/08/2026 às 09:57", "valor_bruto": 13.50},
                    {"data_venda": "10/08/2026 às 13:03", "valor_bruto": 36.80},
                    {"data_venda": "10/08/2026 às 14:15", "valor_bruto": 9.90},
                    {"data_venda": "10/08/2026 às 14:30", "valor_bruto": 23.50},
                ],
            }
        },
    )

    pix = prepared["relatorios_pagamento"]["pix_caixa"]

    assert pix["quantidade_autorizados"] == 3
    assert pix["total_autorizado"] == 60.20
    assert [item["valor_bruto"] for item in pix["itens_autorizados"]] == [13.50, 36.80, 9.90]


def test_mva_agent_falls_back_to_cielo_for_an_uncovered_card_total(monkeypatch):
    closing = {
        "fechamento_janelas": [
            {"abertura": "29/08/2026 13:00:00", "fechamento": "29/08/2026 18:00:00"}
        ],
        "relatorios_pagamento": {
            "cartao_credito": {
                "total_autorizado": 100.0,
                "itens_autorizados": [{"valor_bruto": 100.0, "data_venda": "29/08/2026 às 14:00"}],
            },
        },
    }
    azulzinha = {
        "cartao_credito_caixa": {
            "total_autorizado": 20.0,
            "itens_autorizados": [{"valor_bruto": 20.0, "data_venda": "29/08/2026 às 14:00"}],
        },
    }

    def integrate_cielo(prepared, data_br, **options):
        assert data_br == "29/08/2026"
        assert options["auto_download_missing"] is True
        assert options["force_refresh_payments"] is True
        assert options["company"] == "MVA"
        prepared["relatorios_pagamento"]["cartao_credito_caixa"] = {
            "total_autorizado": 100.0,
            "itens_autorizados": [{"valor_bruto": 100.0, "data_venda": "29/08/2026 às 14:00"}],
        }
        return prepared, ["Relatório da Cielo foi usado para complementar o crédito."]

    monkeypatch.setattr(agente_relatorios, "_integrate_cielo_card_reports_if_needed", integrate_cielo)

    prepared, warnings = agente_relatorios._prepare_mva_payment_reports(date(2026, 8, 29), closing, azulzinha)

    assert prepared["relatorios_pagamento"]["cartao_credito_caixa"]["total_autorizado"] == 100.0
    assert warnings == ["Relatório da Cielo foi usado para complementar o crédito."]


def test_mva_agent_does_not_consult_cielo_outside_friday_or_saturday(monkeypatch):
    closing = {
        "relatorios_pagamento": {
            "cartao_debito": {"total_autorizado": 100.0},
            "cartao_debito_caixa": {"total_autorizado": 20.0},
        }
    }

    monkeypatch.setattr(
        agente_relatorios,
        "_integrate_cielo_card_reports_if_needed",
        lambda *_args, **_kwargs: pytest.fail("A Cielo não deve ser consultada fora de sexta e sábado."),
    )

    prepared, warnings = agente_relatorios._prepare_mva_payment_reports(
        date(2026, 8, 31),
        closing,
        {},
    )

    assert prepared["relatorios_pagamento"]["cartao_debito_caixa"]["total_autorizado"] == 20.0
    assert warnings == []
    agente_relatorios._validate_mva_card_payment_sources(prepared, date(2026, 8, 31))


def test_mva_agent_rejects_a_card_gap_that_cielo_did_not_cover():
    closing = {
        "relatorios_pagamento": {
            "cartao_debito": {"total_autorizado": 100.0},
            "cartao_debito_caixa": {"total_autorizado": 20.0},
        }
    }

    with pytest.raises(RuntimeError, match="Cielo não cobriu.*Cartão Débito"):
        agente_relatorios._validate_mva_card_payment_sources(closing, date(2026, 8, 29))


def test_mva_agent_scopes_clipp_data_to_the_requested_afternoon_window():
    dav = {
        "caixa_modelo": "MVA",
        "itens_caixa": [
            {"pedido": "000001", "ordem": "2026-08-10 09:57:00", "valor": 13.50},
            {"pedido": "000002", "ordem": "2026-08-10 15:20:00", "valor": 9.90},
        ],
        "itens_excluidos": [],
    }
    closing = {
        "fechamento_janelas": [
            {"id_movimento": 921, "abertura": "10/08/2026 07:52:15", "fechamento": "10/08/2026 14:16:45"},
            {"id_movimento": 922, "abertura": "10/08/2026 14:16:55", "fechamento": "10/08/2026 17:35:46"},
        ],
        "nfces": [
            {"numero": "000001", "data_venda": "10/08/2026 09:57:00", "valor": 13.50},
            {"numero": "000002", "data_venda": "10/08/2026 15:20:00", "valor": 9.90},
        ],
        "relatorios_pagamento": {
            "pix_fechamento": {
                "total_autorizado": 23.40,
                "quantidade_autorizados": 2,
                "itens_autorizados": [
                    {"numero": "000001", "data_venda": "10/08/2026 09:57:00", "valor_bruto": 13.50},
                    {"numero": "000002", "data_venda": "10/08/2026 15:20:00", "valor_bruto": 9.90},
                ],
            }
        },
    }

    scoped_dav, scoped_closing = agente_relatorios._scope_mva_reports(dav, closing, "afternoon")

    assert [item["pedido"] for item in scoped_dav["itens_caixa"]] == ["000002"]
    assert [item["numero"] for item in scoped_closing["nfces"]] == ["000002"]
    assert scoped_closing["relatorios_pagamento"]["pix_fechamento"]["total_autorizado"] == 9.90
    assert scoped_closing["fechamento_janelas"] == [
        {"id_movimento": 922, "abertura": "10/08/2026 14:16:55", "fechamento": "10/08/2026 17:35:46"}
    ]


def test_mva_agent_uses_explicit_shared_reports_directory():
    assert agente_relatorios._output_dir_from_environment(
        r"C:\Users\TI\Desktop\Relatorios"
    ) == Path(r"C:\Users\TI\Desktop\Relatorios")


def test_mva_agent_uses_shared_reports_directory_without_environment_override(monkeypatch):
    monkeypatch.setattr(
        agente_relatorios.Path,
        "home",
        classmethod(lambda cls: Path(r"C:\Users\relatorios.wol")),
    )

    assert agente_relatorios._output_dir_from_environment("") == Path(
        r"C:\Users\TI\Desktop\Relatorios"
    )


def test_print_document_page_style_reserves_a_safe_top_margin():
    from qt_vendas import _print_document_page_style

    assert "padding:8pt 0 0" in _print_document_page_style()


def test_agent_restores_project_root_on_import_path_after_staging_directory(monkeypatch, tmp_path):
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "path", [entry for entry in sys.path if entry != str(agente_relatorios.ROOT)])

    agente_relatorios._ensure_project_root_on_import_path()

    assert sys.path[0] == str(agente_relatorios.ROOT)


def test_agent_sends_both_valid_final_reports_to_the_printer_without_a_window(tmp_path):
    mva_pdf = tmp_path / "Relatorio_MVA.pdf"
    horizonte_pdf = tmp_path / "Relatorio_Horizonte.pdf"
    mva_pdf.write_bytes(b"%PDF-1.7\nMVA")
    horizonte_pdf.write_bytes(b"%PDF-1.7\nHorizonte")
    summary = {
        "mva": {"status": "ok", "arquivos": [str(mva_pdf)]},
        "eh": {"status": "ok", "arquivos": [str(horizonte_pdf)]},
    }
    printed_commands = []

    printer_summary = agente_relatorios._send_final_reports_to_printer(
        summary,
        printer_name="IMP-Valdirene",
        executable=tmp_path / "SumatraPDF.exe",
        command_runner=lambda command, **options: printed_commands.append((command, options)),
    )

    assert printer_summary == {
        "status": "enviado",
        "impressora": "IMP-Valdirene",
        "arquivos": [str(mva_pdf), str(horizonte_pdf)],
    }
    assert [command for command, _ in printed_commands] == [
        [str(tmp_path / "SumatraPDF.exe"), "-silent", "-print-to", "IMP-Valdirene", str(mva_pdf)],
        [str(tmp_path / "SumatraPDF.exe"), "-silent", "-print-to", "IMP-Valdirene", str(horizonte_pdf)],
    ]
    assert all(options["check"] is True for _, options in printed_commands)


def test_agent_does_not_print_when_only_one_final_report_is_valid(tmp_path):
    mva_pdf = tmp_path / "Relatorio_MVA.pdf"
    mva_pdf.write_bytes(b"%PDF-1.7\nMVA")
    summary = {
        "mva": {"status": "ok", "arquivos": [str(mva_pdf)]},
        "eh": {"status": "erro", "mensagem": "Falha na fonte"},
    }

    printer_summary = agente_relatorios._send_final_reports_to_printer(
        summary,
        executable=tmp_path / "SumatraPDF.exe",
        command_runner=lambda *args, **kwargs: pytest.fail("Não deveria haver envio para a impressora."),
    )

    assert printer_summary is None


def test_agent_cleanup_leaves_a_locked_staging_file_without_failing(tmp_path, monkeypatch):
    staging_dir = tmp_path / ".agente_tmp"
    staging_dir.mkdir()
    locked_file = staging_dir / "Historico_Simplificado_de_vendas_26-08-2026_eh_auto.xlsx"
    locked_file.write_bytes(b"arquivo temporario")
    original_unlink = Path.unlink

    def deny_locked_file_removal(path, *args, **kwargs):
        if path == locked_file:
            raise PermissionError("arquivo em uso")
        return original_unlink(path, *args, **kwargs)

    monkeypatch.setattr(agente_relatorios, "STAGING_DIR", staging_dir)
    monkeypatch.setattr(Path, "unlink", deny_locked_file_removal)

    blocked_files = agente_relatorios._cleanup_staging_dir()

    assert locked_file.is_file()
    assert blocked_files == [str(locked_file)]


def test_agent_lock_replaces_a_legacy_pid_lock_that_can_be_reused_by_another_process(tmp_path):
    lock_path = tmp_path / "agente_relatorios.lock"
    lock_path.write_text("4452", encoding="ascii")

    lock_token = agente_relatorios._acquire_agent_lock(lock_path)

    assert lock_token
    lock_payload = json.loads(lock_path.read_text(encoding="utf-8"))
    assert lock_payload["pid"] == os.getpid()
    assert lock_payload["token"] == lock_token


def test_agent_lock_keeps_a_lock_owned_by_the_same_running_process(tmp_path, monkeypatch):
    lock_path = tmp_path / "agente_relatorios.lock"
    lock_path.write_text(
        json.dumps({"pid": 9876, "process_marker": "creation-9876", "token": "active-token"}),
        encoding="utf-8",
    )
    monkeypatch.setattr(agente_relatorios, "_process_creation_marker", lambda pid: "creation-9876")

    assert agente_relatorios._acquire_agent_lock(lock_path) is None
    assert json.loads(lock_path.read_text(encoding="utf-8"))["token"] == "active-token"


def test_agent_lock_release_does_not_remove_a_newer_owners_lock(tmp_path):
    lock_path = tmp_path / "agente_relatorios.lock"
    lock_path.write_text(
        json.dumps({"pid": 9876, "process_marker": "creation-9876", "token": "newer-token"}),
        encoding="utf-8",
    )

    agente_relatorios._release_agent_lock(lock_path, "old-token")

    assert json.loads(lock_path.read_text(encoding="utf-8"))["token"] == "newer-token"


def test_mva_agent_defers_an_open_closing_without_downloading_external_reports(tmp_path, monkeypatch, capsys):
    class OpenClosingReader:
        def build_closing_report(self, target):
            return {
                "fechamento_parcial": True,
                "fechamento_janelas": [
                    {
                        "id_movimento": 1235,
                        "abertura": "10/08/2026 07:52:15",
                        "fechamento": None,
                    }
                ],
            }

        def build_dav_report(self, target):
            raise AssertionError("O DAV não deve ser consultado antes de o caixa fechar.")

    monkeypatch.setattr(agente_relatorios, "OUTPUT_DIR", tmp_path / "Relatorios")
    monkeypatch.setattr(agente_relatorios, "STAGING_DIR", tmp_path / "staging")
    monkeypatch.setattr(agente_relatorios, "RETRY_STATE_DIR", tmp_path / "retry_state")
    monkeypatch.setattr(
        agente_relatorios.ClippMvaReader,
        "from_environment",
        lambda: OpenClosingReader(),
    )
    monkeypatch.setattr(
        agente_relatorios,
        "_download_mva_azulzinha_reports",
        lambda target: pytest.fail("A Azulzinha não deve ser consultada antes do fechamento."),
    )

    assert agente_relatorios._run("morning", "10/08/2026") == 0

    status = json.loads(capsys.readouterr().out)
    assert status == {
        "status": "adiado",
        "escopo": "morning",
        "data_alvo": "10/08/2026",
        "proxima_verificacao_minutos": 15,
        "motivo": "O caixa MVA ainda está aberto.",
    }
    assert (tmp_path / "retry_state" / "2026-08-10_morning.json").is_file()


def test_agent_retry_recovers_a_missed_main_run_only_in_its_retry_window(tmp_path, monkeypatch):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    target = date(2026, 8, 12)

    monkeypatch.setattr(agente_relatorios, "RETRY_STATE_DIR", tmp_path / "retry_state")
    monkeypatch.setattr(agente_relatorios, "EXECUTION_STATE_DIR", tmp_path / "execution_state")

    assert agente_relatorios._retry_execution_mode(
        "afternoon",
        None,
        target,
        now=datetime(2026, 8, 13, 8, 15, tzinfo=sao_paulo),
    ) == "catch_up"

    agente_relatorios._record_execution_start(target, "afternoon", "main")

    assert agente_relatorios._retry_execution_mode(
        "afternoon",
        None,
        target,
        now=datetime(2026, 8, 13, 8, 15, tzinfo=sao_paulo),
    ) == "skip"
    assert agente_relatorios._retry_execution_mode(
        "afternoon",
        None,
        target,
        now=datetime(2026, 8, 13, 8, 0, tzinfo=sao_paulo),
    ) == "skip"


def test_agent_retry_prefers_a_pending_closing_over_missed_run_recovery(tmp_path, monkeypatch):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    target = date(2026, 8, 12)

    monkeypatch.setattr(agente_relatorios, "RETRY_STATE_DIR", tmp_path / "retry_state")
    monkeypatch.setattr(agente_relatorios, "EXECUTION_STATE_DIR", tmp_path / "execution_state")
    agente_relatorios._record_retry_request(target, "afternoon")

    assert agente_relatorios._retry_execution_mode(
        "afternoon",
        None,
        target,
        now=datetime(2026, 8, 13, 8, 15, tzinfo=sao_paulo),
    ) == "pending"


def test_agent_retry_never_recovers_a_weekend_target(tmp_path, monkeypatch):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    target = date(2026, 8, 16)

    monkeypatch.setattr(agente_relatorios, "RETRY_STATE_DIR", tmp_path / "retry_state")
    monkeypatch.setattr(agente_relatorios, "EXECUTION_STATE_DIR", tmp_path / "execution_state")

    assert agente_relatorios._retry_execution_mode(
        "afternoon",
        None,
        target,
        now=datetime(2026, 8, 18, 8, 15, tzinfo=sao_paulo),
    ) == "skip"


def test_agent_cleanup_removes_empty_staging_directory_after_deleting_artifacts(tmp_path, monkeypatch):
    staging = tmp_path / "staging"
    nested = staging / "downloads"
    nested.mkdir(parents=True)
    (staging / "temporary.csv").write_text("conteudo", encoding="utf-8")
    (nested / "temporary.html").write_text("conteudo", encoding="utf-8")
    monkeypatch.setattr(agente_relatorios, "STAGING_DIR", staging)
    monkeypatch.chdir(staging)

    agente_relatorios._cleanup_staging_dir()

    assert not staging.exists()


def test_agent_rejects_horizonte_closing_when_card_source_is_absent():
    fechamento_horizonte = {
        "relatorios_pagamento": {
            "cartao_credito": {"total_autorizado": 1049.25},
            "cartao_debito": {"total_autorizado": 421.45},
        }
    }

    with pytest.raises(RuntimeError, match="Cartão Crédito.*Cartão Débito"):
        agente_relatorios._validate_eh_card_payment_sources(fechamento_horizonte)


def test_mva_agent_identifies_a_closed_movement_as_ready_for_report_generation():
    assert agente_relatorios._mva_closing_is_ready(
        {
            "fechamento_parcial": False,
            "fechamento_janelas": [
                {
                    "id_movimento": 1235,
                    "abertura": "10/08/2026 07:52:15",
                    "fechamento": "10/08/2026 14:16:45",
                }
            ],
        }
    ) is True
    assert agente_relatorios._mva_closing_is_ready(
        {
            "fechamento_parcial": True,
            "fechamento_janelas": [
                {
                    "id_movimento": 1235,
                    "abertura": "10/08/2026 07:52:15",
                    "fechamento": None,
                }
            ],
        }
    ) is False


def _successful_report_summary(tmp_path):
    mva_pdf = tmp_path / "Relatorio_MVA_11-08-2026.pdf"
    horizonte_pdf = tmp_path / "Relatorio_Horizonte_11-08-2026.pdf"
    mva_pdf.write_bytes(b"%PDF-1.7\nMVA")
    horizonte_pdf.write_bytes(b"%PDF-1.7\nHorizonte")
    return {
        "mva": {"status": "ok", "arquivos": [str(mva_pdf)]},
        "eh": {"status": "ok", "arquivos": [str(horizonte_pdf)]},
    }


def test_agent_uses_a_distinct_final_pdf_name_for_each_closing_scope(tmp_path, monkeypatch):
    monkeypatch.setattr(agente_relatorios, "OUTPUT_DIR", tmp_path)
    target = date(2026, 8, 18)

    morning = agente_relatorios._final_pdf_path("MVA", target, "morning")
    afternoon = agente_relatorios._final_pdf_path("MVA", target, "afternoon")

    assert morning.name == "Relatorio_MVA_18-08-2026_Manha.pdf"
    assert afternoon.name == "Relatorio_MVA_18-08-2026_Tarde.pdf"
    assert morning != afternoon


def test_agent_only_eh_cli_runs_horizonte_without_starting_mva(monkeypatch):
    captured = {}

    def fake_run(scope, requested, **kwargs):
        captured.update({"scope": scope, "requested": requested, **kwargs})
        return 0

    monkeypatch.setattr(agente_relatorios, "_run", fake_run)
    monkeypatch.setattr(sys, "argv", ["agente_relatorios.py", "--scope", "morning", "--date", "05/09/2026", "--only-eh"])

    assert agente_relatorios.main() == 0
    assert captured == {
        "scope": "morning",
        "requested": "05/09/2026",
        "retry": False,
        "shutdown_after_wol": False,
        "only_mva": False,
        "only_eh": True,
    }


def test_wol_shutdown_is_armed_only_after_a_valid_report_cycle_started_by_wol(tmp_path):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    shutdown_calls = []

    shutdown = agente_relatorios._schedule_shutdown_for_wol_boot(
        "morning",
        None,
        _successful_report_summary(tmp_path),
        now=datetime(2026, 8, 11, 13, 46, tzinfo=sao_paulo),
        booted_at=datetime(2026, 8, 11, 13, 16, tzinfo=sao_paulo),
        command_runner=shutdown_calls.append,
    )

    assert shutdown == {
        "status": "agendado",
        "desligamento_em_segundos": 90,
        "wake_programado_para": "11/08/2026 13:15",
    }
    assert shutdown_calls == [[
        "shutdown.exe",
        "/s",
        "/t",
        "90",
        "/c",
        "Relatorios de fechamento concluidos pelo agente.",
    ]]


def test_wol_shutdown_does_not_turn_off_a_machine_that_was_already_on(tmp_path):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    shutdown_calls = []

    shutdown = agente_relatorios._schedule_shutdown_for_wol_boot(
        "afternoon",
        None,
        _successful_report_summary(tmp_path),
        now=datetime(2026, 8, 11, 8, 5, tzinfo=sao_paulo),
        booted_at=datetime(2026, 8, 11, 7, 30, tzinfo=sao_paulo),
        command_runner=shutdown_calls.append,
    )

    assert shutdown is None
    assert shutdown_calls == []


def test_wol_shutdown_requires_both_valid_final_pdfs(tmp_path):
    sao_paulo = ZoneInfo("America/Sao_Paulo")
    shutdown_calls = []
    summary = _successful_report_summary(tmp_path)
    Path(summary["eh"]["arquivos"][0]).write_bytes(b"arquivo sem cabecalho PDF")

    shutdown = agente_relatorios._schedule_shutdown_for_wol_boot(
        "morning",
        None,
        summary,
        now=datetime(2026, 8, 11, 13, 46, tzinfo=sao_paulo),
        booted_at=datetime(2026, 8, 11, 13, 16, tzinfo=sao_paulo),
        command_runner=shutdown_calls.append,
    )

    assert shutdown is None
    assert shutdown_calls == []


def test_eh_keeps_unmatched_card_payment_even_when_an_unrelated_nf_has_same_value():
    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "caixa_modelo": "EH",
            "periodo": "10/08/2026 - 10/08/2026",
            "itens_caixa": [],
            "itens_excluidos": [
                {
                    "pedido": "000022591",
                    "documento": "Nota Fiscal Eletronica",
                    "motivo": "NF-e",
                    "valor": 23.70,
                }
            ],
            "total_caixa": 0.0,
        },
        {
            "periodo": "10/08/2026 - 10/08/2026",
            "nfces": [],
            "relatorios_pagamento": {
                "dinheiro": {"total_autorizado": 0.0, "itens_autorizados": []},
                "cartao_debito": {"total_autorizado": 0.0, "itens_autorizados": []},
                "cartao_debito_caixa": {
                    "total_autorizado": 23.70,
                    "itens_autorizados": [
                        {
                            "numero": "003143",
                            "data_venda": "10/08/2026 às 09:10",
                            "valor_bruto": 23.70,
                        }
                    ],
                },
            },
        },
    )

    alertas = fechamento["relatorios_pagamento"]["alertas_eh"]

    assert ("Cartão Débito", "R$ 0,00", "R$ 23,70", "Divergente") in alertas["correlacao_rows"]
    assert alertas["cartao_maquina_rows"] == [("Débito: 10/08/2026 às 09:10", "R$ 23,70")]
    assert alertas["total_relatorio"] == 23.70


def test_eh_keeps_card_transaction_when_the_same_amount_was_paid_in_cash():
    fechamento = utils.comparar_caixa_resumo_nfce(
        {
            "caixa_modelo": "EH",
            "periodo": "29/08/2026 - 29/08/2026",
            "itens_caixa": [{"pedido": "000110220", "valor": 76.80}],
            "itens_excluidos": [],
            "total_caixa": 0.0,
        },
        {
            "periodo": "29/08/2026 - 29/08/2026",
            "nfces": [],
            "relatorios_pagamento": {
                "dinheiro": {
                    "total_autorizado": 76.80,
                    "itens_autorizados": [],
                },
                "cartao_credito": {
                    "total_autorizado": 76.80,
                    "itens_autorizados": [
                        {
                            "numero": "000110221",
                            "numero_exibicao": "110221",
                            "valor_bruto": 76.80,
                        }
                    ],
                },
                "cartao_credito_caixa": {
                    "total_autorizado": 76.80,
                    "itens_autorizados": [
                        {
                            "data_venda": "29/08/2026 às 10:30",
                            "valor_bruto": 76.80,
                        }
                    ],
                },
            },
        },
    )

    alertas = fechamento["relatorios_pagamento"]["alertas_eh"]

    assert alertas["cartao_maquina_rows"] == [("Crédito: 29/08/2026 às 10:30", "R$ 76,80")]
    assert alertas["total_relatorio"] == 153.60

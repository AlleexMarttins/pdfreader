"""Agente headless para gerar os fechamentos EH e MVA sem abrir o PDFReader."""

from __future__ import annotations

import argparse
import ctypes
import json
import os
import shutil
import subprocess
import sys
import uuid
from copy import deepcopy
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

import pandas as pd

from clipp_mva import ClippMvaReader
from utils import (
    _build_card_reports_from_caixa,
    _build_pix_report_from_caixa_csv,
    _filter_payment_report_to_scope,
    _integrate_cielo_card_reports_if_needed,
    _mva_cielo_needed_card_keys,
    aplicar_escopo_relatorio_caixa,
    baixar_relatorios_caixa_eh_azulzinha,
    comparar_caixa_resumo_nfce,
    gerar_relatorios_caixa_eh_zweb,
)


ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT_DIR = Path(r"C:\Users\TI\Desktop\Relatorios")


def _ensure_project_root_on_import_path() -> None:
    root_text = str(ROOT)
    if root_text in sys.path:
        sys.path.remove(root_text)
    sys.path.insert(0, root_text)


def _output_dir_from_environment(value: str | None = None) -> Path:
    configured = str(value if value is not None else os.environ.get("PDFREADER_REPORTS_DIR") or "").strip()
    return Path(configured).expanduser() if configured else DEFAULT_OUTPUT_DIR


OUTPUT_DIR = _output_dir_from_environment()
STAGING_DIR = OUTPUT_DIR / ".agente_tmp"
RETRY_STATE_DIR = ROOT / ".agent_retry_state"
EXECUTION_STATE_DIR = ROOT / ".agent_execution_state"
SAO_PAULO = ZoneInfo("America/Sao_Paulo")
WOL_SHUTDOWN_DELAY_SECONDS = 90
DEFAULT_REPORT_PRINTER = "IMP-Valdirene"
PDF_PRINT_TIMEOUT_SECONDS = 60


def _target_date(scope: str, requested: str | None) -> date:
    if requested:
        return datetime.strptime(requested, "%d/%m/%Y").date()
    today = date.today()
    return today - timedelta(days=1) if scope == "afternoon" else today


def _final_pdf_path(company: str, target: date, scope: str) -> Path:
    scope_label = "Manha" if scope == "morning" else "Tarde"
    return OUTPUT_DIR / f"Relatorio_{company}_{target:%d-%m-%Y}_{scope_label}.pdf"


def _scheduled_run_is_skipped(scope: str, requested: str | None) -> str | None:
    if requested:
        return None
    today = date.today()
    if today.weekday() == 6:
        return "Domingo não possui execução de relatórios."
    if scope == "afternoon" and (today - timedelta(days=1)).weekday() == 6:
        return "O fechamento de domingo não possui execução na segunda-feira."
    return None


def _write_json(path: Path, payload: object) -> None:
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2, default=str), encoding="utf-8")


def _process_creation_marker(process_id: int) -> str | None:
    """Returns the Windows creation timestamp that distinguishes a recycled PID."""
    if os.name != "nt" or process_id <= 0:
        return None

    process_handle = ctypes.windll.kernel32.OpenProcess(0x1000, False, process_id)
    if not process_handle:
        return None
    try:
        created = ctypes.wintypes.FILETIME()
        exited = ctypes.wintypes.FILETIME()
        kernel = ctypes.wintypes.FILETIME()
        user = ctypes.wintypes.FILETIME()
        if not ctypes.windll.kernel32.GetProcessTimes(
            process_handle,
            ctypes.byref(created),
            ctypes.byref(exited),
            ctypes.byref(kernel),
            ctypes.byref(user),
        ):
            return None
        return str((created.dwHighDateTime << 32) | created.dwLowDateTime)
    finally:
        ctypes.windll.kernel32.CloseHandle(process_handle)


def _read_agent_lock(lock_path: Path) -> dict[str, object] | None:
    try:
        lock_payload = json.loads(lock_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return lock_payload if isinstance(lock_payload, dict) else None


def _lock_belongs_to_running_agent(lock_path: Path) -> bool:
    lock_payload = _read_agent_lock(lock_path)
    if not lock_payload:
        return False
    process_id = lock_payload.get("pid")
    process_marker = lock_payload.get("process_marker")
    token = lock_payload.get("token")
    if not isinstance(process_id, int) or not isinstance(process_marker, str) or not isinstance(token, str):
        return False
    return _process_creation_marker(process_id) == process_marker


def _acquire_agent_lock(lock_path: Path) -> str | None:
    lock_token = uuid.uuid4().hex
    process_marker = _process_creation_marker(os.getpid())
    if process_marker is None:
        raise RuntimeError("Não foi possível identificar o processo atual para criar o bloqueio do agente.")
    lock_payload = json.dumps(
        {"pid": os.getpid(), "process_marker": process_marker, "token": lock_token},
        ensure_ascii=True,
    )
    while True:
        try:
            with lock_path.open("x", encoding="utf-8") as lock_handle:
                lock_handle.write(lock_payload)
            return lock_token
        except FileExistsError:
            if _lock_belongs_to_running_agent(lock_path):
                return None
            try:
                lock_path.unlink()
            except FileNotFoundError:
                continue


def _release_agent_lock(lock_path: Path, lock_token: str) -> None:
    lock_payload = _read_agent_lock(lock_path)
    if lock_payload and lock_payload.get("token") == lock_token:
        lock_path.unlink(missing_ok=True)


def _retry_state_path(target: date, scope: str) -> Path:
    return RETRY_STATE_DIR / f"{target:%Y-%m-%d}_{scope}.json"


def _mva_closing_is_ready(closing: dict) -> bool:
    windows = list(closing.get("fechamento_janelas") or [])
    return bool(windows) and not closing.get("fechamento_parcial") and all(
        isinstance(window, dict) and window.get("fechamento")
        for window in windows
    )


def _record_retry_request(target: date, scope: str) -> None:
    RETRY_STATE_DIR.mkdir(parents=True, exist_ok=True)
    _write_json(
        _retry_state_path(target, scope),
        {
            "escopo": scope,
            "data_alvo": target.strftime("%d/%m/%Y"),
            "proxima_verificacao_minutos": 15,
        },
    )


def _clear_retry_request(target: date, scope: str) -> None:
    _retry_state_path(target, scope).unlink(missing_ok=True)


def _execution_state_path(target: date, scope: str) -> Path:
    return EXECUTION_STATE_DIR / f"{target:%Y-%m-%d}_{scope}.json"


def _record_execution_start(target: date, scope: str, origin: str) -> None:
    EXECUTION_STATE_DIR.mkdir(parents=True, exist_ok=True)
    _write_json(
        _execution_state_path(target, scope),
        {
            "escopo": scope,
            "data_alvo": target.strftime("%d/%m/%Y"),
            "origem": origin,
            "iniciado_em": datetime.now(SAO_PAULO).isoformat(timespec="seconds"),
        },
    )


def _is_retry_window(scope: str, now: datetime) -> bool:
    local_now = now if now.tzinfo else now.replace(tzinfo=SAO_PAULO)
    local_now = local_now.astimezone(SAO_PAULO)
    minute_of_day = local_now.hour * 60 + local_now.minute
    if scope == "afternoon":
        return local_now.weekday() in (1, 2, 3, 4) and 8 * 60 + 15 <= minute_of_day <= 9 * 60 + 30
    return local_now.weekday() in (0, 1, 2, 3) and 13 * 60 + 45 <= minute_of_day <= 15 * 60 + 30


def _is_automatic_report_date(target: date) -> bool:
    return target.weekday() in (0, 1, 2, 3)


def _retry_execution_mode(scope: str, requested: str | None, target: date, *, now: datetime) -> str:
    if not requested and not _is_automatic_report_date(target):
        return "skip"
    if _retry_state_path(target, scope).is_file():
        return "pending"
    if requested or _execution_state_path(target, scope).is_file():
        return "skip"
    return "catch_up" if _is_retry_window(scope, now) else "skip"


def _cleanup_staging_dir() -> list[str]:
    blocked_files: list[str] = []
    if not STAGING_DIR.is_dir():
        return blocked_files
    for artifact in STAGING_DIR.iterdir():
        if artifact.is_file() or artifact.is_symlink():
            try:
                artifact.unlink(missing_ok=True)
            except OSError:
                blocked_files.append(str(artifact))
        elif artifact.is_dir():
            shutil.rmtree(artifact, ignore_errors=True)
    try:
        if Path.cwd().resolve() == STAGING_DIR.resolve():
            os.chdir(ROOT)
        STAGING_DIR.rmdir()
    except OSError:
        pass
    return blocked_files


def _scheduled_wol_time(scope: str, requested: str | None, now: datetime) -> datetime | None:
    if requested:
        return None
    local_now = now.astimezone(SAO_PAULO)
    weekday = local_now.weekday()
    if scope == "morning" and weekday in (0, 1, 2, 3):
        return local_now.replace(hour=13, minute=15, second=0, microsecond=0)
    if scope == "afternoon" and weekday in (1, 2, 3, 4):
        return local_now.replace(hour=7, minute=45, second=0, microsecond=0)
    return None


def _current_windows_boot_time() -> datetime | None:
    if os.name != "nt":
        return None
    uptime_milliseconds = ctypes.windll.kernel32.GetTickCount64()
    return datetime.now(timezone.utc) - timedelta(milliseconds=uptime_milliseconds)


def _has_valid_final_pdfs(summary: dict[str, object]) -> bool:
    for company in ("mva", "eh"):
        company_summary = summary.get(company)
        if not isinstance(company_summary, dict) or company_summary.get("status") != "ok":
            return False
        report_files = company_summary.get("arquivos")
        if not isinstance(report_files, list) or not report_files:
            return False
        for report_file in report_files:
            try:
                with Path(str(report_file)).open("rb") as pdf_file:
                    if pdf_file.read(5) != b"%PDF-":
                        return False
            except OSError:
                return False
    return True


def _find_pdf_print_executable() -> Path:
    configured_path = str(os.environ.get("PDFREADER_SUMATRA_PDF_PATH") or "").strip()
    candidates = [Path(configured_path).expanduser()] if configured_path else []
    for environment_name in ("ProgramFiles", "ProgramW6432", "LOCALAPPDATA"):
        base_path = str(os.environ.get(environment_name) or "").strip()
        if base_path:
            candidates.append(Path(base_path) / "SumatraPDF" / "SumatraPDF.exe")
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise RuntimeError(
        "SumatraPDF não foi localizado para a impressão silenciosa. "
        "Instale-o ou defina PDFREADER_SUMATRA_PDF_PATH."
    )


def _final_pdf_files(summary: dict[str, object]) -> list[Path]:
    if not _has_valid_final_pdfs(summary):
        return []
    pdf_files: list[Path] = []
    for company in ("mva", "eh"):
        company_summary = summary[company]
        assert isinstance(company_summary, dict)
        pdf_files.extend(Path(str(report_file)) for report_file in company_summary["arquivos"])
    return pdf_files


def _send_final_reports_to_printer(
    summary: dict[str, object],
    *,
    printer_name: str | None = None,
    executable: Path | None = None,
    command_runner=None,
) -> dict[str, object] | None:
    pdf_files = _final_pdf_files(summary)
    if not pdf_files:
        return None

    selected_printer = str(printer_name or os.environ.get("PDFREADER_REPORT_PRINTER") or DEFAULT_REPORT_PRINTER).strip()
    if not selected_printer:
        raise RuntimeError("A impressora dos relatórios não foi configurada.")
    print_executable = executable or _find_pdf_print_executable()
    if command_runner is None:
        command_runner = subprocess.run
    run_options: dict[str, object] = {"check": True, "timeout": PDF_PRINT_TIMEOUT_SECONDS}
    if os.name == "nt":
        run_options["creationflags"] = subprocess.CREATE_NO_WINDOW

    for pdf_file in pdf_files:
        command_runner(
            [str(print_executable), "-silent", "-print-to", selected_printer, str(pdf_file)],
            **run_options,
        )
    return {
        "status": "enviado",
        "impressora": selected_printer,
        "arquivos": [str(pdf_file) for pdf_file in pdf_files],
    }


def _schedule_shutdown_for_wol_boot(
    scope: str,
    requested: str | None,
    summary: dict[str, object],
    *,
    now: datetime | None = None,
    booted_at: datetime | None = None,
    command_runner=None,
) -> dict[str, object] | None:
    if not _has_valid_final_pdfs(summary):
        return None
    current_time = now or datetime.now(SAO_PAULO)
    scheduled_wol = _scheduled_wol_time(scope, requested, current_time)
    actual_boot = booted_at or _current_windows_boot_time()
    if scheduled_wol is None or actual_boot is None:
        return None
    local_boot = actual_boot.astimezone(SAO_PAULO)
    last_allowed_boot = scheduled_wol + timedelta(minutes=15)
    if not scheduled_wol <= local_boot <= last_allowed_boot or current_time < scheduled_wol:
        return None
    command = [
        "shutdown.exe",
        "/s",
        "/t",
        str(WOL_SHUTDOWN_DELAY_SECONDS),
        "/c",
        "Relatorios de fechamento concluidos pelo agente.",
    ]
    if command_runner is None:
        command_runner = lambda shutdown_command: subprocess.run(shutdown_command, check=True)
    command_runner(command)
    return {
        "status": "agendado",
        "desligamento_em_segundos": WOL_SHUTDOWN_DELAY_SECONDS,
        "wake_programado_para": scheduled_wol.strftime("%d/%m/%Y %H:%M"),
    }


def _write_final_pdf(path: Path, report: dict, closing: dict | None, payment: dict | None = None) -> None:
    _ensure_project_root_on_import_path()
    from PySide6 import QtGui, QtPrintSupport, QtWidgets
    from qt_vendas import CaixaReportDialog, _render_html_document_to_printer

    app = QtWidgets.QApplication.instance() or QtWidgets.QApplication([])
    dialog = CaixaReportDialog(None, report, closing, payment)
    try:
        jobs = dialog.build_automation_bundle_jobs()
        if not jobs:
            raise RuntimeError("O gerador visual não criou nenhum documento.")
        printer = QtPrintSupport.QPrinter(QtPrintSupport.QPrinter.HighResolution)
        printer.setOutputFormat(QtPrintSupport.QPrinter.PdfFormat)
        printer.setOutputFileName(str(path))
        printer.setPageSize(QtGui.QPageSize(QtGui.QPageSize.A4))
        _render_html_document_to_printer("<div></div>".join(html for _, html in jobs), printer, dialog.font().family() or "Lexend")
    finally:
        dialog.deleteLater()
        app.processEvents()


def _prepare_mva_closing_for_comparison(closing: dict, azulzinha: dict[str, dict] | None = None) -> dict:
    """Attach real Azulzinha reports to the MVA closing comparison."""
    prepared = deepcopy(closing)
    reports = prepared.setdefault("relatorios_pagamento", {})
    closed_windows = [
        window
        for window in (prepared.get("fechamento_janelas") or [])
        if isinstance(window, dict) and window.get("abertura") and window.get("fechamento")
    ]
    for source_key, external_key in ("pix", "pix_caixa"), ("cartao_credito", "cartao_credito_caixa"), ("cartao_debito", "cartao_debito_caixa"):
        if azulzinha and azulzinha.get(external_key):
            external_report = deepcopy(azulzinha[external_key])
            reports[external_key] = _filter_payment_report_to_scope(external_report, closed_windows)
    return prepared


def _scope_mva_reports(dav: dict, closing: dict, scope: str) -> tuple[dict, dict]:
    scoped_dav, scoped_closing, _ = aplicar_escopo_relatorio_caixa(
        dav,
        closing,
        None,
        scope_mode=scope,
    )
    movement_by_window = {
        (
            str(window.get("abertura") or "").strip(),
            str(window.get("fechamento") or "").strip(),
        ): window.get("id_movimento")
        for window in (closing.get("fechamento_janelas") or [])
        if isinstance(window, dict) and window.get("id_movimento") is not None
    }
    for window in scoped_closing.get("fechamento_janelas") or []:
        if not isinstance(window, dict):
            continue
        movement_id = movement_by_window.get(
            (
                str(window.get("abertura") or "").strip(),
                str(window.get("fechamento") or "").strip(),
            )
        )
        if movement_id is not None:
            window["id_movimento"] = movement_id
    return scoped_dav, scoped_closing


def _validate_eh_card_payment_sources(closing: dict) -> None:
    payment_reports = dict(closing.get("relatorios_pagamento") or {})
    missing_sources: list[str] = []

    for label, closing_key, source_key in (
        ("Cartão Crédito", "cartao_credito", "cartao_credito_caixa"),
        ("Cartão Débito", "cartao_debito", "cartao_debito_caixa"),
    ):
        closing_report = payment_reports.get(closing_key) or {}
        closing_total = float(closing_report.get("total_autorizado") or 0.0)
        if closing_total > 0.009 and not payment_reports.get(source_key):
            missing_sources.append(label)

    if missing_sources:
        missing_text = ", ".join(missing_sources)
        raise RuntimeError(
            "A Caixa/Azulzinha da Horizonte não retornou o relatório necessário para validar: "
            f"{missing_text}. O PDF não será publicado."
        )


def _download_mva_azulzinha_reports(target: date) -> dict[str, dict]:
    downloaded = baixar_relatorios_caixa_eh_azulzinha(
        target.strftime("%d/%m/%Y"),
        company="MVA",
        need_pix=True,
        need_cartoes=True,
    )
    reports: dict[str, dict] = {}
    pix_path = downloaded.get("pix")
    cards_path = downloaded.get("cartoes")
    if pix_path:
        reports["pix_caixa"] = _build_pix_report_from_caixa_csv(str(pix_path), target.strftime("%d/%m/%Y"))
    if cards_path:
        reports.update(_build_card_reports_from_caixa(str(cards_path), target.strftime("%d/%m/%Y")))
    if not reports:
        raise RuntimeError("A Azulzinha não retornou relatórios de PIX ou cartões para a MVA.")
    return reports


def _mva_uses_cielo_fallback(target: date) -> bool:
    """A Cielo complementa a MVA somente nos fechamentos de sexta e sábado."""
    return target.weekday() in (4, 5)


def _prepare_mva_payment_reports(target: date, closing: dict, azulzinha_reports: dict[str, dict]) -> tuple[dict, list[str]]:
    """Completa cartões da MVA pela Cielo somente nos dias em que ela é usada."""
    prepared = _prepare_mva_closing_for_comparison(closing, azulzinha_reports)
    if not _mva_uses_cielo_fallback(target):
        return prepared, []
    if not _mva_cielo_needed_card_keys(prepared):
        return prepared, []
    return _integrate_cielo_card_reports_if_needed(
        prepared,
        target.strftime("%d/%m/%Y"),
        auto_download_missing=True,
        force_refresh_payments=True,
        company="MVA",
    )


def _validate_mva_card_payment_sources(closing: dict, target: date) -> None:
    if not _mva_uses_cielo_fallback(target):
        return
    missing_keys = _mva_cielo_needed_card_keys(closing)
    if not missing_keys:
        return
    labels = {
        "cartao_credito_caixa": "Cartão Crédito",
        "cartao_debito_caixa": "Cartão Débito",
    }
    missing_text = ", ".join(labels[key] for key in missing_keys)
    raise RuntimeError(
        "A Cielo não cobriu integralmente os cartões da MVA: "
        f"{missing_text}. O PDF não será publicado."
    )


def _run_with_acquired_lock(
    scope: str,
    requested: str | None,
    target: date,
    retry_mode: str,
    shutdown_after_wol: bool,
    only_mva: bool,
    only_eh: bool,
) -> int:
    _record_execution_start(target, scope, retry_mode)
    summary: dict[str, object] = {
        "executado_em": datetime.now().isoformat(timespec="seconds"),
        "escopo": scope,
        "data_alvo": target.strftime("%d/%m/%Y"),
        "modo_execucao": retry_mode,
        "mva": {},
        "eh": {},
    }
    exit_code = 0

    if only_eh:
        summary["mva"] = {"status": "ignorado", "motivo": "Execução solicitada somente para a Horizonte."}
    else:
        try:
            reader = ClippMvaReader.from_environment()
            closing = reader.build_closing_report(target)
            if not _mva_closing_is_ready(closing):
                _record_retry_request(target, scope)
                print(
                    json.dumps(
                        {
                            "status": "adiado",
                            "escopo": scope,
                            "data_alvo": target.strftime("%d/%m/%Y"),
                            "proxima_verificacao_minutos": 15,
                            "motivo": "O caixa MVA ainda está aberto.",
                        },
                        ensure_ascii=False,
                    )
                )
                return 0

            _clear_retry_request(target, scope)
            STAGING_DIR.mkdir(parents=True, exist_ok=True)
            dav = reader.build_dav_report(target)
            dav, closing = _scope_mva_reports(dav, closing, scope)
            closing["fiscal_status_map"] = reader.build_cancelled_coupon_status_map(closing)
            closing["fiscal_status_source"] = "clipp_movements"
            azulzinha_reports = _download_mva_azulzinha_reports(target)
            closing_for_comparison, cielo_warnings = _prepare_mva_payment_reports(target, closing, azulzinha_reports)
            _validate_mva_card_payment_sources(closing_for_comparison, target)
            fechamento_final = comparar_caixa_resumo_nfce(
                dav,
                closing_for_comparison,
            )
            mva_pdf = _final_pdf_path("MVA", target, scope)
            _write_final_pdf(mva_pdf, dav, fechamento_final)
            summary["mva"] = {
                "status": "ok",
                "pedidos": dav.get("pedidos_total", 0),
                "nfce": closing.get("quantidade_nfce", 0),
                "total_vendas": closing.get("total_nfce", closing.get("total_geral", 0)),
                "arquivos": [str(mva_pdf)],
                "avisos": cielo_warnings,
            }
        except Exception as exc:
            summary["mva"] = {"status": "erro", "mensagem": str(exc)}
            exit_code = 1

    if only_mva:
        summary["eh"] = {"status": "ignorado", "motivo": "Execução solicitada somente para a MVA."}
    else:
        try:
            data_br = target.strftime("%d/%m/%Y")
            STAGING_DIR.mkdir(parents=True, exist_ok=True)
            os.chdir(STAGING_DIR)
            relatorio, fechamento, relatorio_pix = gerar_relatorios_caixa_eh_zweb(
                data_br,
                force_refresh_payments=True,
                fechamento_data_inicio_br=data_br,
                fechamento_data_fim_br=data_br,
                filtrar_fechamento_por_data_venda=True,
                scope_mode=scope,
            )
            eh_pdf = _final_pdf_path("Horizonte", target, scope)
            _validate_eh_card_payment_sources(fechamento)
            fechamento_final = comparar_caixa_resumo_nfce(relatorio, fechamento) if fechamento else None
            _write_final_pdf(eh_pdf, relatorio, fechamento_final, relatorio_pix)
            summary["eh"] = {"status": "ok", "arquivos": [str(eh_pdf)]}
        except Exception as exc:
            summary["eh"] = {"status": "erro", "mensagem": str(exc)}
            exit_code = 1

    try:
        print_job = _send_final_reports_to_printer(summary)
        if print_job:
            summary["impressao"] = print_job
    except Exception as exc:
        summary["impressao"] = {"status": "erro", "mensagem": str(exc)}
        exit_code = 1

    blocked_staging_files = _cleanup_staging_dir()
    os.chdir(ROOT)
    if blocked_staging_files:
        summary["limpeza"] = {"status": "pendente", "arquivos": blocked_staging_files}
    if shutdown_after_wol and exit_code == 0:
        try:
            shutdown = _schedule_shutdown_for_wol_boot(scope, requested, summary)
            if shutdown:
                summary["desligamento"] = shutdown
        except Exception as exc:
            summary["desligamento"] = {"status": "erro", "mensagem": str(exc)}
            exit_code = 1
    print(json.dumps(summary, ensure_ascii=False, indent=2, default=str))
    return exit_code


def _run(
    scope: str,
    requested: str | None,
    *,
    retry: bool = False,
    shutdown_after_wol: bool = False,
    only_mva: bool = False,
    only_eh: bool = False,
) -> int:
    if only_mva and only_eh:
        raise ValueError("Escolha somente uma empresa: MVA ou Horizonte.")
    skip_reason = _scheduled_run_is_skipped(scope, requested)
    if skip_reason:
        print(skip_reason)
        return 0
    if date.today().weekday() == 6 and not requested:
        print("Domingo: execução ignorada.")
        return 0
    target = _target_date(scope, requested)
    retry_mode = "main"
    if retry:
        retry_mode = _retry_execution_mode(scope, requested, target, now=datetime.now(SAO_PAULO))
    if retry and retry_mode == "skip":
        print(
            json.dumps(
                {
                    "status": "sem_tentativa_pendente",
                    "escopo": scope,
                    "data_alvo": target.strftime("%d/%m/%Y"),
                },
                ensure_ascii=False,
            )
        )
        return 0

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    lock_path = OUTPUT_DIR / "agente_relatorios.lock"
    lock_token = _acquire_agent_lock(lock_path)
    if lock_token is None:
        print("Outra execução do agente já está em andamento.")
        return 0
    try:
        return _run_with_acquired_lock(scope, requested, target, retry_mode, shutdown_after_wol, only_mva, only_eh)
    finally:
        _release_agent_lock(lock_path, lock_token)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=("morning", "afternoon"), required=True)
    parser.add_argument("--date", help="Data DD/MM/AAAA para teste ou reprocessamento")
    parser.add_argument("--retry", action="store_true", help="Executa somente uma nova tentativa previamente adiada")
    company_scope = parser.add_mutually_exclusive_group()
    company_scope.add_argument(
        "--only-mva",
        action="store_true",
        help="Gera somente a MVA; não consulta, publica ou imprime a Horizonte.",
    )
    company_scope.add_argument(
        "--only-eh",
        action="store_true",
        help="Gera somente a Horizonte; não consulta, publica ou imprime a MVA.",
    )
    parser.add_argument(
        "--shutdown-after-wol",
        action="store_true",
        help="Desliga somente após um ciclo válido iniciado pela janela Wake-on-LAN.",
    )
    args = parser.parse_args()
    return _run(
        args.scope,
        args.date,
        retry=args.retry,
        shutdown_after_wol=args.shutdown_after_wol,
        only_mva=args.only_mva,
        only_eh=args.only_eh,
    )


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import json
import os
import sys
import traceback
from datetime import date, datetime
from pathlib import Path

PROJECT_ROOT = Path(r"D:\pdfReader")
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

import agente_relatorios as agent
from utils import comparar_caixa_resumo_nfce, gerar_relatorios_caixa_eh_zweb


TARGET_DATE = date(2026, 9, 2)
SCOPE = "afternoon"
RESULT_PATH = Path(r"D:\pdfReader\tmp\horizonte_visible_result.json")


def record(stage: str, **details: object) -> None:
    payload = {
        "updated_at": datetime.now().isoformat(timespec="seconds"),
        "stage": stage,
        **details,
    }
    RESULT_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2, default=str), encoding="utf-8")
    print(json.dumps(payload, ensure_ascii=False, default=str), flush=True)


def main() -> int:
    os.environ["PDFREADER_SHOW_BROWSER"] = "1"
    os.environ["PDFREADER_KEEP_BROWSER_OPEN"] = "1"
    agent.STAGING_DIR.mkdir(parents=True, exist_ok=True)
    os.chdir(agent.STAGING_DIR)
    record("starting", target_date=TARGET_DATE.strftime("%d/%m/%Y"), scope=SCOPE)
    try:
        record("collecting_zweb_and_caixa")
        report, closing, pix_report = gerar_relatorios_caixa_eh_zweb(
            TARGET_DATE.strftime("%d/%m/%Y"),
            force_refresh_payments=True,
            fechamento_data_inicio_br=TARGET_DATE.strftime("%d/%m/%Y"),
            fechamento_data_fim_br=TARGET_DATE.strftime("%d/%m/%Y"),
            filtrar_fechamento_por_data_venda=True,
            scope_mode=SCOPE,
        )
        record(
            "validating_card_sources",
            payment_sources=sorted((closing.get("relatorios_pagamento") or {}).keys()),
        )
        agent._validate_eh_card_payment_sources(closing)
        record("building_reconciliation")
        reconciliation = comparar_caixa_resumo_nfce(report, closing) if closing else None
        pdf_path = agent._final_pdf_path("Horizonte", TARGET_DATE, SCOPE)
        record("rendering_pdf", output=str(pdf_path))
        agent._write_final_pdf(pdf_path, report, reconciliation, pix_report)
        record("completed", output=str(pdf_path))
        return 0
    except Exception as exc:
        record("failed", error_type=type(exc).__name__, error=str(exc), traceback=traceback.format_exc())
        return 1
    finally:
        os.chdir(agent.ROOT)


if __name__ == "__main__":
    raise SystemExit(main())

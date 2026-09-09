"""Leitura do Clipp da MVA para substituir os PDFs de DAV e fechamento."""

from __future__ import annotations

import os
from dataclasses import dataclass
from datetime import date, datetime, time
from typing import Any


_PAYMENT_LABELS = {
    "DINHEIRO": ("Dinheiro", "dinheiro"),
    "CARTAO DE CREDITO": ("Cartão de Crédito", "cartao_credito"),
    "CARTAO DE DEBITO": ("Cartão de Débito", "cartao_debito"),
    "PAGAMENTO INSTANTANEO (PIX)": ("Pagamento Instantâneo (PIX)", "pix_fechamento"),
}


class ClippMvaConnectionError(RuntimeError):
    pass


@dataclass(frozen=True)
class ClippMvaConnectionSettings:
    host: str
    database: str
    user: str
    password: str
    charset: str = "WIN1252"

    @classmethod
    def from_environment(cls) -> "ClippMvaConnectionSettings | None":
        password = os.getenv("PDFREADER_CLIPP_PASSWORD", "").strip()
        if not password:
            return None
        return cls(
            host=os.getenv("PDFREADER_CLIPP_HOST", "SRV-MVA").strip(),
            database=os.getenv(
                "PDFREADER_CLIPP_DATABASE",
                r"C:\Program Files (x86)\CompuFour\Clipp\BASE\CLIPP.FDB",
            ).strip(),
            user=os.getenv("PDFREADER_CLIPP_USER", "SYSDBA").strip(),
            password=password,
            charset=os.getenv("PDFREADER_CLIPP_CHARSET", "WIN1252").strip(),
        )


def database_is_configured() -> bool:
    return ClippMvaConnectionSettings.from_environment() is not None


def _normalize_payment_name(value: object) -> str:
    import unicodedata

    text = unicodedata.normalize("NFKD", str(value or ""))
    return " ".join(
        "".join(char for char in text if not unicodedata.combining(char)).upper().split()
    )


def _format_datetime_br(value: datetime | None) -> str:
    return value.strftime("%d/%m/%Y %H:%M:%S") if value else ""


def _fiscal_number(value: object) -> str:
    return str(value or "").strip().zfill(9)


def _missing_fiscal_numbers(numbers: list[str]) -> list[str]:
    sequence = sorted({int(number) for number in numbers if str(number).isdigit()})
    missing: list[str] = []
    for current, following in zip(sequence, sequence[1:]):
        missing.extend(str(number).zfill(9) for number in range(current + 1, following))
    return missing


class ClippMvaReader:
    def __init__(self, settings: ClippMvaConnectionSettings):
        self.settings = settings

    @classmethod
    def from_environment(cls) -> "ClippMvaReader":
        settings = ClippMvaConnectionSettings.from_environment()
        if not settings:
            raise ClippMvaConnectionError(
                "A senha do Clipp não está configurada. Defina PDFREADER_CLIPP_PASSWORD para habilitar a leitura direta."
            )
        return cls(settings)

    def _connect(self):
        try:
            import firebirdsql
        except ImportError as exc:
            raise ClippMvaConnectionError("O driver Firebird não está instalado.") from exc

        try:
            return firebirdsql.connect(
                host=self.settings.host,
                database=self.settings.database,
                user=self.settings.user,
                password=self.settings.password,
                charset=self.settings.charset,
            )
        except Exception as exc:
            raise ClippMvaConnectionError(f"Não foi possível conectar ao Clipp da MVA: {exc}") from exc

    def build_dav_report(self, sale_date: date) -> dict[str, Any]:
        with self._connect() as connection:
            cursor = connection.cursor()
            cursor.execute(
                """
                select id_pedido, dt_pedido, hr_pedido, cliente, vendedor, descricao, vlr_total
                from v_pedido_venda
                where dt_pedido = ?
                order by dt_pedido, hr_pedido, id_pedido
                """,
                (sale_date,),
            )
            rows = cursor.fetchall()

        records = []
        for order_id, order_date, order_time, customer, seller, status, total in rows:
            order_datetime = datetime.combine(order_date, order_time or time.min)
            records.append(
                {
                    "pedido": str(order_id),
                    "cliente": str(customer or "-").strip(),
                    "vendedor": str(seller or "-").strip(),
                    "documento": str(status or "-").strip(),
                    "valor": round(float(total or 0), 2),
                    "data_venda": _format_datetime_br(order_datetime),
                    "ordem": order_datetime.strftime("%Y-%m-%d %H:%M:%S"),
                    "origem_mva": "Clipp direto",
                }
            )

        finalized = [item for item in records if item["documento"] == "Finalizado"]
        excluded = [item for item in records if item["documento"] != "Finalizado"]
        return {
            "arquivo": "Clipp direto - DAV",
            "caixa_modelo": "MVA",
            "arquivo_tipo": "exportacao_dados_mva",
            "origem": "clipp_direto_mva",
            "periodo": f"{sale_date:%d/%m/%Y} - {sale_date:%d/%m/%Y}",
            "pedidos_total": len(records),
            "pedidos_balcao": 0,
            "pedidos_caixa": len(finalized),
            "pedidos_excluidos": len(excluded),
            "pedidos_excluidos_cliente": 0,
            "pedidos_excluidos_documento": 0,
            "pedidos_editando": sum(item["documento"] == "Editando" for item in excluded),
            "pedidos_outros_status": sum(item["documento"] not in {"Editando", "Finalizado"} for item in records),
            "total_documento": round(sum(item["valor"] for item in records), 2),
            "total_excluido": round(sum(item["valor"] for item in excluded), 2),
            "total_caixa": round(sum(item["valor"] for item in finalized), 2),
            "itens_caixa": finalized,
            "itens_excluidos": excluded,
        }

    def build_closing_report(self, opening_date: date) -> dict[str, Any]:
        with self._connect() as connection:
            cursor = connection.cursor()
            cursor.execute(
                """
                select id_pdv_mov, id_pdv, dt_hr_abertura, dt_hr_fechamento, vlr_abertura, vlr_sangria, vlr_suprimento
                from tb_pdv_mov
                where cast(dt_hr_abertura as date) = ?
                order by dt_hr_abertura, id_pdv_mov
                """,
                (opening_date,),
            )
            movements = cursor.fetchall()
            closed_movements = [movement for movement in movements if movement[3] is not None]
            if closed_movements:
                movements = closed_movements

            coupons: list[dict[str, Any]] = []
            payment_rows: list[tuple[Any, ...]] = []
            windows = []
            for movement_id, pdv_id, opened_at, closed_at, opening_amount, withdrawal, supply in movements:
                cursor.execute(
                    """
                    select n.id_nfvenda, n.nf_numero, n.dt_emissao, n.hr_saida, n.cliente, n.vlr_total
                    from tb_pdv_venda pv
                    join v_nfce n on n.id_nfvenda = pv.id_nfvenda
                    where pv.id_pdv_mov = ? and n.status = '100'
                    order by n.nf_numero
                    """,
                    (movement_id,),
                )
                movement_coupons = [
                    {
                        "id_nfvenda": sale_id,
                        "numero": _fiscal_number(number),
                        "numero_exibicao": str(number),
                        "data_venda": _format_datetime_br(datetime.combine(issue_date, issue_time or time.min)),
                        "cliente": str(customer or "-").strip(),
                        "valor": round(float(total or 0), 2),
                    }
                    for sale_id, number, issue_date, issue_time, customer, total in cursor.fetchall()
                ]
                if not movement_coupons:
                    continue
                coupons.extend(movement_coupons)
                windows.append(
                    {
                        "id_movimento": movement_id,
                        "caixa": pdv_id,
                        "abertura": _format_datetime_br(opened_at),
                        "fechamento": _format_datetime_br(closed_at),
                        "abertura_valor": round(float(opening_amount or 0), 2),
                        "sangria": round(float(withdrawal or 0), 2),
                        "suprimento": round(float(supply or 0), 2),
                    }
                )

            coupon_ids = [item["id_nfvenda"] for item in coupons]
            if coupon_ids:
                placeholders = ", ".join("?" for _ in coupon_ids)
                cursor.execute(
                    f"""
                    select id_nfvenda, desc_formapagamento, vlr_pagto
                    from v_nfvenda_pagamentos
                    where id_nfvenda in ({placeholders})
                    order by id_nfvenda, id_numpag
                    """,
                    tuple(coupon_ids),
                )
                payment_rows = cursor.fetchall()

        payments: dict[str, dict[str, Any]] = {}
        coupon_by_sale = {item["id_nfvenda"]: item for item in coupons}
        for sale_id, payment_name, amount in payment_rows:
            normalized = _normalize_payment_name(payment_name)
            display, key = _PAYMENT_LABELS.get(normalized, (str(payment_name).strip(), normalized.casefold()))
            coupon = coupon_by_sale.get(sale_id)
            if not coupon:
                continue
            bucket = payments.setdefault(
                key,
                {"forma_pagamento": display, "itens": []},
            )
            bucket["itens"].append(
                {
                    "numero": coupon["numero"],
                    "numero_exibicao": coupon["numero_exibicao"],
                    "data_venda": coupon["data_venda"],
                    "valor_bruto": round(float(amount or 0), 2),
                }
            )

        payment_reports = {}
        totalizers = {}
        for key, bucket in payments.items():
            items = bucket["itens"]
            total = round(sum(item["valor_bruto"] for item in items), 2)
            totalizers[bucket["forma_pagamento"]] = total
            payment_reports[key] = {
                "arquivo": "Clipp direto - Fechamento de Caixa",
                "periodo": f"{opening_date:%d/%m/%Y} - {opening_date:%d/%m/%Y}",
                "quantidade_autorizados": len(items),
                "total_autorizado": total,
                "itens_autorizados": items,
                "quantidade_relatorio": len(items),
                "total_relatorio": total,
                "consistente": True,
                "origem": "clipp_direto_mva",
                "categoria": key,
            }

        for coupon in coupons:
            coupon.pop("id_nfvenda", None)
        numbers = [item["numero"] for item in coupons]
        total_nfce = round(sum(item["valor"] for item in coupons), 2)
        has_open_movement = any(not window["fechamento"] for window in windows)
        return {
            "arquivo": "Clipp direto - Fechamento de Caixa",
            "arquivo_tipo": "fechamento_caixa_clipp_mva",
            "arquivo_resumo_titulo": "Clipp direto",
            "total_resumo_titulo": "Total Fechamento de caixa",
            "subtitle": "Dados lidos diretamente do Clipp, usando NFC-e autorizadas vinculadas aos movimentos do período.",
            "resumo_modelo": "MVA",
            "origem": "clipp_direto_mva",
            "periodo": f"{opening_date:%d/%m/%Y} - {opening_date:%d/%m/%Y}",
            "quantidade_nfce": len(coupons),
            "total_nfce": total_nfce,
            "total_geral": total_nfce,
            "totalizadores": totalizers,
            "relatorios_pagamento": payment_reports,
            "fechamento_janelas": windows,
            "fechamento_parcial": has_open_movement,
            "nfces": coupons,
            "nfces_faltantes_sequencia": _missing_fiscal_numbers(numbers),
            "fiscal_status_map": {},
        }

    def build_cancelled_coupon_status_map(self, closing_report: dict[str, Any]) -> dict[str, dict[str, Any]]:
        movement_ids = sorted(
            {
                int(window["id_movimento"])
                for window in closing_report.get("fechamento_janelas", [])
                if isinstance(window, dict) and str(window.get("id_movimento") or "").isdigit()
            }
        )
        if not movement_ids:
            return {}

        placeholders = ", ".join("?" for _ in movement_ids)
        with self._connect() as connection:
            cursor = connection.cursor()
            cursor.execute(
                f"""
                select n.nf_numero, n.dt_emissao, n.hr_saida, n.vlr_total, n.status
                from tb_pdv_venda pv
                join v_nfce n on n.id_nfvenda = pv.id_nfvenda
                where pv.id_pdv_mov in ({placeholders})
                  and n.status = '135'
                order by n.nf_numero
                """,
                tuple(movement_ids),
            )
            rows = cursor.fetchall()

        return {
            _fiscal_number(number): {
                "numero": _fiscal_number(number),
                "numero_exibicao": str(number),
                "valor": round(float(total or 0), 2),
                "cancelada": True,
                "status_codigo": int(status or 135),
                "emissao": _format_datetime_br(datetime.combine(issue_date, issue_time or time.min)),
                "origem": "clipp_direto_mva",
            }
            for number, issue_date, issue_time, total, status in rows
        }

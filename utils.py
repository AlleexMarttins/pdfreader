import os
import sys
import re
import json
import time
import html
import csv
import socket
import shutil
import tempfile
import zipfile
import asyncio
import base64
import threading
import subprocess
import queue
import difflib
import unicodedata
from urllib.parse import urljoin
from datetime import datetime, timedelta
from pathlib import Path
from typing import Iterable

import requests

try:
    from ftfy import fix_text as _ftfy_fix_text
except Exception:
    _ftfy_fix_text = None

from ui_dialogs import filedialog, messagebox
from global_vars import (
    listFiles, list_results, regex_data, regex_negative, 
    APP_VERSION, GITHUB_REPO, LAST_EH, LAST_MVA , LAST_HASH_MERGE,
    SALES_PERIOD, MINHAS_NOTAS_LOGIN, MINHAS_NOTAS_PASSWORD,
    ZWEB_USERNAME, ZWEB_PASSWORD, ZWEB_BASE_URL,
    GMAIL_OAUTH_CLIENT_ID, GMAIL_OAUTH_CLIENT_SECRET,
) 

# Configuração de logging mais leve (somente avisos e erros)
progress_queue = queue.Queue()
cancel_event = threading.Event()
LAST_STATE_SPREADSHEET = {}
_MINHAS_NOTAS_CACHE = {}

# Correções confirmadas no fechamento, quando a maquininha registrou cartão mas o CF foi pago em dinheiro.
_EH_CARD_MACHINE_CASH_COUPONS = {("29/08/2026", "110220")}

_UI_REFS = {
    "btn_cancel": None,
    "progress_var": None,
    "progress_bar": None,
    "progress_var_online": None,
    "progress_bar_online": None,
    "btn_tag": None,
    "btn_add_mais": None,
    "btn_merge_spreadsheet": None,
    "btn_select_pdf": None,
}

REGEX_VENDOR_HEADER = re.compile(r"^\s*Vendedor(?:\(a\))?:\s*(.+?)\s*$", re.IGNORECASE)
REGEX_NEW_SALE_LINE = re.compile(r"^\s*(?:NFC|NF)-e\s+\d+\s+\d{2}/\d{2}/\d{4}\b", re.IGNORECASE)
REGEX_NEW_TOTALS_LINE = re.compile(r"^\s*Totais\s+R\$\s+([-\d\.,]+)\s+[-\d\.,]+\s*$", re.IGNORECASE)
REGEX_NEW_SALE_AMOUNT = re.compile(r"^\s*(?:NFC|NF)-e\s+\d+\s+\d{2}/\d{2}/\d{4}\b.*?\s+([-\d\.,]+)\s+[-\d\.,]+\s*$", re.IGNORECASE)
REGEX_ANY_DATE = re.compile(r"\b(\d{2}/\d{2}/\d{4})\b")
REGEX_D_MARKER = re.compile(r"\(\s*d\s*\)", re.IGNORECASE)

_MOJIBAKE_MARKERS = ("\u00c3", "\u00c2", "\u00e2", "\ud83d")
_TEXT_FALLBACK_REPLACEMENTS = {
    "Relat?rio": "Relatório",
    "relat?rio": "relatório",
    "N?o": "Não",
    "n?o": "não",
    "m?quina": "máquina",
    "M?quina": "Máquina",
    "Per?odo": "Período",
    "Pend?ncias": "Pendências",
    "Transa??o": "Transação",
    "Transa??es": "Transações",
    "transa??o": "transação",
    "transa??es": "transações",
    "Cart?o": "Cartão",
    "cart?o": "cartão",
    "Cr?dito": "Crédito",
    "cr?dito": "crédito",
    "D?bito": "Débito",
    "d?bito": "débito",
    "Eletr?nica": "Eletrônica",
    "eletr?nica": "eletrônica",
    "Impress?o": "Impressão",
    "impress?o": "impressão",
    "Confirma??o": "Confirmação",
    "conclu?da": "concluída",
    "selec??o": "seleção",
}


def corrigir_texto(texto: str) -> str:
    """Corrige mojibake comum em textos PT-BR usando ftfy e fallback manual."""
    if not texto or not isinstance(texto, str):
        return texto

    corrigido = texto
    if _ftfy_fix_text is not None:
        try:
            corrigido = _ftfy_fix_text(corrigido)
        except Exception:
            pass

    if any(marker in corrigido for marker in _MOJIBAKE_MARKERS):
        for _ in range(2):
            try:
                candidato = corrigido.encode("latin1").decode("utf-8")
            except (UnicodeEncodeError, UnicodeDecodeError):
                break
            if candidato == corrigido:
                break
            corrigido = candidato
            if _ftfy_fix_text is not None:
                try:
                    corrigido = _ftfy_fix_text(corrigido)
                except Exception:
                    pass

    for origem, destino in _TEXT_FALLBACK_REPLACEMENTS.items():
        corrigido = corrigido.replace(origem, destino)

    return corrigido


def corrigir_estrutura_texto(valor):
    if isinstance(valor, str):
        return corrigir_texto(valor)
    if isinstance(valor, list):
        return [corrigir_estrutura_texto(item) for item in valor]
    if isinstance(valor, tuple):
        return tuple(corrigir_estrutura_texto(item) for item in valor)
    if isinstance(valor, dict):
        return {
            corrigir_estrutura_texto(chave) if isinstance(chave, str) else chave: corrigir_estrutura_texto(item)
            for chave, item in valor.items()
        }
    return valor


# Compatibilidade com chamadas legadas.
globals()["corrigirCodificação"] = corrigir_texto
globals()["corrigirCodifica\u00c3\u00a7\u00c3\u00a3o"] = corrigir_texto


def _empty_caixa_report(caminho_pdf: str, pdf_info: dict | None = None) -> dict:
    return {
        "arquivo": os.path.basename(caminho_pdf),
        "caixa_modelo": "",
        "arquivo_tipo": "pdf_sem_texto" if (pdf_info or {}).get("pdf_sem_texto") else "",
        "periodo": None,
        "pedidos_total": 0,
        "pedidos_balcao": 0,
        "pedidos_caixa": 0,
        "pedidos_excluidos": 0,
        "pedidos_excluidos_cliente": 0,
        "pedidos_excluidos_documento": 0,
        "pedidos_excluidos_cancelados": 0,
        "pedidos_editando": 0,
        "pedidos_outros_status": 0,
        "total_documento": 0.0,
        "total_excluido": 0.0,
        "total_excluido_cancelados": 0.0,
        "total_caixa": 0.0,
        "itens_caixa": [],
        "itens_excluidos": [],
        **(pdf_info or {}),
    }


def _empty_resumo_nfce_report(caminho_pdf: str, pdf_info: dict | None = None) -> dict:
    return {
        "arquivo": os.path.basename(caminho_pdf),
        "resumo_modelo": "",
        "periodo": None,
        "quantidade_nfce": 0,
        "total_nfce": 0.0,
        "nfces": [],
        "nfces_faltantes_sequencia": [],
        **(pdf_info or {}),
    }


def set_ui_refs(**kwargs):
    _UI_REFS.update({k: v for k, v in kwargs.items() if k in _UI_REFS})

def set_btn_cancel(state="disabled"):
    btn_cancel = _UI_REFS.get("btn_cancel")
    if btn_cancel:
        btn_cancel.configure(state=state)


def _extract_vendor_name(line: str) -> str | None:
    match = REGEX_VENDOR_HEADER.match(line or "")
    if not match:
        return None
    return match.group(1).strip()


def _is_sale_entry_line(line: str) -> bool:
    if not line:
        return False
    return bool(regex_data.match(line) or REGEX_NEW_SALE_LINE.match(line))


def _extract_total_vendas(line: str) -> str | None:
    if not line:
        return None

    match = re.search(r"Totais:\s*([-\d\.,]+)", line)
    if match:
        return match.group(1)

    match = REGEX_NEW_TOTALS_LINE.match(line)
    if match:
        return match.group(1)

    return None


def _extract_sale_date(line: str) -> str | None:
    if not line:
        return None

    if REGEX_NEW_SALE_LINE.match(line):
        match = REGEX_ANY_DATE.search(line)
        if match:
            return match.group(1)

    match = regex_data.match(line)
    if not match:
        return None

    lowered = line.lower()
    if " ate " in lowered or " até " in lowered:
        return None

    return match.group().strip()


def _line_has_d_marker(line: str) -> bool:
    return bool(REGEX_D_MARKER.search(line or ""))


def _extract_sale_amount(line: str) -> float | None:
    match = REGEX_NEW_SALE_AMOUNT.match(line or "")
    if not match:
        return None
    try:
        return parse_number(match.group(1))
    except Exception:
        return None

def process_cancel(): 
    cancel_event.set()
    while not progress_queue.empty():
        try:
            progress_queue.get_nowait()
        except queue.Empty:
            break
    set_btn_cancel()
    # 🔹 Reseta barra
    progress_var = _UI_REFS.get("progress_var")
    progress_bar = _UI_REFS.get("progress_bar")
    progress_var_online = _UI_REFS.get("progress_var_online")
    progress_bar_online = _UI_REFS.get("progress_bar_online")
    if progress_var:
        progress_var.set(0)
    if progress_bar:
        progress_bar.stop()
        progress_bar.config(mode="determinate")
    if progress_var_online:
        progress_var_online.set(0)
    if progress_bar_online:
        progress_bar_online.stop()
        progress_bar_online.config(mode="determinate")


def _scroll_tree_to_top(tree) -> None:
    scroll = getattr(tree, "scroll_to_top", None)
    if callable(scroll):
        scroll()


def _has_visible_data(dados: dict) -> bool:
    atendidos = int(dados.get("atendidos", 0) or 0)
    devolucoes = int(dados.get("devolucoes", 0) or 0)
    total_clientes = int(dados.get("total_clientes", 0) or 0)

    try:
        total_vendas = parse_number(dados.get("total_vendas", 0))
    except Exception:
        total_vendas = 0.0

    return any((atendidos, devolucoes, total_clientes)) or abs(total_vendas) > 0


def _total_vendas_value(dados: dict) -> float:
    try:
        return parse_number(dados.get("total_vendas", 0))
    except Exception:
        return 0.0


def _sorted_rows_by_total_vendas(data: dict) -> list[tuple[str, dict]]:
    return sorted(
        data.items(),
        key=lambda item: (-_total_vendas_value(item[1]), item[0].casefold())
    )

def _poll_queue(root, tree, progress_var, progress_bar, label_files_var=None, path_var=None):
    """Consome eventos da fila em intervalos e atualiza a UI sem travar."""
    
    try:
        kind, payload = progress_queue.get_nowait()
    except queue.Empty:
        # Agenda a próxima checagem em 50ms (menos carga na CPU/UI)
        root.after(50, lambda: _poll_queue(root, tree, progress_var, progress_bar, label_files_var, path_var))
        return

    if kind == "progress":
        progress_var.set(payload)
        progress_bar.update_idletasks()

    elif kind == "done":
        set_btn_cancel()
        # payload agora ? {"results": resultados, "source": origem, "path_var": caminho}
        results = payload.get("resultados")
        source = payload.get("origem")
        path_var = payload.get("caminho")

        if not isinstance(results, dict):
            messagebox.showerror("Erro", "Resultado inválido do processamento.")
            return

        if results.get("__cancelled__"):
            progress_var.set(0)
            messagebox.showinfo("Cancelado", "Processamento cancelado pelo usuário.")
            return
        if results.get("__empty__"):
            progress_var.set(0)
            messagebox.showwarning(
                "Aviso",
                results.get("__warning__") or "Nenhum dado foi encontrado neste PDF.",
            )
            return
        if results.get("__error__"):
            messagebox.showerror("Erro", results.get("__error__"))
            return

        # garante que results_by_source exista no globalVar
        try:
            from global_vars import results_by_source
        except Exception:
            results_by_source = {"MVA": [], "EH": []}

        # armazena por origem
        if source not in results_by_source:
            results_by_source[source] = []
        results_by_source[source].append((path_var, results))

        # armazena lista global e atualiza a tree
        listFiles.append(path_var)
        list_results.append(results)

        # atualiza a interface (label e tree)
        label_files_var.set(f"{os.path.basename(path_var)} ({source})")
        tree_update(tree)
        _scroll_tree_to_top(tree)
        messagebox.showinfo("Concluído", f"Processamento finalizado ({source})!")

    elif kind == "error":
        set_btn_cancel()
        messagebox.showerror("Erro", payload)
        return

    # Sempre agenda a próxima checagem, exceto se houve erro (onde damos return acima)
    root.after(50, lambda: _poll_queue(root, tree, progress_var, progress_bar, label_files_var, path_var))

def _project_base_dir() -> str:
    import sys

    if getattr(sys, "frozen", False):
        candidates = [
            Path(os.path.dirname(os.path.abspath(sys.executable))),
            Path(r"D:\pdfReader"),
        ]
    else:
        candidates = [
            Path(r"D:\pdfReader"),
        ]
    candidates.append(Path(os.path.dirname(os.path.abspath(__file__))))

    for candidate in candidates:
        if candidate.is_dir():
            return str(candidate)
    return str(candidates[-1])


def resource_path(relative_path): 
    import sys

    """Retorna o caminho absoluto do recurso, compatível com PyInstaller."""
    preferred_base = _project_base_dir()
    preferred_path = os.path.join(preferred_base, relative_path)
    if os.path.exists(preferred_path):
        return preferred_path
    if hasattr(sys, '_MEIPASS'):  # Executando empacotado
        bundled_path = os.path.join(sys._MEIPASS, relative_path)
        if os.path.exists(bundled_path):
            return bundled_path
    return preferred_path

def load_mapping(path='mapping.json'): 
  
    full_path = resource_path(path)
    if not os.path.exists(full_path):
        raise FileNotFoundError(f"Arquivo de mapeamento não encontrado: {full_path}")
    with open(full_path, 'r', encoding='utf-8') as f:
        mp = json.load(f)
    return {k.strip().upper(): v.strip() for (k, v) in mp.items()}

mapping = None
CANON_BY_VALUE_UPPER = None


def _ensure_mapping_loaded():
    global mapping, CANON_BY_VALUE_UPPER
    if mapping is None:
        mapping = load_mapping()
        CANON_BY_VALUE_UPPER = {v.upper(): v for v in mapping.values()}

def save_mapping(): 
    """Salva o mapeamento atualizado no arquivo do usuário."""
    appdata_dir = os.path.join(os.getenv("APPDATA"), "RelatorioClientes")
    os.makedirs(appdata_dir, exist_ok=True)
    user_json = os.path.join(appdata_dir, "mapping.json")
    with open(user_json, "w", encoding="utf-8") as f:
        json.dump(mapping, f, indent=4, ensure_ascii=False)

def _normalize_key(s: str) -> str:
    if not s:
        return ""
    s = s.replace('\u00A0', ' ')                # NBSP -> espaço
    s = re.sub(r"^\s*\d+\s*", "", s)            # remove prefixo numérico "14 C O" -> "C O"
    s = re.sub(r"\s+", " ", s)                  # espaços múltiplos
    s = s.replace("–", "-").replace("—", "-")   # normaliza hifens
    return s.strip().upper()

def parse_number(num_str: str) -> float:
    """Converte string numerica em float, suportando formatos BR e US, removendo R$."""
    if num_str is None:
        return 0.0
    if isinstance(num_str, (int, float)):
        return float(num_str)

    s = str(num_str).strip()
    if not s:
        return 0.0

    s = s.replace("R$", "").replace(" ", "").replace(" ", "")
    last_comma = s.rfind(",")
    last_dot = s.rfind(".")

    if last_comma != -1 and last_dot != -1:
        if last_comma > last_dot:
            s = s.replace(".", "").replace(",", ".")
        else:
            s = s.replace(",", "")
        return float(s)

    if last_comma != -1:
        return float(s.replace(",", "."))

    return float(s)

def format_number_br(num: float) -> str:
    """Formata número no padrão brasileiro com duas casas decimais."""
    return f"{num:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")


def normalizarClienteCaixa(nome: str, mantemAcentos: bool = False) -> str:
    """
    Normaliza o nome do cliente para comparações, opcionalmente mantendo acentuações.
    """
    import unicodedata

    if not nome:
        return ""

    normalizado = unicodedata.normalize("NFKD", nome)
    if not mantemAcentos:
        normalizado = "".join(ch for ch in normalizado if not unicodedata.combining(ch))

    return normalizado.strip().upper()

# Alias para compatibilidade legada
def _normalize_caixa_client(name: str) -> str:
    return normalizarClienteCaixa(name, mantemAcentos=False)



def _classify_caixa_document(description: str) -> str:
    normalized = _normalize_caixa_client(description)
    if (
        "NOTA FISCAL DE CONSUMIDOR" in normalized
        and "ELETR" in normalized
    ):
        return "Nota Fiscal de Consumidor Eletronica"
    if (
        "NOTA FISCAL" in normalized
        and "ELETR" in normalized
        and "CONSUMIDOR" not in normalized
    ):
        return "Nota Fiscal Eletronica"
    return description.strip()


def _is_eh_counter_client(cliente: str) -> bool:
    compacto = re.sub(r"[^A-Z]", "", _normalize_caixa_client(cliente))
    return compacto.startswith("CLIENTEBALC")


def _decode_report_response_text(response) -> str:
    content = response.content or b""
    encodings = []
    for encoding in (
        getattr(response, "apparent_encoding", None),
        getattr(response, "encoding", None),
        "utf-8",
        "latin1",
    ):
        encoding = str(encoding or "").strip()
        if encoding and encoding not in encodings:
            encodings.append(encoding)

    for encoding in encodings:
        try:
            texto = content.decode(encoding)
        except Exception:
            continue
        if texto:
            return texto
    return content.decode("utf-8", errors="ignore")


def _clean_zweb_html_value(value: str) -> str:
    texto = html.unescape(str(value or ""))
    texto = re.sub(r"<[^>]+>", " ", texto)
    texto = re.sub(r"\s+", " ", texto)
    return texto.strip()


def _extract_zweb_period(html_text: str) -> str | None:
    match = re.search(
        r"(\d{2}/\d{2}/\d{4})\s+at\S*\s+(\d{2}/\d{2}/\d{4})",
        html_text,
        re.IGNORECASE,
    )
    if not match:
        datas = re.findall(r"\d{2}/\d{2}/\d{4}", html_text[:4000])
        if len(datas) >= 2:
            return f"{datas[0]} - {datas[1]}"
        return None
    return f"{match.group(1)} - {match.group(2)}"


def _extract_zweb_fiscal_emission_iso(value: str) -> str:
    texto = str(value or "").strip()
    if not texto:
        return ""

    match = re.match(r"^(\d{4}-\d{2}-\d{2})", texto)
    if match:
        return match.group(1)

    for fmt in ("%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%S"):
        try:
            return datetime.strptime(texto, fmt).strftime("%Y-%m-%d")
        except ValueError:
            continue
    return ""


def _is_zweb_fiscal_cancelled(item: dict) -> bool:
    if item.get("canceledXml"):
        return True
    try:
        return int(item.get("status")) == 3
    except (TypeError, ValueError):
        return False


def _build_zweb_fiscal_status_map(itens: list[dict]) -> dict:
    status_map = {}
    for item in itens:
        numero = _normalize_fiscal_number(item.get("numero", ""))
        if not numero or numero in status_map:
            continue
        try:
            valor = round(float(item.get("valorTotal", 0.0) or 0.0), 2)
        except (TypeError, ValueError):
            valor = 0.0
        status_map[numero] = {
            "numero": numero,
            "numero_exibicao": _display_fiscal_number(numero),
            "cancelada": _is_zweb_fiscal_cancelled(item),
            "status_codigo": item.get("status"),
            "status_transmissao": item.get("statusTransmissao"),
            "modelo": str(item.get("modelo", "") or "").strip(),
            "emissao": _extract_zweb_fiscal_emission_iso(item.get("emission", "")),
            "valor": valor,
        }
    return status_map

def _analisar_html_pedidos_importados_eh(html_text: str, arquivo: str = "Pedidos importados - Zweb") -> dict:
    from bs4 import BeautifulSoup
    periodo = _extract_zweb_period(html_text)
    itens_brutos = []

    soup = BeautifulSoup(html_text, "html.parser")
    blocks = soup.find_all("div", class_="mt-3")

    for block in blocks:
        # Check if this block looks like an order (has the border style usually)
        style = block.get("style", "")
        if "border" not in style or "#A4A5A7" not in style:
            continue

        pedido_val = ""
        cliente_val = ""
        documento_val = ""
        tipo_val = ""
        valor_val = ""

        spans = block.find_all("span")
        for i, sp in enumerate(spans):
            sp_text = sp.get_text(strip=True)
            sp_lower = sp_text.lower()
            if "número do pedido:" in sp_lower and i + 1 < len(spans):
                pedido_val = spans[i+1].get_text(strip=True)
            elif "cliente:" in sp_lower and i + 1 < len(spans):
                cliente_val = spans[i+1].get_text(strip=True)
            elif sp_lower.startswith("n") and re.search(r'\d{6,}', sp_text):
                m = re.search(r'(\d{6,})', sp_text)
                if m:
                    documento_val = m.group(1)
        
        table = block.find("table")
        if table:
            tb = table.find("tbody")
            if tb:
                tr_data = tb.find("tr")
                if tr_data:
                    tr_tds = tr_data.find_all("td")
                    if len(tr_tds) >= 3:
                        n_span = tr_tds[0].find("span")
                        if n_span:
                            m = re.search(r'(\d{6,})', n_span.text)
                            if m:
                                documento_val = m.group(1)
                        tipo_val = tr_tds[1].get_text(strip=True)
                        valor_val = tr_tds[2].get_text(strip=True)

        if not all((cliente_val, documento_val, tipo_val, valor_val)):
            continue

        cliente = _clean_zweb_html_value(cliente_val)
        documento_fiscal = _normalize_fiscal_number(documento_val)
        descricao_tipo = _clean_zweb_html_value(tipo_val)
        valor = round(parse_number(valor_val), 2)

        itens_brutos.append(
            {
                "pedido_importado": pedido_val,
                "pedido": documento_fiscal,
                "cliente": cliente,
                "documento": _classify_caixa_document(descricao_tipo),
                "valor": valor,
            }
        )

    total_documento = round(sum(item["valor"] for item in itens_brutos), 2)
    total_excluido = 0.0
    pedidos_caixa = 0
    pedidos_balcao = 0
    pedidos_excluidos = 0
    pedidos_excluidos_cliente = 0
    pedidos_excluidos_documento = 0
    itens_caixa = []
    itens_excluidos = []

    for pedido in itens_brutos:
        cliente = pedido["cliente"]
        valor = pedido["valor"]
        is_balcao = _is_eh_counter_client(cliente)
        is_nfe = pedido["documento"] == "Nota Fiscal Eletronica"
        motivos = []

        if is_balcao:
            pedidos_balcao += 1
        else:
            pedidos_excluidos_cliente += 1
            motivos.append("Cliente diferente")

        if is_nfe:
            pedidos_excluidos_documento += 1
            motivos.append("NF-e")

        if motivos:
            total_excluido += valor
            pedidos_excluidos += 1
            itens_excluidos.append(
                {
                    "pedido": pedido["pedido"],
                    "cliente": cliente,
                    "documento": pedido["documento"],
                    "motivo": " + ".join(motivos),
                    "valor": valor,
                }
            )
            continue

        pedidos_caixa += 1
        itens_caixa.append(
            {
                "pedido": pedido["pedido"],
                "cliente": cliente,
                "documento": pedido["documento"],
                "valor": valor,
            }
        )

    total_excluido = round(total_excluido, 2)
    total_caixa = round(total_documento - total_excluido, 2)
    return {
        "arquivo": arquivo,
        "caixa_modelo": "EH",
        "arquivo_tipo": "pedidos_importados_eh",
        "periodo": periodo,
        "pedidos_total": len(itens_brutos),
        "pedidos_balcao": pedidos_balcao,
        "pedidos_caixa": pedidos_caixa,
        "pedidos_excluidos": pedidos_excluidos,
        "pedidos_excluidos_cliente": pedidos_excluidos_cliente,
        "pedidos_excluidos_documento": pedidos_excluidos_documento,
        "pedidos_excluidos_cancelados": 0,
        "total_documento": total_documento,
        "total_excluido": total_excluido,
        "total_excluido_cancelados": 0.0,
        "total_caixa": total_caixa,
        "itens_caixa": sorted(
            itens_caixa,
            key=lambda item: (item["pedido"], item["cliente"].casefold()),
        ),
        "itens_excluidos": sorted(
            itens_excluidos,
            key=lambda item: (-item["valor"], item["cliente"].casefold(), item["pedido"]),
        ),
    }


def _aplicar_filtro_canceladas_pedidos_eh(relatorio: dict, fiscal_status_map: dict) -> dict:
    if (relatorio.get("caixa_modelo") or "").upper() != "EH" or not fiscal_status_map:
        return relatorio

    itens_caixa_filtrados = []
    itens_excluidos = [{**item} for item in relatorio.get("itens_excluidos", [])]
    numeros_presentes = {
        _normalize_fiscal_number(item.get("pedido", ""))
        for item in list(relatorio.get("itens_caixa") or []) + itens_excluidos
    }
    cancelados_count = 0
    cancelados_valor = 0.0
    cancelados_presentes_valor = 0.0
    cancelados_ausentes_valor = 0.0

    for item in relatorio.get("itens_caixa", []):
        numero = _normalize_fiscal_number(item.get("pedido", ""))
        fiscal_info = fiscal_status_map.get(numero) or {}
        if fiscal_info.get("cancelada"):
            valor = round(float(item.get("valor", 0.0)), 2)
            cancelados_count += 1
            cancelados_valor = round(cancelados_valor + valor, 2)
            cancelados_presentes_valor = round(cancelados_presentes_valor + valor, 2)
            itens_excluidos.append(
                {
                    "pedido": item.get("pedido", ""),
                    "cliente": item.get("cliente", ""),
                    "documento": "NFC-e cancelada",
                    "motivo": "Cupom cancelado",
                    "valor": valor,
                }
            )
            continue
        itens_caixa_filtrados.append({**item})

    for numero, fiscal_info in sorted((fiscal_status_map or {}).items()):
        numero_normalizado = _normalize_fiscal_number(numero)
        if not numero_normalizado or numero_normalizado in numeros_presentes:
            continue
        if not (fiscal_info or {}).get("cancelada"):
            continue
        valor = round(float((fiscal_info or {}).get("valor", 0.0) or 0.0), 2)
        cancelados_count += 1
        cancelados_valor = round(cancelados_valor + valor, 2)
        cancelados_ausentes_valor = round(cancelados_ausentes_valor + valor, 2)
        itens_excluidos.append(
            {
                "pedido": numero_normalizado,
                "cliente": "CLIENTE BALCÃO",
                "documento": "NFC-e cancelada",
                "motivo": "Cupom cancelado",
                "valor": valor,
            }
        )
        numeros_presentes.add(numero_normalizado)

    if not cancelados_count:
        return relatorio

    total_excluido = round(float(relatorio.get("total_excluido", 0.0)) + cancelados_valor, 2)
    total_caixa = round(float(relatorio.get("total_caixa", 0.0)) - cancelados_presentes_valor, 2)
    total_documento = round(float(relatorio.get("total_documento", 0.0)) + cancelados_ausentes_valor, 2)

    return {
        **relatorio,
        "pedidos_caixa": len(itens_caixa_filtrados),
        "pedidos_excluidos": len(itens_excluidos),
        "pedidos_excluidos_cancelados": int(relatorio.get("pedidos_excluidos_cancelados", 0)) + cancelados_count,
        "total_excluido": total_excluido,
        "total_excluido_cancelados": round(
            float(relatorio.get("total_excluido_cancelados", 0.0)) + cancelados_valor,
            2,
        ),
        "total_documento": total_documento,
        "total_caixa": total_caixa,
        "itens_caixa": sorted(
            itens_caixa_filtrados,
            key=lambda current: (current.get("pedido", ""), str(current.get("cliente", "")).casefold()),
        ),
        "itens_excluidos": sorted(
            itens_excluidos,
            key=lambda current: (
                -round(float(current.get("valor", 0.0)), 2),
                str(current.get("cliente", "")).casefold(),
                current.get("pedido", ""),
            ),
        ),
    }


def _display_zweb_short_date(data_texto: str) -> str:
    texto = str(data_texto or "").strip()
    if not texto:
        return ""
    for formato in ("%d/%m/%y", "%d/%m/%Y"):
        try:
            return datetime.strptime(texto, formato).strftime("%d/%m/%Y")
        except ValueError:
            continue
    return texto


def _build_zweb_payment_report_meta(label: str) -> dict | None:
    titulo = _clean_zweb_html_value(label)
    if "|" in titulo:
        titulo = titulo.split("|", 1)[1].strip()
    titulo = _clean_zweb_html_value(titulo)
    titulo_normalizado = _normalize_caixa_client(titulo)

    if not titulo_normalizado:
        return None
    if "PAGAMENTO INSTANTANEO" in titulo_normalizado and "PIX" in titulo_normalizado:
        return {
            "key": "pix_fechamento",
            "tab_title": "PIX Fechamento",
            "menu_text": "Abrir PIX fechamento",
            "summary_label": "PIX fechamento",
            "total_label": "Total PIX fechamento",
            "section_label": "Transações PIX no Fechamento",
            "empty_message": "Nenhuma transação PIX encontrada no Fechamento para este dia.",
            "forma_pagamento": titulo,
        }
    if "DINHEIRO" in titulo_normalizado:
        return {
            "key": "dinheiro",
            "tab_title": "Dinheiro",
            "menu_text": "Abrir dinheiro",
            "summary_label": "Dinheiro",
            "total_label": "Total dinheiro",
            "section_label": "Transações em dinheiro",
            "empty_message": "Nenhuma transação em dinheiro encontrada para este dia.",
            "forma_pagamento": titulo,
        }
    if "CARTAO DE CREDITO" in titulo_normalizado:
        return {
            "key": "cartao_credito",
            "tab_title": "Cartão de Crédito",
            "menu_text": "Abrir cartão de crédito",
            "summary_label": "Cartão de crédito",
            "total_label": "Total cartão de crédito",
            "section_label": "Transações em cartão de crédito",
            "empty_message": "Nenhuma transação em cartão de crédito encontrada para este dia.",
            "forma_pagamento": titulo,
        }
    if "CARTAO DE DEBITO" in titulo_normalizado:
        return {
            "key": "cartao_debito",
            "tab_title": "Cartão de Débito",
            "menu_text": "Abrir cartão de débito",
            "summary_label": "Cartão de débito",
            "total_label": "Total cartão de débito",
            "section_label": "Transações em cartão de débito",
            "empty_message": "Nenhuma transação em cartão de débito encontrada para este dia.",
            "forma_pagamento": titulo,
        }

    slug = re.sub(r"[^a-z0-9]+", "_", titulo_normalizado.casefold()).strip("_")
    if not slug:
        return None
    titulo_minusculo = titulo.casefold()
    return {
        "key": slug,
        "tab_title": titulo,
        "menu_text": f"Abrir {titulo_minusculo}",
        "summary_label": titulo,
        "total_label": f"Total {titulo_minusculo}",
        "section_label": f"Transações - {titulo}",
        "empty_message": f"Nenhuma transação em {titulo_minusculo} encontrada para este dia.",
        "forma_pagamento": titulo,
    }


def _normalize_ascii_text(value: str) -> str:
    return unicodedata.normalize("NFKD", str(value or "")).encode("ascii", "ignore").decode().casefold()


def _mask_sensitive_text(value: str) -> str:
    text = str(value or "")
    if "@" in text:
        return re.sub(
            r"([A-Za-z0-9._%+-]{1,3})[A-Za-z0-9._%+-]*(@[A-Za-z0-9.-]+)",
            r"\1***\2",
            text,
        )
    return text


def _sanitize_cielo_log_value(value, key: str = ""):
    key_norm = _normalize_ascii_text(key)
    sensitive_key = any(marker in key_norm for marker in ("senha", "password", "token", "codigo", "code", "secret"))
    safe_metadata_key = any(
        marker in key_norm
        for marker in (
            "visible",
            "present",
            "enabled",
            "requested",
            "attempt",
            "count",
            "length",
            "len",
            "found",
            "source",
            "state",
            "status",
            "challenge",
            "selected",
            "confirmed",
            "matches",
            "result",
            "elapsed",
            "timeout",
        )
    )
    if sensitive_key and not safe_metadata_key:
        return "[redacted]"
    if isinstance(value, dict):
        return {str(k): _sanitize_cielo_log_value(v, str(k)) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_sanitize_cielo_log_value(item, key) for item in value[:50]]
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, str):
        if sensitive_key:
            return "[redacted]"
        sanitized = _mask_sensitive_text(value)
        return sanitized if len(sanitized) <= 700 else sanitized[:700] + "...[truncated]"
    if isinstance(value, (int, float, bool)) or value is None:
        return value
    return str(value)


def _new_cielo_debug_log_path(data_br: str, company: str = "MVA") -> Path:
    safe_date = re.sub(r"\D", "", str(data_br or "")) or datetime.now().strftime("%Y%m%d")
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    target_dir = Path(_active_report_dir())
    target_dir.mkdir(parents=True, exist_ok=True)
    return target_dir / f"cielo_{_normalize_ascii_text(company) or 'mva'}_debug_{safe_date}_{stamp}.log"


def _cielo_debug_logs_enabled() -> bool:
    raw = str(os.environ.get("PDFREADER_CIELO_DEBUG") or "").strip().casefold()
    if raw in {"1", "true", "yes", "sim", "on"}:
        return True
    for marker_name in ("analisar_cielo.txt", "cielo_debug.flag", "debug_cielo.txt"):
        try:
            if (Path(_project_base_dir()) / marker_name).is_file():
                return True
        except Exception:
            continue
    return False


CIELO_DEBUG_LOGS_ENABLED = _cielo_debug_logs_enabled()
AZULZINHA_DEBUG_ARTIFACTS_ENABLED = False
GMAIL_BODY_DEBUG_ENABLED = False


class _NoopDebugArtifactPath:
    def __init__(self, path: Path):
        self.path = path

    def write_text(self, *args, **kwargs) -> int:
        return 0

    def __str__(self) -> str:
        return str(self.path)


class _AutoArtifactDir:
    def __init__(self, base_dir: str | os.PathLike):
        self.base_dir = Path(base_dir)

    def __truediv__(self, name: str | os.PathLike):
        target = self.base_dir / name
        if _is_debug_artifact_name(target.name) and not AZULZINHA_DEBUG_ARTIFACTS_ENABLED:
            return _NoopDebugArtifactPath(target)
        return target


def _is_debug_artifact_name(name: str) -> bool:
    name_norm = str(name or "").casefold()
    return (
        name_norm == "body_email.txt"
        or name_norm == "debug_zweb.html"
        or name_norm.startswith("azulzinha_")
        or name_norm.startswith("cielo_snapshot_")
        or name_norm.startswith("cielo_") and "_debug_" in name_norm
    )


def _write_cielo_debug_log(log_path: Path | str | None, event: str, **details) -> None:
    if not CIELO_DEBUG_LOGS_ENABLED:
        return
    if not log_path:
        return
    try:
        path = Path(log_path)
        payload = {
            "ts": datetime.now().isoformat(timespec="seconds"),
            "event": str(event or "").strip(),
            "details": _sanitize_cielo_log_value(details),
        }
        with path.open("a", encoding="utf-8", newline="\n") as fh:
            fh.write(json.dumps(payload, ensure_ascii=False, sort_keys=True) + "\n")
    except Exception:
        pass


def _display_eh_order_number(numero: str) -> str:
    return _display_fiscal_number(_normalize_fiscal_number(numero))


def _candidate_local_report_dirs() -> list[Path]:
    dirs = []
    seen = set()
    raw_dirs: list[str | Path] = [_active_report_dir()]
    if getattr(sys, "frozen", False):
        try:
            raw_dirs.append(Path(os.path.dirname(os.path.abspath(sys.executable))))
        except Exception:
            pass
    raw_dirs.append(Path(r"D:\pdfReader"))
    for raw in raw_dirs:
        path = Path(str(raw or "")).expanduser()
        key = str(path).casefold()
        if not path.exists() or key in seen:
            continue
        seen.add(key)
        dirs.append(path)
    return dirs


def _active_report_dir() -> str:
    import sys

    if getattr(sys, "frozen", False):
        base_dir = os.path.dirname(os.path.abspath(sys.executable))
    else:
        base_dir = os.getcwd()
    if base_dir and os.path.isdir(base_dir):
        return base_dir
    return _runtime_user_dir()


def _browser_debug_visible_enabled() -> bool:
    value = str(os.environ.get("PDFREADER_SHOW_BROWSER") or "").strip().casefold()
    if value in {"1", "true", "yes", "sim", "on"}:
        return True

    for name in ("mostrar_navegador.txt", "browser_visible.flag", "debug_browser_visible.txt"):
        try:
            if (Path(_active_report_dir()) / name).exists():
                return True
        except Exception:
            continue
    return False


def _browser_debug_keep_open_enabled() -> bool:
    value = str(os.environ.get("PDFREADER_KEEP_BROWSER_OPEN") or "").strip().casefold()
    return _browser_debug_visible_enabled() and value in {"1", "true", "yes", "sim", "on"}


def _azulzinha_sales_period_shortcut(data_br: str, reference_date=None) -> str | None:
    """Returns the safe relative-period shortcut supported by the sales portal."""
    try:
        target_date = datetime.strptime(str(data_br or ""), "%d/%m/%Y").date()
    except ValueError:
        return None

    current_date = reference_date or datetime.now().date()
    if target_date == current_date - timedelta(days=1):
        return "ontem"
    return None


def _is_azulzinha_captcha_page(
    url: str,
    title: str,
    body_text: str,
    frame_sources: Iterable[str],
) -> bool:
    url_normalized = str(url or "").casefold()
    title_normalized = _normalize_ascii_text(title)
    text_normalized = _normalize_ascii_text(body_text)
    frame_text = " ".join(str(source or "") for source in frame_sources).casefold()

    return (
        "validate.perfdrive.com" in url_normalized
        or "radware bot manager captcha" in title_normalized
        or "hcaptcha" in frame_text
        or "h-captcha" in frame_text
        or (
            "captcha" in text_normalized
            and any(marker in text_normalized for marker in ("verificacao", "seguranca", "robo"))
        )
    )


def _save_zweb_html_report(data_br: str, report_key: str, html_text: str) -> str:
    report_dir = Path(_active_report_dir())
    report_dir.mkdir(parents=True, exist_ok=True)
    safe_date = str(data_br or "").replace("/", "-").strip() or "sem-data"
    filename_map = {
        "pedidos_importados": f"Pedidos_importados_{safe_date}_eh_zweb_auto.html",
        "fechamento_caixa": f"Fechamento_de_caixa_{safe_date}_eh_zweb_auto.html",
    }
    filename = filename_map.get(report_key) or f"Relatorio_Zweb_{safe_date}_{report_key}_auto.html"
    target = report_dir / filename
    target.write_text(str(html_text or ""), encoding="utf-8")
    return str(target)


_LOCAL_REPORT_SUFFIXES = (".csv", ".xlsx", ".xls", ".pdf")


def _effective_local_report_suffix(path_like: str | Path) -> str:
    path = Path(path_like)
    suffix = path.suffix.lower()
    if suffix == ".crdownload":
        nested_suffix = Path(path.stem).suffix.lower()
        if nested_suffix in _LOCAL_REPORT_SUFFIXES:
            return nested_suffix
    return suffix


def _finalize_local_report_path(path_like: str | Path) -> str:
    path = Path(path_like)
    if path.suffix.lower() != ".crdownload":
        return str(path)
    if _effective_local_report_suffix(path) not in _LOCAL_REPORT_SUFFIXES:
        return str(path)
    target = path.with_suffix("")
    try:
        path.replace(target)
        return str(target)
    except Exception:
        if target.exists():
            return str(target)
        return str(path)


def _download_watch_dirs(download_dir: str | os.PathLike | None) -> list[Path]:
    raw_dirs: list[str | os.PathLike | None] = [
        download_dir,
        _active_report_dir(),
        Path.home() / "Downloads",
    ]
    user_profile = os.environ.get("USERPROFILE")
    if user_profile:
        raw_dirs.append(Path(user_profile) / "Downloads")

    seen: set[str] = set()
    dirs: list[Path] = []
    for raw in raw_dirs:
        if not raw:
            continue
        try:
            path = Path(raw).expanduser()
            key = str(path.resolve() if path.exists() else path.absolute()).casefold()
        except Exception:
            continue
        if key in seen or not path.is_dir():
            continue
        seen.add(key)
        dirs.append(path)
    return dirs


def _report_suffix_from_response_metadata(mime_type: str, content_disposition: str, default: str = ".pdf") -> str:
    mime_norm = str(mime_type or "").lower()
    disposition_norm = str(content_disposition or "").lower()
    if "csv" in mime_norm or "csv" in disposition_norm:
        return ".csv"
    if ".xlsx" in disposition_norm or "spreadsheetml" in mime_norm:
        return ".xlsx"
    if ".xls" in disposition_norm or "excel" in mime_norm or "sheet" in mime_norm:
        return ".xls"
    if "pdf" in mime_norm or "pdf" in disposition_norm:
        return ".pdf"
    return default


def _read_pdf_text(path: str | Path) -> str:
    pdfplumber = _get_pdfplumber()
    with pdfplumber.open(str(path)) as pdf:
        return "\n".join((page.extract_text() or "") for page in pdf.pages)


def _read_text_file(path: str | Path) -> str:
    for encoding in ("utf-8-sig", "utf-8", "cp1252", "latin1"):
        try:
            return Path(path).read_text(encoding=encoding)
        except UnicodeDecodeError:
            continue
    return Path(path).read_text(encoding="utf-8", errors="ignore")


def _read_xlsx_rows_fallback(path: str | Path) -> list[tuple[str, list[list[str]]]]:
    import posixpath
    import xml.etree.ElementTree as ET
    from zipfile import ZipFile

    ns_main = {"x": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    rel_ns = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}id"
    ns_pkg = {"r": "http://schemas.openxmlformats.org/package/2006/relationships"}

    def _xlsx_col_index(ref: str) -> int:
        letters = re.match(r"([A-Z]+)", str(ref or "").upper())
        if not letters:
            return 0
        value = 0
        for ch in letters.group(1):
            value = (value * 26) + (ord(ch) - 64)
        return value

    def _shared_strings(archive: ZipFile) -> list[str]:
        if "xl/sharedStrings.xml" not in archive.namelist():
            return []
        root = ET.fromstring(archive.read("xl/sharedStrings.xml"))
        items: list[str] = []
        for si in root.findall("x:si", ns_main):
            texts = [node.text or "" for node in si.findall(".//x:t", ns_main)]
            items.append("".join(texts))
        return items

    def _sheet_paths(archive: ZipFile) -> list[tuple[str, str]]:
        workbook_name = "xl/workbook.xml"
        rels_name = "xl/_rels/workbook.xml.rels"
        if workbook_name not in archive.namelist():
            return [("sheet1", "xl/worksheets/sheet1.xml")] if "xl/worksheets/sheet1.xml" in archive.namelist() else []
        workbook_root = ET.fromstring(archive.read(workbook_name))
        rel_map: dict[str, str] = {}
        if rels_name in archive.namelist():
            rel_root = ET.fromstring(archive.read(rels_name))
            for rel in rel_root.findall("r:Relationship", ns_pkg):
                rel_id = str(rel.attrib.get("Id") or "")
                target = str(rel.attrib.get("Target") or "")
                if rel_id and target:
                    rel_map[rel_id] = posixpath.normpath(posixpath.join("xl", target))
        sheets: list[tuple[str, str]] = []
        for sheet in workbook_root.findall(".//x:sheets/x:sheet", ns_main):
            name = str(sheet.attrib.get("name") or "sheet")
            rel_id = str(sheet.attrib.get(rel_ns) or "")
            target = rel_map.get(rel_id)
            if target and target in archive.namelist():
                sheets.append((name, target))
        if not sheets and "xl/worksheets/sheet1.xml" in archive.namelist():
            sheets.append(("sheet1", "xl/worksheets/sheet1.xml"))
        return sheets

    def _sheet_rows(archive: ZipFile, sheet_path: str, shared: list[str]) -> list[list[str]]:
        root = ET.fromstring(archive.read(sheet_path))
        rows: list[list[str]] = []
        for row in root.findall(".//x:sheetData/x:row", ns_main):
            values: dict[int, str] = {}
            max_col = 0
            for cell in row.findall("x:c", ns_main):
                ref = str(cell.attrib.get("r") or "")
                col = _xlsx_col_index(ref)
                max_col = max(max_col, col)
                cell_type = str(cell.attrib.get("t") or "")
                if cell_type == "inlineStr":
                    value = "".join(node.text or "" for node in cell.findall(".//x:t", ns_main))
                else:
                    node = cell.find("x:v", ns_main)
                    raw = str(node.text or "") if node is not None else ""
                    if cell_type == "s" and raw.isdigit():
                        idx = int(raw)
                        value = shared[idx] if 0 <= idx < len(shared) else raw
                    else:
                        value = raw
                if col:
                    values[col] = value
            if max_col:
                rows.append([values.get(idx, "") for idx in range(1, max_col + 1)])
        return rows

    with ZipFile(path) as archive:
        shared = _shared_strings(archive)
        return [(sheet_name, _sheet_rows(archive, sheet_path, shared)) for sheet_name, sheet_path in _sheet_paths(archive)]


def _read_excel_text(path: str | Path) -> str:
    import pandas as pd

    chunks: list[str] = []
    try:
        xls = pd.ExcelFile(path)
        for sheet_name in xls.sheet_names:
            df = pd.read_excel(xls, sheet_name=sheet_name, dtype=str)
            if df.empty:
                continue
            chunks.append(sheet_name)
            header_text = " ".join(str(value or "").strip() for value in df.columns if str(value or "").strip())
            if header_text:
                chunks.append(header_text)
            chunks.extend(" ".join(str(value or "").strip() for value in row if str(value or "").strip()) for row in df.fillna("").values.tolist())
    except Exception:
        try:
            fallback_rows = _read_xlsx_rows_fallback(path)
        except Exception:
            text = _read_text_file(path)
            return text
        for sheet_name, rows in fallback_rows:
            if not rows:
                continue
            chunks.append(sheet_name)
            chunks.extend(
                " ".join(str(value or "").strip() for value in row if str(value or "").strip())
                for row in rows
                if any(str(value or "").strip() for value in row)
            )
    return "\n".join(chunks)


def _extract_local_report_date_br(text: str) -> str | None:
    if not text:
        return None
    text_norm = _normalize_ascii_text(text)
    preferred_patterns = (
        r"periodo(?:\s+de\s+venda)?\D{0,80}(\d{2}/\d{2}/\d{4})\s+(?:a|ate|-)\s+(\d{2}/\d{2}/\d{4})",
        r"relatorio\s+inicio\s*-\s*fim\D{0,80}(\d{2}/\d{2}/\d{4})\s+(?:a|ate|-)\s+(\d{2}/\d{2}/\d{4})",
        r"(\d{2}/\d{2}/\d{4})\s+(?:a|ate|-)\s+(\d{2}/\d{2}/\d{4})",
    )
    for pattern in preferred_patterns:
        match = re.search(pattern, text_norm, re.IGNORECASE)
        if match:
            return match.group(1)
    match = re.search(r"data\s+da\s+venda\D{0,80}(\d{2}/\d{2}/\d{4})\b", text_norm, re.IGNORECASE)
    if match:
        return match.group(1)
    match = re.search(r"\b(\d{2}/\d{2}/\d{4})\b", text_norm)
    if match:
        return match.group(1)
    return None


def _path_name_contains_br_date(path_like: str | Path, data_br: str) -> bool:
    if not data_br:
        return False
    date_tokens = {
        data_br,
        data_br.replace("/", "-"),
        data_br.replace("/", ""),
    }
    name_norm = _normalize_ascii_text(Path(path_like).name)
    return any(_normalize_ascii_text(token) in name_norm for token in date_tokens)


def _caixa_rows_include_date(rows: list[dict[str, str]], data_br: str) -> bool:
    if not data_br:
        return True
    saw_any_date = False
    for row in rows:
        normalized_row = {_normalize_ascii_text(key): str(value or "").strip() for key, value in row.items()}
        data_raw = normalized_row.get("data da venda", "")
        match = re.search(r"\b(\d{2}/\d{2}/\d{4})\b", _normalize_ascii_text(data_raw))
        if not match:
            continue
        saw_any_date = True
        if match.group(1) == data_br:
            return True
    return not saw_any_date


def _caixa_xlsx_rows_have_sales_headers(rows: list[dict[str, str]]) -> bool:
    for row in rows:
        keys = {_normalize_ascii_text(key) for key in row.keys()}
        if "data da venda" in keys and "valor bruto" in keys and "status" in keys:
            return True
    return False


def _looks_like_caixa_card_report_text(text: str) -> bool:
    text_norm = _normalize_ascii_text(text)
    if not text_norm:
        return False
    if "relatorio de vendas pix" in text_norm or "vendas pix" in text_norm:
        return False
    has_sales_headers = "data da venda" in text_norm and "valor bruto" in text_norm and "status" in text_norm
    has_card_columns = (
        "produto" in text_norm
        and (
            "bandeira" in text_norm
            or "parcelas" in text_norm
            or "comprovante da venda" in text_norm
            or "numero do terminal" in text_norm
            or "credito" in text_norm
            or "debito" in text_norm
        )
    )
    has_card_title = (
        "relatorio de vendas_historico de vendas" in text_norm
        or "relatorio de historico de vendas" in text_norm
        or "historico de vendas" in text_norm
    )
    return has_sales_headers and (has_card_columns or has_card_title)


def _looks_like_caixa_pix_xlsx(path_like: str | Path, data_br: str, text: str = "") -> bool:
    path = Path(path_like)
    text_norm = _normalize_ascii_text(text)
    name_suggests_pix = "pix" in _normalize_ascii_text(path.name)
    title_suggests_pix = "relatorio de vendas pix" in text_norm
    if not name_suggests_pix and not title_suggests_pix:
        return False
    if title_suggests_pix and "valor total de vendas finalizadas" in text_norm:
        return True
    try:
        rows = _collect_card_rows_from_caixa_xlsx(str(path))
    except Exception:
        return False
    if not rows or not _caixa_xlsx_rows_have_sales_headers(rows):
        return False
    if _path_name_contains_br_date(path, data_br):
        return True
    return _caixa_rows_include_date(rows, data_br)


def _find_eh_local_payment_reports(data_br: str, *, company: str = "EH") -> dict[str, object]:
    pix_csv_matches: list[Path] = []
    pix_xlsx_matches: list[Path] = []
    pix_pdf_matches: list[Path] = []
    card_matches: list[Path] = []
    avisos: list[str] = []
    patterns = ("*.pdf", "*.csv", "*.xlsx", "*.xls", "*.crdownload")
    company_norm = _normalize_ascii_text(company) or "eh"

    preferred_dirs = _candidate_local_report_dirs()

    for directory in preferred_dirs:
        for pattern in patterns:
            for path in directory.glob(pattern):
                try:
                    effective_suffix = _effective_local_report_suffix(path)
                    if effective_suffix == ".csv":
                        text = _read_text_file(path)
                    elif effective_suffix in {".xlsx", ".xls"}:
                        text = _read_excel_text(path)
                    elif effective_suffix == ".pdf":
                        text = _read_pdf_text(path)
                    else:
                        continue
                except Exception:
                    continue

                text_norm = _normalize_ascii_text(text)
                name_norm = _normalize_ascii_text(path.name)
                if "cielo" in name_norm or "cielo" in text_norm[:6000]:
                    continue
                detected_date = _extract_local_report_date_br(text)
                report_kind = None
                normalized_path = Path(_finalize_local_report_path(path))
                if effective_suffix == ".csv" and "data da venda" in text_norm and "valor bruto" in text_norm:
                    report_kind = "pix_csv"
                elif effective_suffix in {".xlsx", ".xls"} and _looks_like_caixa_pix_xlsx(normalized_path, data_br, text):
                    report_kind = "pix_xlsx"
                elif "extrato pix" in text_norm:
                    report_kind = "pix_pdf"
                elif effective_suffix in {".xlsx", ".xls"} and _looks_like_caixa_card_report_text(text):
                    report_kind = "cartoes"
                elif _looks_like_caixa_card_report_text(text):
                    report_kind = "cartoes"
                else:
                    continue

                if detected_date and detected_date != data_br:
                    tipo = "PIX" if report_kind.startswith("pix") else "cartões"
                    avisos.append(
                        f'O arquivo "{path.name}" foi identificado como relatório de {tipo}, mas o conteúdo é de {detected_date} e não de {data_br}. '
                        "Ele foi ignorado."
                    )
                    continue

                if report_kind == "pix_csv":
                    pix_csv_matches.append(normalized_path)
                elif report_kind == "pix_xlsx":
                    pix_xlsx_matches.append(normalized_path)
                elif report_kind == "pix_pdf":
                    pix_pdf_matches.append(normalized_path)
                else:
                    card_matches.append(normalized_path)

    def _pick_latest(paths: list[Path]) -> str | None:
        if not paths:
            return None
        explicit_other_company_paths = [
            item
            for item in paths
            if any(f"_{other}_auto" in item.stem.casefold() for other in ("eh", "mva") if other != company_norm)
        ]
        paths = [item for item in paths if item not in explicit_other_company_paths]
        if not paths:
            return None
        def _score(item: Path) -> tuple[int, float]:
            name = item.stem.casefold()
            if name.endswith(f"_{company_norm}_auto"):
                company_score = 4
            elif f"_{company_norm}_auto" in name:
                company_score = 3
            elif "_auto" in name:
                company_score = 1
            else:
                company_score = 0
            return (company_score, item.stat().st_mtime)

        latest = max(paths, key=_score)
        return str(latest)

    pix_match = _pick_latest(pix_csv_matches + pix_xlsx_matches) or _pick_latest(pix_pdf_matches)
    card_match = _pick_latest(card_matches)
    avisos_filtrados = []
    for aviso in avisos:
        aviso_norm = _normalize_ascii_text(aviso)
        if pix_match and "relatorio de pix" in aviso_norm:
            continue
        if card_match and "relatorio de cart" in aviso_norm:
            continue
        avisos_filtrados.append(aviso)

    return {
        "pix": pix_match,
        "cartoes": card_match,
        "avisos": list(dict.fromkeys(avisos_filtrados)),
    }


def _integrate_local_payment_reports(
    relatorio_fechamento: dict,
    data_br: str,
    *,
    avisos_usuario: list[str] | None = None,
    relatorio_pix_padrao: dict | None = None,
    company: str = "EH",
) -> tuple[dict, dict | None, list[str]]:
    avisos = list(avisos_usuario or [])
    local_payment_reports = _find_eh_local_payment_reports(data_br, company=company)
    local_pix_pdf = local_payment_reports.get("pix")
    local_card_pdf = local_payment_reports.get("cartoes")
    avisos.extend(local_payment_reports.get("avisos") or [])
    scope_windows = _report_scope_windows(relatorio_fechamento)
    scope_label = " dentro do escopo horário do fechamento" if scope_windows else ""

    relatorios_pagamento = dict(relatorio_fechamento.get("relatorios_pagamento") or {})
    relatorio_pix = _filter_payment_report_to_scope(relatorio_pix_padrao, scope_windows)

    if local_card_pdf:
        try:
            relatorios_cartao = _build_card_reports_from_caixa(local_card_pdf, data_br)
            relatorios_validos = {}
            for key, report in relatorios_cartao.items():
                report_filtrado = _filter_payment_report_to_scope(report, scope_windows)
                if report_filtrado.get("itens_autorizados"):
                    relatorios_validos[key] = report_filtrado
            if relatorios_validos:
                relatorios_pagamento.update(relatorios_validos)
            else:
                avisos.append(
                    f'O arquivo "{os.path.basename(local_card_pdf)}" não trouxe transações de cartão para {data_br}{scope_label} e foi ignorado.'
                )
        except Exception as exc:
            avisos.append(
                f'Não foi possível ler o arquivo "{os.path.basename(local_card_pdf)}" para {data_br}: {exc}'
            )

    if local_pix_pdf:
        try:
            pix_suffix = _effective_local_report_suffix(local_pix_pdf)
            if pix_suffix == ".csv":
                relatorio_pix = _build_pix_report_from_caixa_csv(local_pix_pdf, data_br)
            elif pix_suffix == ".xlsx":
                relatorio_pix = _build_pix_report_from_caixa_xlsx(local_pix_pdf, data_br)
            else:
                relatorio_pix = _build_pix_report_from_caixa_pdf(local_pix_pdf, data_br)
            relatorio_pix = _filter_payment_report_to_scope(relatorio_pix, scope_windows)
            if relatorio_pix.get("quantidade_autorizados", 0) <= 0:
                avisos.append(
                    f'O arquivo "{os.path.basename(local_pix_pdf)}" não trouxe transações PIX para {data_br}{scope_label} e foi ignorado.'
                )
                relatorio_pix = _filter_payment_report_to_scope(relatorio_pix_padrao, scope_windows)
        except Exception as exc:
            avisos.append(
                f'Não foi possível ler o arquivo "{os.path.basename(local_pix_pdf)}" para {data_br}: {exc}'
            )
            relatorio_pix = _filter_payment_report_to_scope(relatorio_pix_padrao, scope_windows)

    relatorio_fechamento["relatorios_pagamento"] = relatorios_pagamento
    if relatorio_pix:
        relatorios_pagamento[str(relatorio_pix.get("categoria") or "pix_caixa")] = relatorio_pix

    avisos = list(dict.fromkeys(avisos))
    if avisos:
        relatorio_fechamento["avisos_usuario"] = avisos
        if relatorio_pix is not None:
            relatorio_pix["avisos_usuario"] = avisos

    _cleanup_eh_auto_payment_reports(local_pix_pdf, local_card_pdf)
    return relatorio_fechamento, relatorio_pix, avisos


def _load_azulzinha_credentials(company: str = "EH") -> dict | None:
    company_norm = _normalize_ascii_text(company)
    target_cnpj = "34.636.193/0001-93" if company_norm == "eh" else "18.471.209/0001-07"
    env_user = os.environ.get(f"AZULZINHA_{company_norm.upper()}_CNPJ")
    env_password = os.environ.get(f"AZULZINHA_{company_norm.upper()}_PASSWORD")
    if env_user and env_password:
        return {
            "cnpj": str(env_user).strip(),
            "password": str(env_password).strip(),
            "base_url": "https://portal.azulzinhadacaixa.com.br",
            "login_url": "https://portal.azulzinhadacaixa.com.br/",
            "sales_url": "https://portal.azulzinhadacaixa.com.br/MinhasVendas?Router=0",
        }

    candidate_files = [
        _runtime_file_path("credenciais.txt"),
        _runtime_file_path("credencias.txt"),
        _runtime_file_path("passo-a-passo.txt"),
    ]
    cnpj_pattern = re.compile(r"^\d{2}\.\d{3}\.\d{3}/\d{4}-\d{2}$")

    for caminho in candidate_files:
        if not caminho.is_file():
            continue
        try:
            linhas = [corrigir_texto(linha.strip()) for linha in caminho.read_text(encoding="utf-8", errors="ignore").splitlines()]
        except OSError:
            continue
        for idx, linha in enumerate(linhas):
            if not cnpj_pattern.match(linha):
                continue
            senha = str(linhas[idx + 1] if len(linhas) > idx + 1 else "").strip()
            if linha == target_cnpj and senha:
                return {
                    "cnpj": linha,
                    "password": senha,
                    "base_url": "https://portal.azulzinhadacaixa.com.br",
                    "login_url": "https://portal.azulzinhadacaixa.com.br/",
                    "sales_url": "https://portal.azulzinhadacaixa.com.br/MinhasVendas?Router=0",
                }
    return None


def _format_azulzinha_login_rejected_message(error_message: str, company_label: str = "EH") -> str:
    detail = str(error_message or "").strip()
    prefix = f"A Azulzinha/Caixa recusou o login da {company_label}."
    if detail:
        prefix = f"{prefix}\nMotivo informado pelo portal: {detail}"
    return (
        f"{prefix}\n\n"
        "Credenciais mudaram? Confira o CNPJ e a senha no arquivo credenciais.txt, "
        "na seção CONTA AZULZINHA / CAIXA, e atualize esse arquivo para os próximos usos."
    )


def _load_cielo_credentials(company: str = "MVA") -> dict | None:
    company_norm = _normalize_ascii_text(company) or "mva"
    env_user = os.environ.get(f"CIELO_{company_norm.upper()}_EMAIL") or os.environ.get("CIELO_EMAIL")
    env_password = os.environ.get(f"CIELO_{company_norm.upper()}_PASSWORD") or os.environ.get("CIELO_PASSWORD")
    if env_user and env_password:
        return {
            "email": str(env_user).strip(),
            "password": str(env_password).strip(),
            "login_url": "https://minhaconta2.cielo.com.br/site/acessos/login",
            "base_url": "https://minhaconta2.cielo.com.br",
        }

    candidate_files = [
        _runtime_file_path("credenciais.txt"),
        _runtime_file_path("credencias.txt"),
        _runtime_file_path("passo-a-passo.txt"),
    ]
    for caminho in candidate_files:
        if not caminho.is_file():
            continue
        try:
            linhas = [corrigir_texto(linha.strip()) for linha in caminho.read_text(encoding="utf-8", errors="ignore").splitlines()]
        except OSError:
            continue
        for idx, linha in enumerate(linhas):
            if "cielo" not in _normalize_ascii_text(linha):
                continue
            email = ""
            password = ""
            for candidate in linhas[idx + 1 : idx + 10]:
                candidate = str(candidate or "").strip()
                if not candidate:
                    continue
                if "@" in candidate and not email:
                    email = candidate
                    continue
                if email and not password:
                    password = candidate
                    break
            if email and password:
                return {
                    "email": email,
                    "password": password,
                    "login_url": "https://minhaconta2.cielo.com.br/site/acessos/login",
                    "base_url": "https://minhaconta2.cielo.com.br",
                }
    return None


def _cielo_browser_profile_dir(company: str = "MVA") -> str:
    root = os.path.join(_runtime_user_dir(), "cielo_browser")
    profile = os.path.join(root, _normalize_ascii_text(company) or "mva")
    os.makedirs(profile, exist_ok=True)
    return profile


def _azulzinha_browser_profile_dir(company: str = "EH") -> str:
    root = os.path.join(_runtime_user_dir(), "azulzinha_browser")
    profile = os.path.join(root, _normalize_ascii_text(company) or "eh")
    os.makedirs(profile, exist_ok=True)
    return profile


def _azulzinha_device_aliases(company: str = "EH") -> list[str]:
    company_norm = _normalize_ascii_text(company)
    if company_norm == "mva":
        return [
            "MVA COMERCIO",
            "MVA COMÉRCIO",
            "MVA FINANCEIRO",
            "MVA 01",
            "MVA",
        ]
    return [
        "EH FINANCEIRO",
        "EH 01",
        "ELETRONICA HORIZONTE",
        "HORIZONTE",
        "EH VAL",
        "MARIA EDUARDA",
    ]


def _load_gmail_token_credentials() -> tuple[str, str] | None:
    login = str(MINHAS_NOTAS_LOGIN or "").strip()
    password = str(MINHAS_NOTAS_PASSWORD or "").strip()
    if login and password:
        return login, password

    for filename in ("credenciais.txt", "credencias.txt"):
        caminho = _runtime_file_path(filename)
        if not caminho.is_file():
            continue
        try:
            linhas = [linha.strip() for linha in caminho.read_text(encoding="utf-8", errors="ignore").splitlines() if linha.strip()]
        except OSError:
            continue
        for idx, linha in enumerate(linhas):
            if "@" in linha and idx + 1 < len(linhas):
                return linha, linhas[idx + 1]
    return None


def _gmail_oauth_token_path() -> Path:
    return _runtime_file_path("gmail_oauth_token.json", prefer_existing=True)


def get_gmail_oauth_status() -> dict[str, object]:
    client_path = _runtime_file_path("gmail_oauth_client.json", prefer_existing=True)
    token_path = _gmail_oauth_token_path()
    if not _load_gmail_oauth_client_credentials():
        return {
            "ok": False,
            "needs_auth": True,
            "status": "missing_client",
            "title": "Gmail não configurado",
            "message": "O arquivo gmail_oauth_client.json não foi encontrado ou está inválido.",
            "client_path": str(client_path),
            "token_path": str(token_path),
        }
    if not token_path.is_file():
        return {
            "ok": False,
            "needs_auth": True,
            "status": "missing_token",
            "title": "Gmail não autenticado",
            "message": "O arquivo gmail_oauth_token.json ainda não existe. Autorize o Gmail antes de gerar relatórios que precisam ler tokens por e-mail.",
            "client_path": str(client_path),
            "token_path": str(token_path),
        }

    try:
        from google.oauth2.credentials import Credentials
        from google.auth.transport.requests import Request

        creds = Credentials.from_authorized_user_file(
            str(token_path),
            scopes=["https://www.googleapis.com/auth/gmail.readonly"],
        )
    except Exception as exc:
        return {
            "ok": False,
            "needs_auth": True,
            "status": "invalid_token",
            "title": "Gmail precisa de nova autenticação",
            "message": f"O token OAuth do Gmail está inválido: {exc}",
            "client_path": str(client_path),
            "token_path": str(token_path),
        }

    if creds.valid:
        return {
            "ok": True,
            "needs_auth": False,
            "status": "valid",
            "title": "Gmail autenticado",
            "message": "O token OAuth do Gmail está válido.",
            "client_path": str(client_path),
            "token_path": str(token_path),
        }
    if creds.expired and getattr(creds, "refresh_token", None):
        try:
            creds.refresh(Request())
            token_path.write_text(creds.to_json(), encoding="utf-8")
            return {
                "ok": True,
                "needs_auth": False,
                "status": "valid",
                "title": "Gmail autenticado",
                "message": "O token OAuth do Gmail foi renovado automaticamente.",
                "client_path": str(client_path),
                "token_path": str(token_path),
            }
        except Exception as exc:
            return {
                "ok": False,
                "needs_auth": True,
                "status": "refresh_failed",
                "title": "Gmail precisa de nova autenticação",
                "message": f"O token OAuth do Gmail expirou e não pôde ser renovado automaticamente: {exc}",
                "client_path": str(client_path),
                "token_path": str(token_path),
            }
    return {
        "ok": False,
        "needs_auth": True,
        "status": "needs_auth",
        "title": "Gmail precisa de nova autenticação",
        "message": "O token OAuth do Gmail expirou ou não possui permissão de renovação automática.",
        "client_path": str(client_path),
        "token_path": str(token_path),
    }


def _load_gmail_oauth_client_credentials() -> tuple[str, str] | None:
    client_id = str(GMAIL_OAUTH_CLIENT_ID or "").strip()
    client_secret = str(GMAIL_OAUTH_CLIENT_SECRET or "").strip()
    if client_id and client_secret:
        return client_id, client_secret

    env_client_id = str(os.environ.get("GMAIL_OAUTH_CLIENT_ID") or "").strip()
    env_client_secret = str(os.environ.get("GMAIL_OAUTH_CLIENT_SECRET") or "").strip()
    if env_client_id and env_client_secret:
        return env_client_id, env_client_secret

    config_path = _runtime_file_path("gmail_oauth_client.json", prefer_existing=True)
    if not config_path.is_file():
        return None

    try:
        payload = json.loads(config_path.read_text(encoding="utf-8-sig"))
    except Exception:
        return None

    if isinstance(payload, dict):
        for candidate in (payload, payload.get("installed"), payload.get("web")):
            if not isinstance(candidate, dict):
                continue
            file_client_id = str(candidate.get("client_id") or "").strip()
            file_client_secret = str(candidate.get("client_secret") or "").strip()
            if file_client_id and file_client_secret:
                return file_client_id, file_client_secret
    return None


def _raise_if_oauth_cancelled(cancel_event: threading.Event | None) -> None:
    if cancel_event is not None and cancel_event.is_set():
        raise RuntimeError("__cancelled__")


def _sleep_with_cancel(seconds: float, cancel_event: threading.Event | None = None) -> None:
    deadline = time.time() + max(0.0, float(seconds or 0.0))
    while time.time() < deadline:
        _raise_if_oauth_cancelled(cancel_event)
        time.sleep(min(0.25, max(0.0, deadline - time.time())))
    _raise_if_oauth_cancelled(cancel_event)


def _run_gmail_oauth_local_server(flow, *, on_status=None, cancel_event: threading.Event | None = None):
    import webbrowser
    import wsgiref.simple_server

    from google_auth_oauthlib.flow import _RedirectWSGIApp, _WSGIRequestHandler

    _raise_if_oauth_cancelled(cancel_event)

    success_message = "Autorizacao do Gmail concluida. Pode voltar ao aplicativo."
    wsgi_app = _RedirectWSGIApp(success_message)
    wsgiref.simple_server.WSGIServer.allow_reuse_address = False
    local_server = wsgiref.simple_server.make_server(
        "127.0.0.1",
        0,
        wsgi_app,
        handler_class=_WSGIRequestHandler,
    )

    try:
        flow.redirect_uri = f"http://127.0.0.1:{local_server.server_port}/"
        auth_url, _ = flow.authorization_url()
        try:
            webbrowser.get().open(auth_url, new=1, autoraise=True)
            _emit_pix_status(
                on_status,
                "Se o Gmail abrir no perfil errado, copie o link de autorizacao para o perfil correto ou clique em Cancelar.",
            )
        except Exception:
            _emit_pix_status(on_status, "Nao foi possivel abrir o navegador automaticamente. Copie o link de autorizacao abaixo:")
            _emit_pix_status(on_status, auth_url)

        local_server.timeout = 0.5
        deadline = time.time() + 180.0
        while not wsgi_app.last_request_uri:
            _raise_if_oauth_cancelled(cancel_event)
            if time.time() >= deadline:
                raise TimeoutError("Autorizacao do Gmail expirou. Tente novamente e selecione o perfil correto.")
            local_server.handle_request()

        _raise_if_oauth_cancelled(cancel_event)
        authorization_response = wsgi_app.last_request_uri.replace("http", "https", 1)
        flow.fetch_token(authorization_response=authorization_response)
        _raise_if_oauth_cancelled(cancel_event)
        return flow.credentials
    finally:
        local_server.server_close()


def _get_gmail_api_credentials(
    on_status=None,
    cancel_event: threading.Event | None = None,
    *,
    allow_interactive_auth: bool = True,
):
    _raise_if_oauth_cancelled(cancel_event)
    client_credentials = _load_gmail_oauth_client_credentials()
    if not client_credentials:
        return None
    client_id, client_secret = client_credentials

    try:
        from google.oauth2.credentials import Credentials
        from google_auth_oauthlib.flow import InstalledAppFlow
        from google.auth.transport.requests import Request
    except Exception as exc:
        _emit_pix_status(on_status, f"Bibliotecas OAuth do Google indisponiveis: {exc}")
        return None

    scopes = ["https://www.googleapis.com/auth/gmail.readonly"]
    token_path = _gmail_oauth_token_path()
    creds = None
    if token_path.is_file():
        try:
            creds = Credentials.from_authorized_user_file(str(token_path), scopes=scopes)
        except Exception:
            creds = None

    if creds and creds.expired and creds.refresh_token:
        try:
            _raise_if_oauth_cancelled(cancel_event)
            creds.refresh(Request())
            token_path.write_text(creds.to_json(), encoding="utf-8")
        except Exception:
            creds = None

    if creds and creds.valid:
        return creds

    if not allow_interactive_auth:
        _emit_pix_status(
            on_status,
            "Gmail não autenticado. Autorize o Gmail antes de gerar relatórios que precisam ler códigos por e-mail.",
        )
        return None

    _emit_pix_status(on_status, "Autorizando leitura do Gmail no navegador...")
    flow = InstalledAppFlow.from_client_config(
        {
            "installed": {
                "client_id": client_id,
                "client_secret": client_secret,
                "auth_uri": "https://accounts.google.com/o/oauth2/auth",
                "token_uri": "https://oauth2.googleapis.com/token",
                "redirect_uris": ["http://localhost"],
            }
        },
        scopes=scopes,
    )
    creds = _run_gmail_oauth_local_server(flow, on_status=on_status, cancel_event=cancel_event)
    if creds:
        token_path.write_text(creds.to_json(), encoding="utf-8")
    return creds


def _extract_gmail_api_body(payload: dict) -> str:
    chunks = []

    def _walk(part: dict) -> None:
        mime = str(part.get("mimeType") or "")
        body = part.get("body") or {}
        data = body.get("data")
        if mime in {"text/plain", "text/html"} and data:
            try:
                chunks.append(base64.urlsafe_b64decode(data + "===").decode("utf-8", errors="ignore"))
            except Exception:
                pass
        for child in part.get("parts") or []:
            _walk(child)

    _walk(payload or {})
    return "\n".join(chunks)


def _extract_fiserv_email_token(text: str) -> str | None:
    texto = corrigir_texto(str(text or ""))
    texto_sem_style = re.sub(r"(?is)<style\b.*?>.*?</style>", " ", texto)
    texto_sem_script = re.sub(r"(?is)<script\b.*?>.*?</script>", " ", texto_sem_style)
    texto_visivel = re.sub(r"(?is)<[^>]+>", " ", texto_sem_script)
    texto_visivel = html.unescape(texto_visivel)
    texto_visivel = re.sub(r"\s+", " ", texto_visivel).strip()

    candidatos_prioritarios = []
    candidatos_contexto = []

    for match in re.finditer(r"(?<!\d)(\d{6,8})(?!\d)", texto_visivel):
        inicio = max(0, match.start() - 120)
        fim = min(len(texto_visivel), match.end() + 120)
        contexto = _normalize_ascii_text(texto_visivel[inicio:fim])
        codigo = match.group(1)
        if any(
            frase in contexto
            for frase in (
                "seu codigo de verificacao",
                "codigo de verificacao",
                "codigo enviado",
                "codigo que enviamos",
            )
        ):
            candidatos_prioritarios.append(codigo)
            continue
        if any(palavra in contexto for palavra in ("token", "codigo", "verificacao", "validacao", "acesso", "seguranca")):
            candidatos_contexto.append(codigo)

    if candidatos_prioritarios:
        return candidatos_prioritarios[0]
    if candidatos_contexto:
        return candidatos_contexto[0]

    match = re.search(r"(?<!\d)(\d{6})(?!\d)", texto_visivel)
    return match.group(1) if match else None


def _is_likely_login_token_email(sender: str, subject: str, body: str) -> bool:
    texto = _normalize_ascii_text("\n".join([str(sender or ""), str(subject or ""), str(body or "")]))
    return any(
        marker in texto
        for marker in (
            "fiserv",
            "codigo de verificacao",
            "codigo de verificação",
            "verificacao de login",
            "verificação de login",
            "validar o login",
            "codigo enviado",
            "seguranca desta conta",
        )
    )


def _extract_cielo_email_token(text: str) -> str | None:
    texto = corrigir_texto(str(text or ""))
    texto = re.sub(r"(?is)<style\b.*?>.*?</style>", " ", texto)
    texto = re.sub(r"(?is)<script\b.*?>.*?</script>", " ", texto)
    texto = re.sub(r"(?is)<[^>]+>", " ", texto)
    texto = html.unescape(texto)
    texto = re.sub(r"\s+", " ", texto).strip()

    candidatos_prioritarios: list[str] = []
    candidatos_contexto: list[str] = []
    for match in re.finditer(r"(?<!\d)(\d{4,8})(?!\d)", texto):
        inicio = max(0, match.start() - 140)
        fim = min(len(texto), match.end() + 140)
        contexto = _normalize_ascii_text(texto[inicio:fim])
        codigo = match.group(1)
        if "cielo" in contexto and any(
            marker in contexto
            for marker in ("codigo", "token", "verificacao", "validacao", "autenticacao", "seguranca", "acesso")
        ):
            candidatos_prioritarios.append(codigo)
            continue
        if any(marker in contexto for marker in ("codigo", "token", "verificacao", "validacao", "autenticacao")):
            candidatos_contexto.append(codigo)

    if candidatos_prioritarios:
        return candidatos_prioritarios[0]
    if candidatos_contexto:
        return candidatos_contexto[0]
    return None


def _is_likely_cielo_token_email(sender: str, subject: str, body: str) -> bool:
    texto = _normalize_ascii_text("\n".join([str(sender or ""), str(subject or ""), str(body or "")]))
    return "cielo" in texto and any(
        marker in texto
        for marker in (
            "codigo",
            "token",
            "verificacao",
            "validacao",
            "autenticacao",
            "seguranca",
            "acesso",
            "minha conta",
        )
    )


_CIELO_GMAIL_FALLBACK_GRACE_SECONDS = 180.0


def _cielo_gmail_session(on_status=None, cancel_event: threading.Event | None = None) -> requests.Session:
    creds = _get_gmail_api_credentials(
        on_status=on_status,
        cancel_event=cancel_event,
        allow_interactive_auth=False,
    )
    if not creds:
        raise RuntimeError("Credenciais OAuth do Gmail indisponiveis.")
    session = requests.Session()
    session.headers.update({"Authorization": f"Bearer {creds.token}"})
    return session


def _refresh_cielo_gmail_session_if_needed(
    session: requests.Session,
    response,
    on_status=None,
    cancel_event: threading.Event | None = None,
) -> bool:
    if response.status_code != 401:
        return False
    try:
        creds = _get_gmail_api_credentials(
            on_status=on_status,
            cancel_event=cancel_event,
            allow_interactive_auth=False,
        )
        if not creds or not getattr(creds, "refresh_token", None):
            return False
        from google.auth.transport.requests import Request

        creds.refresh(Request())
        _gmail_oauth_token_path().write_text(creds.to_json(), encoding="utf-8")
        session.headers.update({"Authorization": f"Bearer {creds.token}"})
        return True
    except Exception:
        return False


def _list_recent_cielo_token_message_ids(on_status=None, max_results: int = 20) -> set[str]:
    try:
        session = _cielo_gmail_session(on_status=on_status)
        response = session.get(
            "https://gmail.googleapis.com/gmail/v1/users/me/messages",
            params={
                "q": "cielo newer_than:7d",
                "maxResults": max_results,
                "includeSpamTrash": "false",
                "fields": "messages/id,resultSizeEstimate",
            },
            timeout=15.0,
        )
        if _refresh_cielo_gmail_session_if_needed(session, response, on_status=on_status):
            response = session.get(
                "https://gmail.googleapis.com/gmail/v1/users/me/messages",
                params={
                    "q": "cielo newer_than:7d",
                    "maxResults": max_results,
                    "includeSpamTrash": "false",
                    "fields": "messages/id,resultSizeEstimate",
                },
                timeout=15.0,
            )
        response.raise_for_status()
        return {
            str(item.get("id") or "").strip()
            for item in ((response.json() or {}).get("messages") or [])
            if str(item.get("id") or "").strip()
        }
    except Exception:
        return set()


def _fetch_cielo_token_from_gmail(
    timeout: float = 90.0,
    on_status=None,
    ignored_tokens: set[str] | None = None,
    ignored_message_ids: set[str] | None = None,
    min_internal_ts: float | None = None,
    debug_info: dict | None = None,
    cancel_event: threading.Event | None = None,
) -> str | None:
    _raise_if_oauth_cancelled(cancel_event)
    ignored_tokens_normalized = {
        str(token or "").strip()
        for token in (ignored_tokens or set())
        if str(token or "").strip()
    }
    ignored_message_ids_normalized = {
        str(message_id or "").strip()
        for message_id in (ignored_message_ids or set())
        if str(message_id or "").strip()
    }
    deadline = time.time() + timeout
    last_error = None
    try:
        session = _cielo_gmail_session(on_status=on_status, cancel_event=cancel_event)
        while time.time() < deadline:
            _raise_if_oauth_cancelled(cancel_event)
            _emit_pix_status(on_status, "Consultando codigo recente da Cielo no Gmail...")
            response = session.get(
                "https://gmail.googleapis.com/gmail/v1/users/me/messages",
                params={
                    "q": "cielo newer_than:7d",
                    "maxResults": 30,
                    "includeSpamTrash": "true",
                    "fields": "messages/id,resultSizeEstimate",
                },
                timeout=15.0,
            )
            if _refresh_cielo_gmail_session_if_needed(session, response, on_status=on_status, cancel_event=cancel_event):
                continue
            response.raise_for_status()
            messages = (response.json() or {}).get("messages") or []
            candidates: list[tuple[float, str, str, str]] = []
            for item in messages:
                _raise_if_oauth_cancelled(cancel_event)
                msg_id = str(item.get("id") or "").strip()
                if not msg_id:
                    continue
                msg_resp = session.get(
                    f"https://gmail.googleapis.com/gmail/v1/users/me/messages/{msg_id}",
                    params={
                        "format": "metadata",
                        "metadataHeaders": ["Subject", "From"],
                        "fields": "id,internalDate,payload/headers",
                    },
                    timeout=15.0,
                )
                msg_resp.raise_for_status()
                payload = msg_resp.json() or {}
                internal_date_ms = float(payload.get("internalDate") or 0.0)
                if msg_id in ignored_message_ids_normalized and min_internal_ts is None:
                    continue
                headers = payload.get("payload", {}).get("headers") or []
                subject = next((str(h.get("value") or "") for h in headers if str(h.get("name") or "").lower() == "subject"), "")
                sender = next((str(h.get("value") or "") for h in headers if str(h.get("name") or "").lower() == "from"), "")
                candidates.append((internal_date_ms, msg_id, subject, sender))
            if debug_info is not None:
                debug_info["candidate_count"] = len(
                    [
                        item
                        for item in candidates
                        if min_internal_ts is None or ((float(item[0] or 0.0) / 1000.0) >= float(min_internal_ts))
                    ]
                )
                debug_info["all_candidate_count"] = len(candidates)
                debug_info["min_internal_ts"] = min_internal_ts
            candidates.sort(key=lambda item: (item[0], item[1]), reverse=True)
            candidate_sets: list[tuple[str, list[tuple[float, str, str, str]]]] = [
                (
                    "timestamp",
                    [
                        item
                        for item in candidates
                        if min_internal_ts is None or ((float(item[0] or 0.0) / 1000.0) >= float(min_internal_ts))
                    ],
                )
            ]
            if min_internal_ts is not None:
                # Cielo can issue the token before the local automation records the
                # next checkpoint. Only accept a slightly older e-mail, never an
                # unrelated token from a previous login attempt.
                fallback_cutoff_ms = max(0.0, (float(min_internal_ts) - _CIELO_GMAIL_FALLBACK_GRACE_SECONDS) * 1000.0)
                fallback_candidates = [
                    item
                    for item in candidates
                    if float(item[0] or 0.0) >= fallback_cutoff_ms
                ]
                if debug_info is not None:
                    debug_info["fallback_cutoff_ts"] = datetime.fromtimestamp(fallback_cutoff_ms / 1000.0).isoformat(timespec="seconds") if fallback_cutoff_ms else ""
                    debug_info["fallback_candidate_count"] = len(fallback_candidates)
                if fallback_candidates:
                    candidate_sets.append(("latest_recent", fallback_candidates))
            for lookup_mode, active_candidates in candidate_sets:
                for _msg_ts, msg_id, subject, sender in active_candidates:
                    _raise_if_oauth_cancelled(cancel_event)
                    msg_resp = session.get(
                        f"https://gmail.googleapis.com/gmail/v1/users/me/messages/{msg_id}",
                        params={"format": "full", "fields": "id,internalDate,payload,snippet"},
                        timeout=15.0,
                    )
                    msg_resp.raise_for_status()
                    payload = msg_resp.json() or {}
                    body = _extract_gmail_api_body(payload.get("payload") or {})
                    snippet = str(payload.get("snippet") or "").strip()
                    searchable_text = f"{body}\n{snippet}".strip()
                    token = _extract_cielo_email_token(f"{subject}\n{searchable_text}")
                    if token and token not in ignored_tokens_normalized and _is_likely_cielo_token_email(sender, subject, searchable_text):
                        if debug_info is not None:
                            internal_date_ms = float(payload.get("internalDate") or 0.0)
                            msg_ts = internal_date_ms / 1000.0 if internal_date_ms else 0.0
                            debug_info["selected_message_id_tail"] = msg_id[-8:]
                            debug_info["selected_message_ts"] = datetime.fromtimestamp(msg_ts).isoformat(timespec="seconds") if msg_ts else ""
                            debug_info["selected_sender"] = sender
                            debug_info["selected_subject"] = subject
                            debug_info["selected_lookup_mode"] = lookup_mode
                        _emit_pix_status(on_status, "Codigo da Cielo encontrado no Gmail.")
                        return token
            _sleep_with_cancel(5.0, cancel_event)
    except RuntimeError as exc:
        if str(exc).strip() == "__cancelled__":
            raise
        last_error = exc
    except Exception as exc:
        last_error = exc

    if last_error:
        _emit_pix_status(on_status, f"Nao foi possivel ler o codigo da Cielo no Gmail: {last_error}")
    return None


def _write_gmail_body_debug(
    entries: list[dict[str, object]],
    *,
    title: str | None = None,
    summary_lines: list[str] | None = None,
    note: str | None = None,
    extra_lines: list[str] | None = None,
) -> None:
    if not GMAIL_BODY_DEBUG_ENABLED:
        try:
            (Path(_runtime_user_dir()) / "body_email.txt").unlink(missing_ok=True)
        except Exception:
            pass
        return
    try:
        linhas = []
        if title:
            linhas.extend([title, "=" * 100, ""])
        if extra_lines:
            linhas.extend([str(item) for item in extra_lines if str(item or "").strip()])
            if linhas and linhas[-1] != "":
                linhas.append("")
        if summary_lines:
            linhas.append("Últimos e-mails identificados:")
            for line in summary_lines[:8]:
                linhas.append(f"- {line}")
            linhas.append("")
        if note:
            linhas.append(note)
            linhas.append("")
        for idx, entry in enumerate(entries[:8], start=1):
            msg_ts = float(entry.get("timestamp") or 0.0)
            horario = "--:--:--"
            if msg_ts:
                try:
                    horario = datetime.fromtimestamp(msg_ts).strftime("%d/%m/%Y %H:%M:%S")
                except Exception:
                    pass
            remetente = corrigir_texto(str(entry.get("sender") or "Remetente desconhecido"))
            assunto = corrigir_texto(str(entry.get("subject") or "Sem assunto"))
            msg_id = str(entry.get("message_id") or "").strip()
            token = str(entry.get("token") or "").strip() or "(nenhum)"
            decisao = corrigir_texto(str(entry.get("decision") or "sem decisao"))
            snippet = corrigir_texto(str(entry.get("snippet") or "")).strip()
            corpo = corrigir_texto(str(entry.get("body") or "")).strip()
            linhas.extend(
                [
                    "=" * 100,
                    f"Email #{idx}",
                    f"Horário: {horario}",
                    f"Message ID: {msg_id or '(desconhecido)'}",
                    f"Remetente: {remetente}",
                    f"Assunto: {assunto}",
                    f"Token extraído: {token}",
                    f"Decisão do app: {decisao}",
                    "",
                    "Snippet retornado pela API:",
                    snippet or "(vazio)",
                    "",
                    "Corpo visível analisado pelo parser:",
                    corpo or "(vazio)",
                    "",
                ]
            )
        destino = Path(_runtime_user_dir()) / "body_email.txt"
        destino.write_text("\n".join(linhas), encoding="utf-8")
    except Exception:
        pass


def _fetch_fiserv_token_from_gmail(
    sent_after: float,
    timeout: float = 90.0,
    on_status=None,
    ignored_tokens: set[str] | None = None,
    allow_recent_fallback: bool = True,
    cancel_event: threading.Event | None = None,
) -> str | None:
    _raise_if_oauth_cancelled(cancel_event)
    credenciais = _load_gmail_token_credentials()
    if not credenciais:
        return None

    ignored_tokens_normalized = {
        str(token or "").strip()
        for token in (ignored_tokens or set())
        if str(token or "").strip()
    }

    _write_gmail_body_debug(
        [],
        title="Debug do Gmail - nova tentativa",
        note="Aguardando leitura dos últimos e-mails pelo aplicativo.",
    )

    deadline = time.time() + timeout
    last_error = None
    fallback_recent_token: tuple[float, str] | None = None
    checked_full_ids: set[str] = set()
    gmail_query = "from:no-reply@fiserv.com newer_than:7d"
    gmail_debug_limit = 8

    def _format_candidate_summary(msg_ts: float, sender: str, subject: str) -> str:
        horario = "--:--:--"
        if msg_ts:
            try:
                horario = datetime.fromtimestamp(msg_ts).strftime("%H:%M:%S")
            except Exception:
                pass
        remetente = (sender or "Remetente desconhecido").strip()
        if len(remetente) > 45:
            remetente = remetente[:42] + "..."
        assunto = (subject or "Sem assunto").strip()
        if len(assunto) > 55:
            assunto = assunto[:52] + "..."
        return f"{horario} | {remetente} | {assunto}"

    def _compute_poll_interval() -> float:
        remaining = max(0.0, deadline - time.time())
        elapsed = max(0.0, timeout - remaining)
        if elapsed < 30.0:
            return 3.0
        if elapsed < 90.0:
            return 5.0
        return 10.0

    try:
        creds = _get_gmail_api_credentials(
            on_status=on_status,
            cancel_event=cancel_event,
            allow_interactive_auth=False,
        )
        if not creds:
            raise RuntimeError("Credenciais OAuth do Gmail indisponíveis.")
        session = requests.Session()
        session.headers.update({"Authorization": f"Bearer {creds.token}"})
        while time.time() < deadline:
            _raise_if_oauth_cancelled(cancel_event)
            _emit_pix_status(on_status, "Consultando e-mails recentes no Gmail via API...")
            response = session.get(
                "https://gmail.googleapis.com/gmail/v1/users/me/messages",
                params={
                    "q": gmail_query,
                    "maxResults": gmail_debug_limit,
                    "includeSpamTrash": "false",
                    "fields": "messages/id,resultSizeEstimate",
                },
                timeout=15.0,
            )
            if response.status_code == 401 and getattr(creds, "refresh_token", None):
                try:
                    from google.auth.transport.requests import Request
                    _raise_if_oauth_cancelled(cancel_event)
                    creds.refresh(Request())
                    _gmail_oauth_token_path().write_text(creds.to_json(), encoding="utf-8")
                    session.headers.update({"Authorization": f"Bearer {creds.token}"})
                    _emit_pix_status(on_status, "Token OAuth do Gmail renovado. Repetindo consulta...")
                    continue
                except Exception:
                    pass
            response.raise_for_status()
            messages = (response.json() or {}).get("messages") or []
            newest_match: tuple[float, str] | None = None
            ignored_marker_seen = False
            ignored_rejected_logged = False
            older_than_rejected_logged = False
            candidates: list[tuple[float, str, str, str]] = []
            api_debug_entries: list[dict[str, object]] = []
            debug_context_lines = [
                f"Consulta Gmail usada: {gmail_query}",
                f"Fallback recente permitido nesta tentativa: {'sim' if allow_recent_fallback else 'não'}",
                (
                    "Tokens já descartados nesta rodada: "
                    + (", ".join(sorted(ignored_tokens_normalized)) if ignored_tokens_normalized else "(nenhum)")
                ),
                "",
            ]
            for item in messages:
                _raise_if_oauth_cancelled(cancel_event)
                msg_id = str(item.get("id") or "").strip()
                if not msg_id:
                    continue
                msg_resp = session.get(
                    f"https://gmail.googleapis.com/gmail/v1/users/me/messages/{msg_id}",
                    params={
                        "format": "metadata",
                        "metadataHeaders": ["Subject", "From"],
                        "fields": "id,internalDate,payload/headers",
                    },
                    timeout=15.0,
                )
                msg_resp.raise_for_status()
                payload = msg_resp.json() or {}
                internal_date_ms = float(payload.get("internalDate") or 0.0)
                msg_ts = internal_date_ms / 1000.0 if internal_date_ms else 0.0
                headers = payload.get("payload", {}).get("headers") or []
                subject = next((str(h.get("value") or "") for h in headers if str(h.get("name") or "").lower() == "subject"), "")
                sender = next((str(h.get("value") or "") for h in headers if str(h.get("name") or "").lower() == "from"), "")
                candidates.append((msg_ts, msg_id, subject, sender))
            candidates.sort(key=lambda item: item[0], reverse=True)
            candidate_summaries = [
                _format_candidate_summary(msg_ts, sender, subject)
                for msg_ts, _msg_id, subject, sender in candidates[:gmail_debug_limit]
            ]
            for msg_ts, msg_id, subject, sender in candidates[:gmail_debug_limit]:
                _raise_if_oauth_cancelled(cancel_event)
                if msg_id in checked_full_ids:
                    continue
                msg_resp = session.get(
                    f"https://gmail.googleapis.com/gmail/v1/users/me/messages/{msg_id}",
                    params={"format": "full", "fields": "id,internalDate,payload,snippet"},
                    timeout=15.0,
                )
                msg_resp.raise_for_status()
                payload = msg_resp.json() or {}
                checked_full_ids.add(msg_id)
                body = _extract_gmail_api_body(payload.get("payload") or {})
                snippet = str(payload.get("snippet") or "").strip()
                searchable_text = body
                if snippet:
                    searchable_text = f"{searchable_text}\n{snippet}".strip() if searchable_text else snippet
                token = _extract_fiserv_email_token(f"{subject}\n{searchable_text}")
                api_debug_entries.append(
                    {
                        "timestamp": msg_ts,
                        "message_id": msg_id,
                        "sender": sender,
                        "subject": subject,
                        "snippet": snippet,
                        "body": searchable_text,
                        "token": token or "",
                        "decision": "sem_token",
                    }
                )
                if token and _is_likely_login_token_email(sender, subject, searchable_text):
                    if token in ignored_tokens_normalized:
                        ignored_marker_seen = True
                        api_debug_entries[-1]["decision"] = "token_ja_rejeitado"
                        if not ignored_rejected_logged:
                            _emit_pix_status(
                                on_status,
                                "Codigo de login ja rejeitado anteriormente; aguardando um novo e-mail.",
                            )
                            ignored_rejected_logged = True
                        continue
                    if not fallback_recent_token or msg_ts > fallback_recent_token[0]:
                        fallback_recent_token = (msg_ts, token)
                    if ignored_marker_seen and ignored_tokens_normalized and not allow_recent_fallback:
                        api_debug_entries[-1]["decision"] = "token_mais_antigo_que_rejeitado"
                        if not older_than_rejected_logged:
                            _emit_pix_status(
                                on_status,
                                "O código disponível é mais antigo que o rejeitado; aguardando um e-mail mais novo.",
                            )
                            older_than_rejected_logged = True
                        continue
                    if not newest_match or msg_ts > newest_match[0]:
                        newest_match = (msg_ts, token)
                    api_debug_entries[-1]["decision"] = "token_pronto_para_validacao"
                    continue
                if token:
                    api_debug_entries[-1]["decision"] = "token_extraido_sem_confirmacao_de_contexto"
                else:
                    api_debug_entries[-1]["decision"] = "nenhum_token_extraido"
            _write_gmail_body_debug(
                api_debug_entries,
                title="Debug do Gmail via API",
                summary_lines=candidate_summaries,
                extra_lines=debug_context_lines,
                note=(
                    None
                    if api_debug_entries
                    else "Nenhum corpo de e-mail foi lido nesta tentativa da API."
                ),
            )
            if newest_match:
                _emit_pix_status(on_status, f"Codigo de login pronto para validacao na Caixa: {newest_match[1]}.")
                return newest_match[1]
            wait_seconds = _compute_poll_interval()
            _emit_pix_status(
                on_status,
                f"Nenhum token novo ainda. Nova tentativa em {int(wait_seconds)}s.",
            )
            _sleep_with_cancel(wait_seconds, cancel_event)
    except RuntimeError as exc:
        if str(exc).strip() == "__cancelled__":
            raise
        last_error = exc
        _emit_pix_status(on_status, f"Não foi possível ler o token no Gmail via OAuth: {exc}")
    except Exception as exc:
        last_error = exc
        _emit_pix_status(on_status, f"Não foi possível ler o token no Gmail via OAuth: {exc}")

    import email
    import imaplib
    from email.header import decode_header
    from email.utils import parsedate_to_datetime

    login, password = credenciais

    def _decode_mime(value: str) -> str:
        partes = []
        for chunk, charset in decode_header(value or ""):
            if isinstance(chunk, bytes):
                partes.append(chunk.decode(charset or "utf-8", errors="ignore"))
            else:
                partes.append(str(chunk or ""))
        return "".join(partes)

    def _message_text(message) -> str:
        chunks = []
        if message.is_multipart():
            for part in message.walk():
                content_type = part.get_content_type()
                disposition = str(part.get("Content-Disposition") or "").lower()
                if "attachment" in disposition or content_type not in {"text/plain", "text/html"}:
                    continue
                payload = part.get_payload(decode=True)
                if payload is None:
                    continue
                chunks.append(payload.decode(part.get_content_charset() or "utf-8", errors="ignore"))
        else:
            payload = message.get_payload(decode=True)
            if payload is not None:
                chunks.append(payload.decode(message.get_content_charset() or "utf-8", errors="ignore"))
        return "\n".join(chunks)

    while time.time() < deadline:
        try:
            _emit_pix_status(on_status, "Lendo e-mails recentes no Gmail via IMAP...")
            with imaplib.IMAP4_SSL("imap.gmail.com", 993) as mail:
                mail.login(login, password)
                mail.select("INBOX")
                status, data = mail.uid(
                    "search",
                    None,
                    "X-GM-RAW",
                    '"in:inbox"',
                )
                if status != "OK":
                    status, data = mail.uid("search", None, "ALL")
                ids = (data[0] or b"").split()[-20:]
                newest_match: tuple[float, str] | None = None
                ignored_marker_seen = False
                ignored_rejected_logged = False
                older_than_rejected_logged = False
                imap_candidates: list[tuple[float, str, str]] = []
                imap_debug_entries: list[dict[str, object]] = []
                for uid in reversed(ids):
                    status, msg_data = mail.uid("fetch", uid, "(RFC822)")
                    if status != "OK" or not msg_data:
                        continue
                    raw = next((item[1] for item in msg_data if isinstance(item, tuple) and len(item) > 1), None)
                    if not raw:
                        continue
                    msg = email.message_from_bytes(raw)
                    try:
                        msg_dt = parsedate_to_datetime(msg.get("Date") or "")
                        msg_ts = msg_dt.timestamp()
                    except Exception:
                        msg_ts = 0.0
                    remetente = _normalize_ascii_text(msg.get("From") or "")
                    assunto = _decode_mime(msg.get("Subject") or "")
                    corpo = _message_text(msg)
                    imap_candidates.append((msg_ts, msg.get("From") or "", assunto))
                    imap_debug_entries.append(
                        {
                            "timestamp": msg_ts,
                            "sender": msg.get("From") or "",
                            "subject": assunto,
                            "body": corpo,
                        }
                    )
                    token = _extract_fiserv_email_token(f"{assunto}\n{corpo}")
                    if token and _is_likely_login_token_email(remetente, assunto, corpo):
                        if token in ignored_tokens_normalized:
                            ignored_marker_seen = True
                            if not ignored_rejected_logged:
                                _emit_pix_status(
                                    on_status,
                                    "O token retornado via IMAP já foi descartado; aguardando um novo código.",
                                )
                                ignored_rejected_logged = True
                            continue
                        if not fallback_recent_token or msg_ts > fallback_recent_token[0]:
                            fallback_recent_token = (msg_ts, token)
                        if ignored_marker_seen and ignored_tokens_normalized and not allow_recent_fallback:
                            if not older_than_rejected_logged:
                                _emit_pix_status(
                                    on_status,
                                    "O código encontrado via IMAP é mais antigo que o rejeitado; aguardando um e-mail mais novo.",
                                )
                                older_than_rejected_logged = True
                            continue
                        if not newest_match or msg_ts > newest_match[0]:
                            newest_match = (msg_ts, token)
                        continue
                        if not fallback_recent_token or msg_ts > fallback_recent_token[0]:
                            fallback_recent_token = (msg_ts, token)
                        if not newest_match or msg_ts > newest_match[0]:
                            newest_match = (msg_ts, token)
                        _emit_pix_status(
                            on_status,
                            f"Token compatível com login encontrado via IMAP ({assunto_resumido}).",
                        )
                _write_gmail_body_debug(
                    imap_debug_entries,
                    title="Debug do Gmail via IMAP",
                    summary_lines=[
                        _format_candidate_summary(msg_ts, sender, subject)
                        for msg_ts, sender, subject in imap_candidates[:5]
                    ],
                    note=(
                        None
                        if imap_debug_entries
                        else "Nenhum corpo de e-mail foi lido nesta tentativa do IMAP."
                    ),
                )
                if newest_match:
                    _emit_pix_status(on_status, f"Codigo de login via IMAP pronto para validacao na Caixa: {newest_match[1]}.")
                    return newest_match[1]
        except Exception as exc:
            last_error = exc
        wait_seconds = _compute_poll_interval()
        _emit_pix_status(
            on_status,
            f"IMAP ainda sem token novo. Nova tentativa em {int(wait_seconds)}s.",
        )
        time.sleep(wait_seconds)

    if fallback_recent_token and not allow_recent_fallback:
        _emit_pix_status(
            on_status,
            "Nenhum token novo chegou a tempo; códigos antigos não serão reutilizados nesta tentativa.",
        )
        fallback_recent_token = None

    if fallback_recent_token:
        _emit_pix_status(on_status, "Nenhum e-mail novo da Fiserv chegou a tempo; reutilizando o código mais recente do Gmail.")
        return fallback_recent_token[1]

    if last_error:
        _emit_pix_status(on_status, f"Falha final ao ler token no Gmail: {last_error}")
    return None


def _wait_for_downloaded_report(
    download_dir: str,
    data_br: str,
    kind: str,
    started_at: float,
    timeout: float = 90.0,
) -> str | None:
    def _find_once() -> str | None:
        suffixes = ("*.csv", "*.xlsx", "*.xls", "*.pdf", "*.crdownload")
        primary_dir_key = ""
        try:
            primary_dir_key = str(Path(download_dir).resolve()).casefold()
        except Exception:
            try:
                primary_dir_key = str(Path(download_dir).absolute()).casefold()
            except Exception:
                primary_dir_key = ""
        for directory in _download_watch_dirs(download_dir):
            try:
                directory_key = str(directory.resolve()).casefold()
            except Exception:
                directory_key = str(directory.absolute()).casefold()
            is_primary_download_dir = bool(primary_dir_key and directory_key == primary_dir_key)
            for pattern in suffixes:
                try:
                    candidates = sorted(
                        directory.glob(pattern),
                        key=lambda item: item.stat().st_mtime,
                        reverse=True,
                    )
                except Exception:
                    continue
                for path in candidates:
                    try:
                        effective_suffix = _effective_local_report_suffix(path)
                        if not is_primary_download_dir and path.stat().st_mtime < started_at - 900:
                            continue
                        if effective_suffix not in _LOCAL_REPORT_SUFFIXES or path.name.endswith(".tmp"):
                            continue
                        if effective_suffix == ".csv":
                            text = _read_text_file(path)
                        elif effective_suffix in {".xlsx", ".xls"}:
                            text = _read_excel_text(path)
                        else:
                            text = _read_pdf_text(path)
                        text_norm = _normalize_ascii_text(text)
                        detected_date = _extract_local_report_date_br(text)
                        if detected_date and detected_date != data_br:
                            continue
                        if kind == "pix" and (
                            (effective_suffix == ".csv" and "data da venda" in text_norm and "valor bruto" in text_norm)
                            or (effective_suffix in {".xlsx", ".xls"} and _looks_like_caixa_pix_xlsx(path, data_br, text))
                            or (effective_suffix == ".pdf" and "valor bruto" in text_norm and "pix" in text_norm)
                        ):
                            normalized_path = _finalize_local_report_path(path)
                            if effective_suffix in {".xlsx", ".xls"}:
                                converted = _convert_pix_xlsx_to_csv(normalized_path)
                                return converted or normalized_path
                            return normalized_path
                        if kind == "cartoes" and (
                            _looks_like_caixa_card_report_text(text)
                        ):
                            return _finalize_local_report_path(path)
                    except Exception:
                        continue
        return None

    found = _find_once()
    if found:
        return found
    deadline = time.time() + timeout
    while time.time() < deadline:
        found = _find_once()
        if found:
            return found
        time.sleep(0.6)
    return None


_AZULZINHA_DEBUG_ARTIFACT_PATTERNS = (
    "azulzinha_*.html",
    "azulzinha_*.json",
    "azulzinha_export_payload_*.json",
    "azulzinha_network_candidates_*.json",
    "azulzinha_export_signals_*.json",
    "azulzinha_export_ready_debug_*.html",
    "azulzinha_export_ready_state_*.json",
    "azulzinha_export_popup_*.html",
    "azulzinha_export_state_*.json",
    "azulzinha_export_debug_*.html",
    "azulzinha_sales_entry_debug.html",
    "azulzinha_sales_before_settle.html",
)


def _cleanup_azulzinha_debug_artifacts() -> None:
    base_dir = Path(_active_report_dir())
    visited: set[Path] = set()
    for pattern in _AZULZINHA_DEBUG_ARTIFACT_PATTERNS:
        try:
            matches = list(base_dir.glob(pattern))
        except Exception:
            continue
        for path in matches:
            if path in visited or not path.is_file():
                continue
            visited.add(path)
            try:
                path.unlink()
            except Exception:
                pass


_EH_AUTO_PAYMENT_REPORT_PREFIXES = (
    "relatorio_de_vendas_pix_",
    "historico_simplificado_de_vendas_",
    "cielo_cartoes_",
)
_EH_AUTO_PAYMENT_REPORT_SUFFIXES = (".csv", ".xlsx", ".xls", ".pdf", ".crdownload")
_AUTO_ZWEB_REPORT_PREFIXES = (
    "pedidos_importados_",
    "fechamento_de_caixa_",
    "relatorio_zweb_",
)
_AUTO_ZWEB_REPORT_SUFFIXES = (".html",)
_GENERATED_RUNTIME_DIRS = (
    "azulzinha_browser",
    "cielo_browser",
)


def _is_eh_auto_payment_report_path(path_like: str | os.PathLike | None) -> bool:
    if not path_like:
        return False
    try:
        path = Path(path_like)
    except TypeError:
        return False
    name = path.name.casefold()
    if not any(name.startswith(prefix) for prefix in _EH_AUTO_PAYMENT_REPORT_PREFIXES):
        return False
    if path.suffix.lower() not in _EH_AUTO_PAYMENT_REPORT_SUFFIXES:
        return False
    return "_auto" in path.stem.casefold()


def _is_generated_auto_report_path(path_like: str | os.PathLike | None) -> bool:
    if _is_eh_auto_payment_report_path(path_like):
        return True
    if not path_like:
        return False
    try:
        path = Path(path_like)
    except TypeError:
        return False
    if _is_debug_artifact_name(path.name):
        return True
    name = path.name.casefold()
    if not any(name.startswith(prefix) for prefix in _AUTO_ZWEB_REPORT_PREFIXES):
        return False
    if path.suffix.lower() not in _AUTO_ZWEB_REPORT_SUFFIXES:
        return False
    return "_auto" in path.stem.casefold()


def _cleanup_eh_auto_payment_reports(*paths_like: str | os.PathLike | None) -> None:
    targets: dict[str, Path] = {}
    scan_dirs: dict[str, Path] = {str(Path(_active_report_dir())).casefold(): Path(_active_report_dir())}
    for raw_path in paths_like:
        if not _is_eh_auto_payment_report_path(raw_path):
            continue
        path = Path(str(raw_path))
        scan_dirs[str(path.parent).casefold()] = path.parent
        base_name = path.name[:-11] if path.name.casefold().endswith(".crdownload") else path.name
        for candidate in (path.parent / f"{base_name}.crdownload",):
            if not candidate.is_file():
                continue
            if not _is_eh_auto_payment_report_path(candidate):
                continue
            targets[str(candidate).casefold()] = candidate

    for directory in scan_dirs.values():
        try:
            partials = list(directory.glob("*.crdownload"))
        except Exception:
            continue
        for candidate in partials:
            name = candidate.name.casefold()
            if (
                "relatorio_de_vendas_pix" in name
                or ("historico" in name and "vendas" in name)
                or "cielo_cartoes" in name
            ):
                targets[str(candidate).casefold()] = candidate

    for candidate in targets.values():
        try:
            candidate.unlink()
        except Exception:
            pass


def cleanup_generated_auto_reports(report_dir: str | os.PathLike | None = None) -> None:
    try:
        base_dir = Path(report_dir or _active_report_dir())
    except TypeError:
        return
    if not base_dir.exists() or not base_dir.is_dir():
        return

    try:
        candidates = list(base_dir.iterdir())
    except Exception:
        return

    for candidate in candidates:
        if not candidate.is_file():
            continue
        if not _is_generated_auto_report_path(candidate):
            continue
        if CIELO_DEBUG_LOGS_ENABLED and candidate.name.casefold().startswith("cielo_") and "_debug_" in candidate.name.casefold():
            continue
        try:
            candidate.unlink()
        except Exception:
            pass

    for dirname in _GENERATED_RUNTIME_DIRS:
        generated_dir = base_dir / dirname
        try:
            if generated_dir.is_dir() and generated_dir.resolve().parent == base_dir.resolve():
                shutil.rmtree(generated_dir, ignore_errors=True)
        except Exception:
            pass


def list_generated_auto_reports(report_dir: str | os.PathLike | None = None) -> list[Path]:
    try:
        base_dir = Path(report_dir or _active_report_dir())
    except TypeError:
        return []
    if not base_dir.exists() or not base_dir.is_dir():
        return []

    try:
        candidates = list(base_dir.iterdir())
    except Exception:
        return []

    report_paths: list[Path] = []
    for candidate in candidates:
        if not candidate.is_file():
            continue
        if not _is_generated_auto_report_path(candidate):
            continue
        report_paths.append(candidate)
    return sorted(report_paths, key=lambda item: item.name.casefold())


def baixar_relatorios_caixa_eh_azulzinha(
    data_br: str,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
    need_pix: bool = True,
    need_cartoes: bool = True,
    company: str = "EH",
) -> dict[str, object]:
    cancel_event = cancel_event or threading.Event()
    company_norm = _normalize_ascii_text(company) or "eh"
    company_label = "MVA" if company_norm == "mva" else "EH"

    def _check_cancelled() -> None:
        if cancel_event.is_set():
            raise RuntimeError("__cancelled__")

    if not need_pix and not need_cartoes:
        return {"pix": None, "cartoes": None, "avisos": []}

    credenciais = _load_azulzinha_credentials(company_label)
    if not credenciais:
        return {
            "pix": None,
            "cartoes": None,
            "avisos": [f"As credenciais da Azulzinha/Caixa da {company_label} não foram encontradas no credenciais.txt ou passo-a-passo.txt."],
        }

    navegador = _find_chromium_browser_path()
    if not navegador:
        return {
            "pix": None,
            "cartoes": None,
            "avisos": ["Nenhum navegador Chromium compatível foi encontrado para baixar os relatórios da Azulzinha/Caixa."],
        }

    download_dir = _active_report_dir()
    artifacts_dir = _AutoArtifactDir(download_dir)
    profile_root = _azulzinha_browser_profile_dir(company_label)
    profile_dir = tempfile.mkdtemp(prefix=f"run_{company_norm}_", dir=profile_root)
    browser_download_dir = tempfile.mkdtemp(prefix=f"downloads_{company_norm}_", dir=profile_root)
    _prepare_chromium_profile(profile_dir, browser_download_dir)
    _cleanup_azulzinha_debug_artifacts()
    port = _pick_free_local_port()
    browser_visible_debug = _browser_debug_visible_enabled()
    chrome_args = [
        navegador,
        f"--remote-debugging-port={port}",
        f"--user-data-dir={profile_dir}",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-background-networking",
        "--disable-background-timer-throttling",
        "--disable-backgrounding-occluded-windows",
        "--disable-component-update",
        "--disable-popup-blocking",
        "--disable-notifications",
        "--disable-renderer-backgrounding",
        "--deny-permission-prompts",
        "--disable-save-password-bubble",
        "--disable-features=PasswordManagerOnboarding,AutofillServerCommunication",
        "--window-size=1400,900",
        "--disable-gpu",
        "about:blank",
    ]
    if browser_visible_debug:
        chrome_args.insert(-2, "--window-position=40,40")
    else:
        chrome_args.insert(-2, "--window-position=-32000,0")
        chrome_args.insert(-2, "--start-minimized")

    def _download_start_time() -> float:
        return time.time() - 1.0

    async def _run() -> dict[str, object]:
        import websockets

        _check_cancelled()
        meta = _wait_for_devtools_ready(port)
        ws_url = str(meta.get("webSocketDebuggerUrl") or "").strip()
        if not ws_url:
            raise RuntimeError("Não foi possível conectar ao Chromium para acessar a Azulzinha/Caixa.")

        async with websockets.connect(ws_url, max_size=50_000_000) as conn:
            next_id = 0
            send_lock = asyncio.Lock()
            pending = {}
            event_log: list[dict] = []
            event_cond = asyncio.Condition()

            async def recv_loop():
                while True:
                    _check_cancelled()
                    mensagem = json.loads(await conn.recv())
                    if "id" in mensagem and mensagem["id"] in pending:
                        pending.pop(mensagem["id"]).set_result(mensagem)
                    elif "method" in mensagem:
                        async with event_cond:
                            event_log.append(mensagem)
                            if len(event_log) > 400:
                                del event_log[:200]
                            event_cond.notify_all()

            recv_task = asyncio.create_task(recv_loop())

            async def cdp(method: str, params: dict | None = None, session_id: str | None = None, timeout: float = 60.0):
                nonlocal next_id
                _check_cancelled()
                next_id += 1
                future = asyncio.get_running_loop().create_future()
                pending[next_id] = future
                mensagem = {"id": next_id, "method": method}
                if params:
                    mensagem["params"] = params
                if session_id:
                    mensagem["sessionId"] = session_id
                async with send_lock:
                    await conn.send(json.dumps(mensagem))
                resposta = await asyncio.wait_for(future, timeout)
                if "error" in resposta:
                    raise RuntimeError(resposta["error"])
                return resposta.get("result", {})

            async def eval_js(session_id: str, expression: str, timeout: float = 60.0):
                resposta = await cdp(
                    "Runtime.evaluate",
                    {"expression": expression, "returnByValue": True, "awaitPromise": True},
                    session_id=session_id,
                    timeout=timeout,
                )
                return resposta.get("result", {}).get("value")

            async def wait_for_condition(
                session_id: str,
                expression: str,
                timeout: float = 60.0,
                step: float = 0.5,
                description: str | None = None,
            ):
                deadline = time.time() + timeout
                last_value = None
                while time.time() < deadline:
                    _check_cancelled()
                    try:
                        last_value = await eval_js(session_id, expression, timeout=15.0)
                        if last_value:
                            return last_value
                    except Exception as exc:
                        last_value = str(exc)
                    await asyncio.sleep(step)
                detail = f" :: ultimo retorno={last_value!r}" if last_value not in (None, "") else ""
                if description:
                    raise TimeoutError(f"{description}{detail}")
                raise TimeoutError(f"{expression}{detail}")

            async def wait_for_event(
                predicate,
                timeout: float = 30.0,
                start_index: int = 0,
            ) -> dict | None:
                deadline = time.time() + timeout
                cursor = start_index
                while time.time() < deadline:
                    async with event_cond:
                        for idx in range(cursor, len(event_log)):
                            mensagem = event_log[idx]
                            if predicate(mensagem):
                                return mensagem
                        cursor = len(event_log)
                        remaining = deadline - time.time()
                        if remaining <= 0:
                            break
                        try:
                            await asyncio.wait_for(event_cond.wait(), timeout=min(1.0, remaining))
                        except asyncio.TimeoutError:
                            pass
                return None

            def _save_captured_report_bytes(
                payload: bytes,
                kind: str,
                suffix: str,
                source_name: str,
            ) -> str | None:
                safe_suffix = suffix if suffix.startswith(".") else f".{suffix}"
                filename = (
                    f"Relatorio_de_Vendas_Pix_{data_br.replace('/', '-')}_{company_norm}_auto{safe_suffix}"
                    if kind == "pix"
                    else f"Historico_Simplificado_de_vendas_{data_br.replace('/', '-')}_{company_norm}_auto{safe_suffix}"
                )
                target = artifacts_dir / filename
                try:
                    target.write_bytes(payload)
                except Exception:
                    return None
                try:
                    if safe_suffix.lower() == ".csv":
                        text = _read_text_file(target)
                    elif safe_suffix.lower() in {".xlsx", ".xls"}:
                        text = _read_excel_text(target)
                    else:
                        text = _read_pdf_text(target)
                    text_norm = _normalize_ascii_text(text)
                    detected_date = _extract_local_report_date_br(text)
                    if detected_date and detected_date != data_br:
                        return None
                    if kind == "pix":
                        if safe_suffix.lower() == ".csv" and "data da venda" in text_norm and "valor bruto" in text_norm:
                            return str(target)
                        if safe_suffix.lower() in {".xlsx", ".xls"} and _looks_like_caixa_pix_xlsx(target, data_br, text):
                            converted = _convert_pix_xlsx_to_csv(str(target))
                            return converted or str(target)
                        if safe_suffix.lower() == ".pdf" and "valor bruto" in text_norm and "pix" in text_norm:
                            return str(target)
                    else:
                        if safe_suffix.lower() in {".xlsx", ".xls"}:
                            text = _read_excel_text(target)
                            text_norm = _normalize_ascii_text(text)
                        if (
                            _looks_like_caixa_card_report_text(text)
                        ):
                            return str(target)
                        if safe_suffix.lower() in {".xlsx", ".xls"}:
                            try:
                                card_reports = _build_card_reports_from_caixa_xlsx(str(target), data_br)
                            except Exception:
                                card_reports = {}
                            if any(report.get("itens_autorizados") for report in card_reports.values()):
                                return str(target)
                except Exception:
                    pass
                try:
                    if target.exists():
                        target.unlink()
                except Exception:
                    pass
                return None

            def _persist_downloaded_report(path_like: str | None, kind: str) -> str | None:
                if not path_like:
                    return None
                try:
                    source_path = Path(str(path_like))
                except Exception:
                    return path_like
                try:
                    payload = source_path.read_bytes()
                except Exception:
                    return str(source_path)
                normalized_source = _finalize_local_report_path(source_path)
                effective_suffix = _effective_local_report_suffix(normalized_source) or ".pdf"
                saved = _save_captured_report_bytes(payload, kind, effective_suffix, str(source_path))
                if saved:
                    try:
                        normalized_path = Path(normalized_source)
                        if normalized_path.exists() and normalized_path.resolve() != Path(saved).resolve():
                            normalized_path.unlink()
                        if source_path.exists() and source_path.resolve() != Path(saved).resolve():
                            source_path.unlink()
                    except Exception:
                        pass
                    return saved
                return normalized_source

            def _find_export_url_in_payload(payload):
                if isinstance(payload, dict):
                    for value in payload.values():
                        found = _find_export_url_in_payload(value)
                        if found:
                            return found
                elif isinstance(payload, list):
                    for value in payload:
                        found = _find_export_url_in_payload(value)
                        if found:
                            return found
                elif isinstance(payload, str):
                    text = payload.strip()
                    if text.startswith("http://") or text.startswith("https://"):
                        return text
                    if "/screenservices/" in text or "/download" in text.lower():
                        return text
                return None

            def _extract_binary_payload_from_json(payload):
                if isinstance(payload, dict):
                    binary_data = payload.get("BinaryData")
                    if isinstance(binary_data, str) and binary_data.strip():
                        raw = base64.b64decode(binary_data)
                        header = raw[:8]
                        if header.startswith(b"PK"):
                            suffix = ".xlsx"
                        elif header.startswith(b"%PDF"):
                            suffix = ".pdf"
                        else:
                            try:
                                preview = raw[:512].decode("utf-8", errors="ignore").lower()
                            except Exception:
                                preview = ""
                            suffix = ".csv" if (";" in preview or "," in preview or "valor bruto" in preview) else ".bin"
                        return raw, suffix
                    for value in payload.values():
                        found = _extract_binary_payload_from_json(value)
                        if found:
                            return found
                elif isinstance(payload, list):
                    for value in payload:
                        found = _extract_binary_payload_from_json(value)
                        if found:
                            return found
                return None

            async def wait_for_captured_report(
                session_id: str,
                kind: str,
                event_start_index: int,
                started_at: float,
                timeout: float = 40.0,
            ) -> str | None:
                seen_candidates: list[dict[str, object]] = []
                seen_export_urls: set[str] = set()

                def is_candidate(message: dict) -> bool:
                    method = str(message.get("method") or "")
                    params = message.get("params") or {}
                    if method == "Browser.downloadWillBegin":
                        suggested = str(params.get("suggestedFilename") or "").lower()
                        url = str(params.get("url") or "").lower()
                        if kind == "pix":
                            return (
                                suggested.endswith((".csv", ".xlsx", ".pdf"))
                                or any(token in suggested for token in ("csv", "xlsx", "pix"))
                                or "pix" in url
                            )
                        return (
                            suggested.endswith((".pdf", ".xlsx"))
                            or any(token in suggested for token in ("pdf", "xlsx", "historico", "vendas"))
                            or any(token in url for token in ("historico", "export", "download", "screenservices", "gerar", "arquivo"))
                        )
                    if method == "Network.requestWillBeSent":
                        if str(message.get("sessionId") or "") != str(session_id):
                            return False
                        request = params.get("request") or {}
                        url = str(request.get("url") or "").lower()
                        if kind == "pix":
                            return (
                                "pix" in url
                                or "export" in url
                                or "download" in url
                                or "screenservices" in url
                                or "gerar" in url
                                or "arquivo" in url
                            )
                        return (
                            "historico" in url
                            or any(token in url for token in ("export", "download", "screenservices", "gerar", "arquivo"))
                        )
                    if method != "Network.responseReceived":
                        return False
                    if str(message.get("sessionId") or "") != str(session_id):
                        return False
                    response = params.get("response") or {}
                    url = str(response.get("url") or "").lower()
                    mime_type = str(response.get("mimeType") or "").lower()
                    headers = {str(k).lower(): str(v) for k, v in (response.get("headers") or {}).items()}
                    content_disposition = headers.get("content-disposition", "").lower()
                    if kind == "pix":
                        return (
                            "text/csv" in mime_type
                            or "application/json" in mime_type
                            or "spreadsheet" in mime_type
                            or "excel" in mime_type
                            or ".xlsx" in content_disposition
                            or ".xls" in content_disposition
                            or "csv" in content_disposition
                            or "pdf" in content_disposition
                            or ("pix" in url)
                            or ("export" in url or "download" in url or "screenservices" in url or "gerar" in url or "arquivo" in url)
                        )
                    return (
                        "application/pdf" in mime_type
                        or "application/json" in mime_type
                        or "spreadsheet" in mime_type
                        or "excel" in mime_type
                        or ".pdf" in url
                        or ".xlsx" in content_disposition
                        or ".xls" in content_disposition
                        or "pdf" in content_disposition
                        or ("historico" in url)
                        or ("export" in url or "download" in url or "screenservices" in url or "gerar" in url or "arquivo" in url)
                    )

                deadline = time.time() + timeout
                processed_request_ids: set[str] = set()
                browser_download_seen = False

                async def try_browser_export_urls() -> str | None:
                    try:
                        captured_urls = await eval_js(
                            session_id,
                            """
                            (() => {
                                const data = window.__codexExportSignals || {};
                                const urls = [];
                                for (const value of [
                                    ...(data.openedUrls || []),
                                    ...(data.anchorUrls || []),
                                    ...(data.iframeUrls || []),
                                    data.lastUrl || '',
                                ]) {
                                    const text = String(value || '').trim();
                                    if (text) urls.push(text);
                                }
                                return [...new Set(urls)];
                            })()
                            """,
                            timeout=5.0,
                        ) or []
                    except Exception:
                        captured_urls = []
                    for export_url in captured_urls:
                        export_url = str(export_url or "").strip()
                        if not export_url or export_url in seen_export_urls:
                            continue
                        seen_export_urls.add(export_url)
                        try:
                            fetched = await eval_js(
                                session_id,
                                f"""
                                (async () => {{
                                    const url = {export_url!r};
                                    const response = await fetch(url, {{ credentials: 'include' }});
                                    const buffer = await response.arrayBuffer();
                                    const bytes = new Uint8Array(buffer);
                                    let binary = '';
                                    const chunk = 0x8000;
                                    for (let i = 0; i < bytes.length; i += chunk) {{
                                        binary += String.fromCharCode(...bytes.subarray(i, i + chunk));
                                    }}
                                    return {{
                                        ok: response.ok,
                                        status: response.status,
                                        mimeType: response.headers.get('content-type') || '',
                                        contentDisposition: response.headers.get('content-disposition') || '',
                                        body: btoa(binary),
                                    }};
                                }})()
                                """,
                                timeout=60.0,
                            ) or {}
                            if fetched.get("ok") and fetched.get("body"):
                                fetched_mime = str(fetched.get("mimeType") or "").lower()
                                fetched_disp = str(fetched.get("contentDisposition") or "").lower()
                                fetched_suffix = _report_suffix_from_response_metadata(fetched_mime, fetched_disp)
                                fetched_payload = base64.b64decode(str(fetched.get("body") or ""))
                                saved = _save_captured_report_bytes(fetched_payload, kind, fetched_suffix, export_url)
                                if saved:
                                    return saved
                        except Exception:
                            pass
                    return None

                while time.time() < deadline:
                    current_state = await get_portal_state_v2(session_id, timeout=5.0)
                    if current_state == "portal_error":
                        raise RuntimeError(
                            f"A Caixa abriu a página de erro ao gerar o relatório de {'cartões' if kind == 'cartoes' else 'PIX'}."
                        )
                    quick_found = _wait_for_downloaded_report(
                        browser_download_dir,
                        data_br,
                        kind,
                        started_at,
                        timeout=0.0,
                    )
                    if quick_found:
                        return _persist_downloaded_report(quick_found, kind)
                    direct_saved = await try_browser_export_urls()
                    if direct_saved:
                        return direct_saved
                    event = await wait_for_event(is_candidate, timeout=min(5.0, max(0.5, deadline - time.time())), start_index=event_start_index)
                    if not event:
                        await asyncio.sleep(0.5)
                        event_start_index = len(event_log)
                        continue
                    method = str(event.get("method") or "")
                    params = event.get("params") or {}
                    if method == "Browser.downloadWillBegin":
                        browser_download_seen = True
                        await asyncio.sleep(2.0)
                        found = _wait_for_downloaded_report(browser_download_dir, data_br, kind, time.time() - 5.0, timeout=10.0)
                        if found:
                            return _persist_downloaded_report(found, kind)
                        event_start_index = len(event_log)
                        continue

                    if method == "Network.requestWillBeSent":
                        request = params.get("request") or {}
                        seen_candidates.append(
                            {
                                "method": method,
                                "requestId": str(params.get("requestId") or ""),
                                "url": str(request.get("url") or ""),
                                "postData": str(request.get("postData") or "")[:4000],
                            }
                        )
                        event_start_index = len(event_log)
                        continue

                    request_id = str(params.get("requestId") or "")
                    if not request_id or request_id in processed_request_ids:
                        event_start_index = len(event_log)
                        continue
                    processed_request_ids.add(request_id)
                    response = params.get("response") or {}
                    seen_candidates.append(
                        {
                            "method": method,
                            "requestId": request_id,
                            "url": str(response.get("url") or ""),
                            "status": response.get("status"),
                            "mimeType": str(response.get("mimeType") or ""),
                            "headers": {str(k): str(v) for k, v in (response.get("headers") or {}).items()},
                        }
                    )
                    headers = {str(k).lower(): str(v) for k, v in (response.get("headers") or {}).items()}
                    content_disposition = headers.get("content-disposition", "")
                    mime_type = str(response.get("mimeType") or "").lower()
                    disposition_norm = content_disposition.lower()
                    suffix = _report_suffix_from_response_metadata(mime_type, disposition_norm)
                    try:
                        body = await cdp("Network.getResponseBody", {"requestId": request_id}, session_id=session_id, timeout=20.0)
                        raw_body = body.get("body") or ""
                        payload = base64.b64decode(raw_body) if body.get("base64Encoded") else str(raw_body).encode("utf-8", errors="ignore")
                        if "application/json" in mime_type:
                            try:
                                json_text = payload.decode("utf-8", errors="ignore")
                                json_payload = json.loads(json_text)
                                try:
                                    debug_path = artifacts_dir / f"azulzinha_export_payload_{kind}.json"
                                    debug_path.write_text(json.dumps(json_payload, ensure_ascii=False, indent=2), encoding="utf-8")
                                except Exception:
                                    pass
                                embedded_binary = _extract_binary_payload_from_json(json_payload)
                                if embedded_binary:
                                    _emit_pix_status(
                                        on_status,
                                        f"Resposta JSON com arquivo embutido detectada para {kind}.",
                                    )
                                    embedded_payload, embedded_suffix = embedded_binary
                                    saved = _save_captured_report_bytes(
                                        embedded_payload,
                                        kind,
                                        embedded_suffix,
                                        str(response.get("url") or ""),
                                    )
                                    if saved:
                                        return saved
                                export_url = _find_export_url_in_payload(json_payload)
                                if export_url:
                                    if export_url.startswith("/"):
                                        base_url = str(response.get("url") or "")
                                        export_url = urljoin(base_url, export_url)
                                    fetched = await eval_js(
                                        session_id,
                                        f"""
                                        (async () => {{
                                            const url = {export_url!r};
                                            const response = await fetch(url, {{ credentials: 'include' }});
                                            const buffer = await response.arrayBuffer();
                                            const bytes = new Uint8Array(buffer);
                                            let binary = '';
                                            const chunk = 0x8000;
                                            for (let i = 0; i < bytes.length; i += chunk) {{
                                                binary += String.fromCharCode(...bytes.subarray(i, i + chunk));
                                            }}
                                            return {{
                                                ok: response.ok,
                                                status: response.status,
                                                mimeType: response.headers.get('content-type') || '',
                                                contentDisposition: response.headers.get('content-disposition') || '',
                                                body: btoa(binary),
                                            }};
                                        }})()
                                        """,
                                        timeout=60.0,
                                    ) or {}
                                    if fetched.get("ok") and fetched.get("body"):
                                        fetched_mime = str(fetched.get("mimeType") or "").lower()
                                        fetched_disp = str(fetched.get("contentDisposition") or "").lower()
                                        fetched_suffix = _report_suffix_from_response_metadata(fetched_mime, fetched_disp)
                                        fetched_payload = base64.b64decode(str(fetched.get("body") or ""))
                                        saved = _save_captured_report_bytes(fetched_payload, kind, fetched_suffix, export_url)
                                        if saved:
                                            return saved
                            except Exception:
                                pass
                        saved = _save_captured_report_bytes(payload, kind, suffix, str(response.get("url") or ""))
                        if saved:
                            return saved
                    except Exception:
                        pass
                    event_start_index = len(event_log)

                if browser_download_seen:
                    return _persist_downloaded_report(
                            _wait_for_downloaded_report(browser_download_dir, data_br, kind, time.time() - 10.0, timeout=10.0),
                        kind,
                    )
                direct_saved = await try_browser_export_urls()
                if direct_saved:
                    return direct_saved
                try:
                    debug_path = artifacts_dir / f"azulzinha_network_candidates_{kind}.json"
                    debug_path.write_text(json.dumps(seen_candidates, ensure_ascii=False, indent=2), encoding="utf-8")
                except Exception:
                    pass
                try:
                    export_signals = await eval_js(
                        session_id,
                        """
                        (() => {
                            const data = window.__codexExportSignals || {};
                            return {
                                openedUrls: data.openedUrls || [],
                                anchorUrls: data.anchorUrls || [],
                                iframeUrls: data.iframeUrls || [],
                                lastUrl: data.lastUrl || '',
                            };
                        })()
                        """,
                        timeout=5.0,
                    )
                    debug_signals_path = artifacts_dir / f"azulzinha_export_signals_{kind}.json"
                    debug_signals_path.write_text(json.dumps(export_signals, ensure_ascii=False, indent=2), encoding="utf-8")
                except Exception:
                    pass
                return None

            async def navigate(session_id: str, url: str) -> None:
                await cdp("Page.navigate", {"url": url}, session_id=session_id)
                await wait_for_condition(session_id, "document.readyState === 'complete' || document.readyState === 'interactive'", timeout=80.0)

            async def click_by_text(session_id: str, text_options: list[str], timeout: float = 30.0) -> bool:
                options = [_normalize_ascii_text(item).upper() for item in text_options]
                expression = f"""
                (() => {{
                    const targets = {json.dumps(options)};
                    const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                    const visible = (el) => {{
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const nodes = [...document.querySelectorAll('button, a, [role="button"], li, span, div, label')].filter(visible);
                    for (const target of targets) {{
                        const matches = nodes
                            .map((el) => {{
                                const text = norm(el.innerText || el.textContent || '');
                                if (!text.includes(target)) return null;
                                const clickable = el.closest('button, a, [role="button"], label') || el.closest('li, div, span') || el;
                                const clickableText = norm(clickable.innerText || clickable.textContent || '');
                                const role = norm(clickable.getAttribute('role') || '');
                                const tag = norm(clickable.tagName || '');
                                const interactiveScore = tag === 'BUTTON' || tag === 'A' || tag === 'LABEL' || role === 'BUTTON' ? 500 : 0;
                                const exactScore = clickableText === target || text === target ? 200 : 0;
                                return {{
                                    clickable,
                                    score: interactiveScore + exactScore - clickableText.length,
                                }};
                            }})
                            .filter(Boolean)
                            .sort((a, b) => b.score - a.score);
                        const match = matches.length ? matches[0].clickable : null;
                        if (match) {{
                            match.scrollIntoView({{ block: 'center', inline: 'center' }});
                            match.click();
                            return true;
                        }}
                    }}
                    return false;
                }})()
                """
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    if await eval_js(session_id, expression):
                        return True
                    await asyncio.sleep(0.5)
                return False

            async def click_card_by_text(session_id: str, text_options: list[str], timeout: float = 30.0) -> bool:
                options = [_normalize_ascii_text(item).upper() for item in text_options]
                expression = f"""
                (() => {{
                    const targets = {json.dumps(options)};
                    const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                    const visible = (el) => {{
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const nodes = [...document.querySelectorAll('[id$="-Content"], .card-content, .ph.card.card-content')].filter(visible);
                    for (const target of targets) {{
                        const matches = nodes
                            .map((el) => {{
                                const text = norm(el.innerText || el.textContent);
                                if (!text.includes(target)) return null;
                                const className = (el.className || '').toString().toUpperCase();
                                const id = (el.id || '').toUpperCase();
                                const isCard = className.includes('CARD-CONTENT') || className.includes('PH CARD');
                                const exact = text === target || text.endsWith(target);
                                return {{
                                    el,
                                    score: (exact ? 1000 : 0) + (isCard ? 200 : 0) - text.length,
                                }};
                            }})
                            .filter(Boolean)
                            .sort((a, b) => b.score - a.score);
                        const node = matches.length ? matches[0].el : null;
                        if (node) {{
                            node.scrollIntoView({{ block: 'center', inline: 'center' }});
                            node.click();
                            return true;
                        }}
                    }}
                    return false;
                }})()
                """
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    if await eval_js(session_id, expression):
                        return True
                    await asyncio.sleep(0.5)
                return False

            async def activate_sales_tab(session_id: str, tab_id: str, timeout: float = 40.0) -> None:
                expected_content = f"{tab_id}Content"
                expression = f"""
                (() => {{
                    const root = document.getElementById({tab_id!r});
                    if (!root) return 'missing-tab';
                    const button = root.querySelector('button[role="tab"]');
                    if (!button) return 'missing-button';
                    const content = document.getElementById({expected_content!r})?.querySelector('[role="tabpanel"]');
                    if (button.getAttribute('aria-selected') === 'true' && content && content.getAttribute('aria-hidden') === 'false') {{
                        return 'ready';
                    }}
                    button.scrollIntoView({{ block: 'center', inline: 'center' }});
                    button.focus();
                    button.dispatchEvent(new MouseEvent('mousedown', {{ bubbles: true, cancelable: true, view: window }}));
                    button.click();
                    button.dispatchEvent(new MouseEvent('mouseup', {{ bubbles: true, cancelable: true, view: window }}));
                    return 'clicked';
                }})()
                """
                deadline = time.time() + timeout
                last_state = ""
                while time.time() < deadline:
                    _check_cancelled()
                    state = await eval_js(session_id, expression)
                    last_state = str(state or "")
                    if state in {"missing-tab", "missing-button"}:
                        await asyncio.sleep(0.5)
                        continue
                    try:
                        await wait_for_condition(
                            session_id,
                            f"""
                            (() => {{
                                const button = document.querySelector("#{tab_id} button[role='tab']");
                                const content = document.querySelector("#{expected_content} [role='tabpanel']");
                                return !!button && !!content &&
                                    button.getAttribute('aria-selected') === 'true' &&
                                    content.getAttribute('aria-hidden') === 'false';
                            }})()
                            """,
                            timeout=2.5,
                            step=0.25,
                        )
                        return
                    except Exception:
                        await asyncio.sleep(0.5)
                try:
                    html_debug = await eval_js(
                        session_id,
                        "document.documentElement ? document.documentElement.outerHTML : ''",
                        timeout=15.0,
                    )
                    if html_debug:
                        debug_path = artifacts_dir / f"azulzinha_tabs_debug_{tab_id}.html"
                        debug_path.write_text(str(html_debug), encoding="utf-8")
                except Exception:
                    pass
                if last_state == "missing-tab":
                    raise RuntimeError(f"Não foi possível localizar a aba {tab_id} no portal Azulzinha/Caixa.")
                if last_state == "missing-button":
                    raise RuntimeError(f"Não foi possível localizar o botão da aba {tab_id} no portal Azulzinha/Caixa.")
                raise RuntimeError(f"Não foi possível abrir a aba {tab_id} no portal Azulzinha/Caixa.")

            async def wait_for_portal_settle(
                session_id: str,
                tab_id: str | None = None,
                timeout: float = 20.0,
                context_label: str = "a tela atual",
            ) -> None:
                content_selector = (
                    f"#{tab_id}Content [role='tabpanel']"
                    if tab_id
                    else (
                        "header[role='tablist'], #HistoricoVendas button[role='tab'], #Pix button[role='tab'], "
                        "[data-testid='vendas-btn-exportar'], [data-testid='vendas-periodo-hoje']"
                    )
                )
                has_tab_id_js = "true" if tab_id else "false"
                settle_expression = f"""
                    (() => {{
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const href = String(location.href || '').toUpperCase();
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                        const passwordInput = document.querySelector('#b2-b1-Input_Password');
                        const loginTextVisible = (
                            text.includes('ACESSE SUA CONTA') ||
                            (text.includes('CNPJ, CPF OU USUARIO') && text.includes('SENHA'))
                        );
                        const deviceVisible = text.includes('SELECIONE O DISPOSITIVO');
                        const tokenDeliveryVisible = (
                            text.includes('ESCOLHA POR ONDE DESEJA RECEBER') ||
                            text.includes('RECEBER POR E-MAIL') ||
                            text.includes('@GMAIL.COM')
                        );
                        const tokenVisible = Boolean(
                            [...document.querySelectorAll('input')]
                                .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el))
                                .length
                        ) && (
                            text.includes('TOKEN') ||
                            text.includes('CODIGO') ||
                            text.includes('E-MAIL') ||
                            text.includes('EMAIL')
                        );
                        const invalidVisible = (
                            text.includes('CODIGO INVALIDO') ||
                            text.includes('TOKEN INVALIDO') ||
                            text.includes('TOKEN EXPIRADO') ||
                            text.includes('TENTATIVAS')
                        );
                        if (href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST')) return 'portal_error';
                        if (
                            href.includes('ISTIMEOUT=TRUE') ||
                            (visible(loginInput) && visible(passwordInput)) ||
                            (
                                loginTextVisible &&
                                !deviceVisible &&
                                !tokenDeliveryVisible &&
                                !tokenVisible &&
                                !invalidVisible
                            )
                        ) return 'login';
                        const busyNodes = [
                            ...document.querySelectorAll('[aria-busy="true"], .ph-item, .ph-picture, .ph-picture-small, .spinner-border, .spinner-grow, .loading, .skeleton, .ant-skeleton')
                        ].filter(visible);
                        if (!{has_tab_id_js} && visible(document.querySelector('[data-testid="vendas-btn-exportar"]'))) {{
                            return busyNodes.length ? '' : 'ready';
                        }}
                        const content = document.querySelector({content_selector!r});
                        if (!content || (content.getAttribute && content.getAttribute('aria-hidden') === 'true')) return '';
                        if (busyNodes.length) return '';
                        const body = (content.innerText || content.textContent || document.body?.innerText || '').trim();
                        return body.length > 20 ? 'ready' : '';
                    }})()
                    """
                try:
                    state = await wait_for_condition(
                        session_id,
                        settle_expression,
                        timeout=timeout,
                        step=0.4,
                    )
                except Exception:
                    await capture_portal_html_debug_v2(session_id, "azulzinha_portal_settle_debug.html")
                    raise
                if state == "portal_error":
                    raise RuntimeError(f"A Caixa abriu a pagina de erro durante {context_label}.")
                if state == "login":
                    raise RuntimeError(f"A Caixa voltou para o login durante {context_label}.")

            async def wait_for_tab_content(session_id: str, tab_id: str, timeout: float = 45.0) -> None:
                content_id = f"{tab_id}Content"
                state = await wait_for_condition(
                    session_id,
                    f"""
                    (() => {{
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const href = String(location.href || '').toUpperCase();
                        if (href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST')) return 'portal_error';
                        const content = document.querySelector("#{content_id} [role='tabpanel']");
                        if (!content || content.getAttribute('aria-hidden') !== 'false') return '';
                        const body = content.innerText || content.textContent || '';
                        const html = content.innerHTML || '';
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const busyNodes = [...content.querySelectorAll('[aria-busy="true"], .ph-item, .ph-picture, .ph-picture-small, .spinner-border, .spinner-grow, .loading, .skeleton, .ant-skeleton')]
                            .filter(visible);
                        if (busyNodes.length) return '';
                        if (body.trim().length > 40 || html.includes('data-testid') || html.includes('Exportar') || html.includes('Filtro')) return 'ready';
                        return '';
                    }})()
                    """,
                    timeout=timeout,
                    step=0.5,
                )
                if state == "portal_error":
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_tab_error_{tab_id}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    raise RuntimeError(f"A Caixa abriu a pagina de erro ao carregar a aba {tab_id}.")
                await asyncio.sleep(0.6)
                await wait_for_portal_settle(
                    session_id,
                    tab_id=tab_id,
                    timeout=20.0,
                    context_label=f"carregar a aba {tab_id}",
                )

            async def focus_selector(session_id: str, selector: str) -> bool:
                return bool(
                    await eval_js(
                        session_id,
                        f"""
                        (() => {{
                            const el = document.querySelector({selector!r});
                            if (!el) return false;
                            el.focus();
                            return true;
                        }})()
                        """,
                    )
                )

            async def insert_text(session_id: str, selector: str, text: str) -> None:
                if not await focus_selector(session_id, selector):
                    raise RuntimeError(f"Não foi possível localizar o campo {selector} na Azulzinha/Caixa.")
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyDown", "windowsVirtualKeyCode": 17, "nativeVirtualKeyCode": 17, "key": "Control", "code": "ControlLeft", "modifiers": 2},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyDown", "windowsVirtualKeyCode": 65, "nativeVirtualKeyCode": 65, "key": "a", "code": "KeyA", "modifiers": 2},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyUp", "windowsVirtualKeyCode": 65, "nativeVirtualKeyCode": 65, "key": "a", "code": "KeyA", "modifiers": 2},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyUp", "windowsVirtualKeyCode": 17, "nativeVirtualKeyCode": 17, "key": "Control", "code": "ControlLeft"},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyDown", "windowsVirtualKeyCode": 8, "nativeVirtualKeyCode": 8, "key": "Backspace", "code": "Backspace"},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyUp", "windowsVirtualKeyCode": 8, "nativeVirtualKeyCode": 8, "key": "Backspace", "code": "Backspace"},
                    session_id=session_id,
                )
                for char in str(text or ""):
                    await cdp("Input.insertText", {"text": char}, session_id=session_id)
                    await asyncio.sleep(0.04)
                await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const el = document.querySelector({selector!r});
                        if (!el) return false;
                        el.dispatchEvent(new KeyboardEvent('keyup', {{ bubbles: true, key: '0' }}));
                        el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                        el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                        return true;
                    }})()
                    """,
                )

            async def press_tab(session_id: str) -> None:
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyDown", "windowsVirtualKeyCode": 9, "nativeVirtualKeyCode": 9, "key": "Tab", "code": "Tab"},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchKeyEvent",
                    {"type": "keyUp", "windowsVirtualKeyCode": 9, "nativeVirtualKeyCode": 9, "key": "Tab", "code": "Tab"},
                    session_id=session_id,
                )

            async def click_selector_native(session_id: str, selector: str, root_selector: str | None = None) -> bool:
                root_selector_js = json.dumps(root_selector) if root_selector else "null"
                rect = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const root = {root_selector_js} ? document.querySelector({root_selector_js}) : document;
                        if (!root) return null;
                        const el = [...root.querySelectorAll({selector!r})].find((candidate) => {{
                            const r = candidate.getBoundingClientRect();
                            const style = getComputedStyle(candidate);
                            return r.width > 0 && r.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }});
                        if (!el) return null;
                        const r = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        if (r.width <= 0 || r.height <= 0 || style.visibility === 'hidden' || style.display === 'none') return null;
                        return {{
                            x: r.left + (r.width / 2),
                            y: r.top + (r.height / 2),
                        }};
                    }})()
                    """,
                )
                if not rect:
                    return False
                await cdp(
                    "Input.dispatchMouseEvent",
                    {"type": "mousePressed", "x": rect["x"], "y": rect["y"], "button": "left", "clickCount": 1},
                    session_id=session_id,
                )
                await cdp(
                    "Input.dispatchMouseEvent",
                    {"type": "mouseReleased", "x": rect["x"], "y": rect["y"], "button": "left", "clickCount": 1},
                    session_id=session_id,
                )
                return True

            async def set_date_inputs(session_id: str) -> None:
                shortcut = _azulzinha_sales_period_shortcut(data_br)
                if shortcut == "ontem":
                    shortcut_selector = '[data-testid="vendas-periodo-ontem"]'
                    try:
                        await wait_for_condition(
                            session_id,
                            f"""
                            (() => {{
                                const button = document.querySelector({shortcut_selector!r});
                                if (!button) return false;
                                const rect = button.getBoundingClientRect();
                                const style = getComputedStyle(button);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            }})()
                            """,
                            timeout=15.0,
                            step=0.25,
                        )
                    except TimeoutError:
                        # Portais antigos não têm atalhos relativos; preserva o calendário legado.
                        pass
                    else:
                        if not await click_selector_native(session_id, shortcut_selector):
                            raise RuntimeError("A Caixa exibiu o atalho Ontem, mas o clique não foi aceito.")
                        try:
                            await wait_for_condition(
                                session_id,
                                f"""
                                (() => {{
                                    const expected = {data_br!r};
                                    const expectedRange = expected + ' - ' + expected;
                                    const period = document.querySelector('[data-testid="generic-calendar-periodo-calendar"]');
                                    return String(period?.innerText || '').replace(/\\s+/g, ' ').trim() === expectedRange;
                                }})()
                                """,
                                timeout=20.0,
                                step=0.25,
                            )
                            return
                        except TimeoutError as exc:
                            raise RuntimeError(
                                f"A Caixa nao confirmou o atalho Ontem para o periodo {data_br}; o relatorio nao sera exportado."
                            ) from exc

                ok = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const value = {data_br!r};
                        const isoValue = value.split('/').reverse().join('-');
                        const digits = value.replace(/\\D/g, '');
                        const setNativeValue = (el, val) => {{
                            const proto = el instanceof HTMLTextAreaElement ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
                            const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
                            if (setter) setter.call(el, val); else el.value = val;
                            el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                        }};
                        const inputs = [...document.querySelectorAll('input')]
                            .filter((el) => {{
                                const type = (el.type || '').toLowerCase();
                                const name = ((el.name || '') + ' ' + (el.id || '') + ' ' + (el.placeholder || '') + ' ' + (el.getAttribute('aria-label') || '')).toLowerCase();
                                return type !== 'hidden' && !el.disabled && (
                                    type === 'date' || name.includes('data') || name.includes('periodo') || /\\d{{2}}\\/\\d{{2}}\\/\\d{{4}}/.test(el.value || '')
                                );
                            }});
                        if (!inputs.length) return false;
                        const flatpickrInput = document.querySelector('input[id$="InputPicker"]');
                        if (flatpickrInput && flatpickrInput._flatpickr) {{
                            try {{
                                flatpickrInput._flatpickr.setDate([isoValue, isoValue], true, 'Y-m-d');
                            }} catch (_err) {{}}
                        }}
                        for (const input of inputs.slice(0, 2)) {{
                            input.focus();
                            setNativeValue(input, (input.type || '').toLowerCase() === 'date' ? isoValue : digits);
                            setNativeValue(input, (input.type || '').toLowerCase() === 'date' ? isoValue : value);
                        }}
                        return true;
                    }})()
                    """,
                )
                if not ok:
                    ok = await eval_js(
                        session_id,
                        f"""
                        (() => {{
                            const value = {data_br!r};
                            const visible = (el) => {{
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            }};
                            const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                            const clickable = [...document.querySelectorAll('input, button, a, [role="button"], div, span')]
                                .filter(visible)
                                .find((el) => {{
                                    const text = norm(el.innerText || el.textContent || el.placeholder || el.getAttribute('aria-label') || '');
                                    const id = norm(el.id || '');
                                    return text.includes('DATA') || text.includes('PERIODO') || id.includes('DATA') || id.includes('PERIODO');
                                }});
                            if (!clickable) return false;
                            clickable.click();
                            const candidates = [...document.querySelectorAll('input')]
                                .filter((el) => visible(el) && (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                            const target = candidates.find((el) => {{
                                const meta = norm((el.name || '') + ' ' + (el.id || '') + ' ' + (el.placeholder || '') + ' ' + (el.getAttribute('aria-label') || ''));
                                return meta.includes('DATA') || meta.includes('PERIODO');
                            }}) || candidates[0];
                            if (!target) return false;
                            const proto = target instanceof HTMLTextAreaElement ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
                            const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
                            const finalValue = (target.type || '').toLowerCase() === 'date' ? value.split('/').reverse().join('-') : value;
                            target.focus();
                            if (setter) setter.call(target, finalValue); else target.value = finalValue;
                            target.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            target.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            target.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                            return true;
                        }})()
                        """,
                    )
                if not ok:
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / "azulzinha_pix_date_debug.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    raise RuntimeError("Não foi possível preencher a data no portal Azulzinha/Caixa.")
                await eval_js(
                    session_id,
                    """
                    (() => {
                        const visible = (el) => {
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const button = document.querySelector('[data-testid="generic-calendar-button-aplicar"]');
                        if (!button || !visible(button)) return false;
                        button.scrollIntoView({ block: 'center', inline: 'center' });
                        button.click();
                        return true;
                    })()
                    """,
                )
                try:
                    await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const wrapper = document.querySelector('[data-testid="calendar-main-div"]')?.closest('[aria-hidden]');
                            return !wrapper || wrapper.getAttribute('aria-hidden') === 'true';
                        })()
                        """,
                        timeout=15.0,
                        step=0.25,
                    )
                except Exception:
                    pass
                await asyncio.sleep(0.8)
                for _attempt in range(3):
                    period_ok = await eval_js(
                        session_id,
                        f"""
                        (() => {{
                            const expected = {data_br!r};
                            const norm = (v) => (v || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .replace(/\\s+/g, ' ')
                                .trim();
                            const period = norm(document.querySelector('[data-testid="generic-calendar-periodo-calendar"]')?.innerText || '');
                            const body = norm(document.body?.innerText || '');
                            return period.includes(expected) || body.includes('Periodo ' + expected + ' - ' + expected);
                        }})()
                        """,
                        timeout=10.0,
                    )
                    if period_ok:
                        break
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const norm = (v) => (v || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .replace(/\\s+/g, ' ')
                                .trim()
                                .toUpperCase();
                            const visible = (el) => {
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const button = document.querySelector('[data-testid="generic-calendar-button-aplicar"]')
                                || [...document.querySelectorAll('button, a, [role="button"], div.btn')]
                                    .filter(visible)
                                    .find((el) => {
                                        const text = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || '');
                                        return text === 'APLICAR' || text.includes('MOSTRAR RESULTADOS');
                                    });
                            if (!button || !visible(button)) return false;
                            button.scrollIntoView({ block: 'center', inline: 'center' });
                            button.click();
                            return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                    await asyncio.sleep(1.5)
                else:
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_date_not_applied_{kind}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    raise RuntimeError(
                        f"A Caixa nao confirmou o periodo {data_br} antes da exportacao do relatorio de {'PIX' if kind == 'pix' else 'cartoes'}."
                    )

            async def ensure_all_establishments_selected(
                session_id: str,
                tab_id: str,
                timeout: float = 25.0,
            ) -> bool:
                expression = f"""
                (() => {{
                    const visible = (el) => {{
                        if (!el) return false;
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const content = document.querySelector("#{tab_id}Content [role='tabpanel']");
                    if (!content || content.getAttribute('aria-hidden') === 'true') return 'missing-content';
                    const filterTrigger = [
                        ...content.querySelectorAll(
                            '[data-testid="vendas-hoje-link-filtrar"], [data-testid="historico-vendas-container-filtros"], [data-testid*="container-filtros"], [data-testid*="link-filtrar"]'
                        )
                    ].find(visible);
                    const sidebar = [
                        ...document.querySelectorAll('aside.osui-sidebar, [role="complementary"]')
                    ].find((el) => visible(el) && (
                        el.querySelector('[data-testid="generic-filter-btn-resultados"]') ||
                        el.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]') ||
                        el.querySelector('[data-testid="generic-filter-check-all-estabelecimentos"]')
                    ));
                    if (!filterTrigger && !sidebar) return 'no-filter';
                    if (!sidebar) {{
                        if (!filterTrigger) return 'no-filter';
                        filterTrigger.scrollIntoView({{ block: 'center', inline: 'center' }});
                        filterTrigger.click();
                        return 'opening';
                    }}
                    const title = sidebar.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]');
                    if (!title) return 'no-estabelecimentos';
                    const titleWrapper = title.closest('[role="button"]') || title.closest('.osui-accordion-item__title') || title;
                    const accordionItem = title.closest('.osui-accordion-item');
                    const contentWrapper = accordionItem
                        ? accordionItem.querySelector('.osui-accordion-item__content, [id$="ContentWrapper"]')
                        : null;
                    const collapsed = Boolean(
                        contentWrapper && (
                            contentWrapper.getAttribute('aria-hidden') === 'true' ||
                            String(contentWrapper.className || '').includes('--is-collapsed')
                        )
                    );
                    if (collapsed) {{
                        titleWrapper.scrollIntoView({{ block: 'center', inline: 'center' }});
                        titleWrapper.click();
                        return 'expanding';
                    }}
                    const establishmentChecks = [
                        ...sidebar.querySelectorAll('[data-testid^="generic-filter-check-estabelecimento-"]')
                    ].filter((el) => !el.disabled);
                    if (!establishmentChecks.length) return 'no-estabelecimentos';
                    if (establishmentChecks.length > 1) {{
                        const checkedCount = establishmentChecks.filter((el) => el.checked).length;
                        if (checkedCount < establishmentChecks.length) {{
                            const checkAll = sidebar.querySelector('[data-testid="generic-filter-check-all-estabelecimentos"]');
                            if (checkAll && !checkAll.disabled && visible(checkAll)) {{
                                checkAll.click();
                                return 'selecting-all';
                            }}
                            const unchecked = establishmentChecks.filter((el) => !el.checked);
                            for (const checkbox of unchecked) {{
                                checkbox.click();
                            }}
                            return unchecked.length ? 'selecting-manual' : 'selected';
                        }}
                    }}
                    const applyButton = sidebar.querySelector('[data-testid="generic-filter-btn-resultados"]');
                    if (!applyButton || !visible(applyButton) || applyButton.disabled) return 'ready';
                    applyButton.click();
                    return establishmentChecks.length > 1 ? 'applied-multiple' : 'applied-single';
                }})()
                """
                deadline = time.time() + timeout
                found_filter = False
                applied_multiple = False
                while time.time() < deadline:
                    _check_cancelled()
                    state = str(await eval_js(session_id, expression, timeout=15.0) or "").strip()
                    if state in {
                        "opening",
                        "expanding",
                        "selecting-all",
                        "selecting-manual",
                        "selected",
                    }:
                        found_filter = True
                        await asyncio.sleep(0.6)
                        continue
                    if state in {"applied-multiple", "applied-single"}:
                        found_filter = True
                        applied_multiple = state == "applied-multiple"
                        try:
                            await wait_for_condition(
                                session_id,
                                """
                                (() => {
                                    const visible = (el) => {
                                        if (!el) return false;
                                        const rect = el.getBoundingClientRect();
                                        const style = getComputedStyle(el);
                                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                    };
                                    const sidebar = [
                                        ...document.querySelectorAll('aside.osui-sidebar, [role="complementary"]')
                                    ].find((el) => visible(el) && (
                                        el.querySelector('[data-testid="generic-filter-btn-resultados"]') ||
                                        el.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]')
                                    ));
                                    return !sidebar;
                                })()
                                """,
                                timeout=6.0,
                                step=0.2,
                            )
                        except Exception:
                            pass
                        try:
                            await wait_for_portal_settle(
                                session_id,
                                tab_id=tab_id,
                                timeout=8.0,
                                context_label=f"aplicar os estabelecimentos da aba {tab_id}",
                            )
                        except TimeoutError:
                            pass
                        return applied_multiple
                    if state in {"ready", "no-estabelecimentos"}:
                        return applied_multiple
                    if state in {"no-filter", "missing-content"}:
                        return False
                    await asyncio.sleep(0.5)
                if found_filter:
                    raise RuntimeError(
                        f"A Caixa não concluiu a aplicação do filtro de estabelecimentos na aba {tab_id}."
                    )
                return False

            async def list_establishment_filter_options(
                session_id: str,
                tab_id: str,
                timeout: float = 25.0,
            ) -> list[str]:
                expression = f"""
                (() => {{
                    const visible = (el) => {{
                        if (!el) return false;
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const content = document.querySelector("#{tab_id}Content [role='tabpanel']");
                    if (!content || content.getAttribute('aria-hidden') === 'true') return '';
                    const filterTrigger = [
                        ...content.querySelectorAll(
                            '[data-testid="vendas-hoje-link-filtrar"], [data-testid="historico-vendas-container-filtros"], [data-testid*="container-filtros"], [data-testid*="link-filtrar"]'
                        )
                    ].find(visible);
                    const sidebar = [
                        ...document.querySelectorAll('aside.osui-sidebar, [role="complementary"]')
                    ].find((el) => visible(el) && (
                        el.querySelector('[data-testid="generic-filter-btn-resultados"]') ||
                        el.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]')
                    ));
                    if (!filterTrigger && !sidebar) return JSON.stringify([]);
                    if (!sidebar) {{
                        if (!filterTrigger) return JSON.stringify([]);
                        filterTrigger.scrollIntoView({{ block: 'center', inline: 'center' }});
                        filterTrigger.click();
                        return '';
                    }}
                    const title = sidebar.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]');
                    if (!title) return JSON.stringify([]);
                    const titleWrapper = title.closest('[role="button"]') || title.closest('.osui-accordion-item__title') || title;
                    const accordionItem = title.closest('.osui-accordion-item');
                    const contentWrapper = accordionItem
                        ? accordionItem.querySelector('.osui-accordion-item__content, [id$="ContentWrapper"]')
                        : null;
                    const collapsed = Boolean(
                        contentWrapper && (
                            contentWrapper.getAttribute('aria-hidden') === 'true' ||
                            String(contentWrapper.className || '').includes('--is-collapsed')
                        )
                    );
                    if (collapsed) {{
                        titleWrapper.scrollIntoView({{ block: 'center', inline: 'center' }});
                        titleWrapper.click();
                        return '';
                    }}
                    const options = [
                        ...sidebar.querySelectorAll('[data-testid^="generic-filter-check-estabelecimento-"]')
                    ]
                        .filter((el) => !el.disabled)
                        .map((el) => String(el.getAttribute('data-testid') || '').replace('generic-filter-check-estabelecimento-', '').trim())
                        .filter(Boolean);
                    return JSON.stringify(options);
                }})()
                """
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    raw = await eval_js(session_id, expression, timeout=15.0)
                    text = str(raw or "").strip()
                    if not text:
                        await asyncio.sleep(0.5)
                        continue
                    try:
                        options = json.loads(text)
                    except Exception:
                        options = []
                    if isinstance(options, list):
                        return [str(item).strip() for item in options if str(item).strip()]
                    return []
                return []

            async def apply_establishment_filter_selection(
                session_id: str,
                tab_id: str,
                selected_ids: list[str],
                timeout: float = 25.0,
            ) -> int:
                desired_ids = [str(item).strip() for item in selected_ids if str(item).strip()]
                if not desired_ids:
                    return 0
                desired_ids_js = json.dumps(desired_ids, ensure_ascii=False)
                expression = f"""
                (() => {{
                    const desired = new Set({desired_ids_js});
                    const visible = (el) => {{
                        if (!el) return false;
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const content = document.querySelector("#{tab_id}Content [role='tabpanel']");
                    if (!content || content.getAttribute('aria-hidden') === 'true') return 'missing-content';
                    const filterTrigger = [
                        ...content.querySelectorAll(
                            '[data-testid="vendas-hoje-link-filtrar"], [data-testid="historico-vendas-container-filtros"], [data-testid*="container-filtros"], [data-testid*="link-filtrar"]'
                        )
                    ].find(visible);
                    const sidebar = [
                        ...document.querySelectorAll('aside.osui-sidebar, [role="complementary"]')
                    ].find((el) => visible(el) && (
                        el.querySelector('[data-testid="generic-filter-btn-resultados"]') ||
                        el.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]')
                    ));
                    if (!filterTrigger && !sidebar) return 'no-filter';
                    if (!sidebar) {{
                        if (!filterTrigger) return 'no-filter';
                        filterTrigger.scrollIntoView({{ block: 'center', inline: 'center' }});
                        filterTrigger.click();
                        return 'opening';
                    }}
                    const title = sidebar.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]');
                    if (!title) return 'no-estabelecimentos';
                    const titleWrapper = title.closest('[role="button"]') || title.closest('.osui-accordion-item__title') || title;
                    const accordionItem = title.closest('.osui-accordion-item');
                    const contentWrapper = accordionItem
                        ? accordionItem.querySelector('.osui-accordion-item__content, [id$="ContentWrapper"]')
                        : null;
                    const collapsed = Boolean(
                        contentWrapper && (
                            contentWrapper.getAttribute('aria-hidden') === 'true' ||
                            String(contentWrapper.className || '').includes('--is-collapsed')
                        )
                    );
                    if (collapsed) {{
                        titleWrapper.scrollIntoView({{ block: 'center', inline: 'center' }});
                        titleWrapper.click();
                        return 'expanding';
                    }}
                    const establishmentChecks = [
                        ...sidebar.querySelectorAll('[data-testid^="generic-filter-check-estabelecimento-"]')
                    ]
                        .filter((el) => !el.disabled)
                        .map((el) => {{
                            const value = String(el.getAttribute('data-testid') || '').replace('generic-filter-check-estabelecimento-', '').trim();
                            return {{ el, value }};
                        }})
                        .filter((entry) => entry.value);
                    if (!establishmentChecks.length) return 'no-estabelecimentos';
                    const needsToggle = establishmentChecks.filter((entry) => desired.has(entry.value) !== entry.el.checked);
                    if (needsToggle.length) {{
                        needsToggle[0].el.click();
                        return 'toggling';
                    }}
                    const applyButton = sidebar.querySelector('[data-testid="generic-filter-btn-resultados"]');
                    if (!applyButton || !visible(applyButton) || applyButton.disabled) return 'ready';
                    applyButton.click();
                    return 'applied';
                }})()
                """
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    state = str(await eval_js(session_id, expression, timeout=15.0) or "").strip()
                    if state in {"opening", "expanding", "toggling"}:
                        await asyncio.sleep(0.5)
                        continue
                    if state == "applied":
                        try:
                            await wait_for_condition(
                                session_id,
                                """
                                (() => {
                                    const visible = (el) => {
                                        if (!el) return false;
                                        const rect = el.getBoundingClientRect();
                                        const style = getComputedStyle(el);
                                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                    };
                                    const sidebar = [
                                        ...document.querySelectorAll('aside.osui-sidebar, [role="complementary"]')
                                    ].find((el) => visible(el) && (
                                        el.querySelector('[data-testid="generic-filter-btn-resultados"]') ||
                                        el.querySelector('[data-testid="generic-filter-accordion-title-estabelecimentos"]')
                                    ));
                                    return !sidebar;
                                })()
                                """,
                                timeout=15.0,
                                step=0.25,
                            )
                        except Exception:
                            pass
                        await wait_for_portal_settle(
                            session_id,
                            tab_id=tab_id,
                            timeout=20.0,
                            context_label=f"aplicar o estabelecimento {', '.join(desired_ids)} na aba {tab_id}",
                        )
                        return len(desired_ids)
                    if state in {"ready", "no-estabelecimentos"}:
                        return len(desired_ids)
                    if state in {"no-filter", "missing-content"}:
                        return 0
                    await asyncio.sleep(0.5)
                raise RuntimeError(
                    f"A Caixa nao concluiu a selecao de estabelecimento(s) na aba {tab_id}."
                )

            async def wait_for_export_ready(
                session_id: str,
                kind: str,
                *,
                tab_id: str | None = None,
                timeout: float = 60.0,
            ) -> None:
                export_selector = '[data-testid="exportar-pix-van"]' if kind == "pix" else '[data-testid^="exportar-"]'
                content_id = f"{tab_id}Content" if tab_id else ("PixContent" if kind == "pix" else "HistoricoVendasContent")
                expression = f"""
                (() => {{
                    const text = (document.body?.innerText || '')
                        .normalize('NFD')
                        .replace(/[\\u0300-\\u036f]/g, '')
                        .toUpperCase();
                    const href = String(location.href || '').toUpperCase();
                    if (href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST')) return 'portal_error';
                    const content = document.querySelector("#{content_id} [role='tabpanel']");
                    if (!content || content.getAttribute('aria-hidden') === 'true') return '';
                    const visible = (el) => {{
                        if (!el) return false;
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const busyNodes = [...content.querySelectorAll('[aria-busy="true"], .ph-item, .ph-picture, .ph-picture-small, .spinner-border, .spinner-grow, .loading, .skeleton, .ant-skeleton')]
                        .filter(visible);
                    if (busyNodes.length) return '';
                    const exportBtn = [...content.querySelectorAll({export_selector!r})].find(visible);
                    if (!exportBtn) return '';
                    return !exportBtn.disabled ? 'ready' : '';
                }})()
                """
                try:
                    state = await wait_for_condition(
                        session_id,
                        expression,
                        timeout=timeout,
                        step=0.5,
                    )
                    if state == "ready":
                        return
                except Exception:
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_export_ready_debug_{kind}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    try:
                        state_debug = await eval_js(
                            session_id,
                            f"""
                            (() => {{
                                const content = document.querySelector("#{content_id} [role='tabpanel']");
                                const exportBtn = content ? [...content.querySelectorAll({export_selector!r})].find((el) => {{
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                }}) : null;
                                const placeholderNodes = content ? [...content.querySelectorAll('.ph-item, .ph-picture, .ph-picture-small')] : [];
                                return {{
                                    contentFound: !!content,
                                    contentHidden: content ? content.getAttribute('aria-hidden') : null,
                                    exportFound: !!exportBtn,
                                    exportDisabled: exportBtn ? !!exportBtn.disabled : null,
                                    exportText: exportBtn ? (exportBtn.innerText || exportBtn.textContent || '').trim() : '',
                                    placeholderCount: placeholderNodes.length,
                                    visibleButtons: [...document.querySelectorAll('button, a, [role="button"]')].map((el) => {{
                                        const rect = el.getBoundingClientRect();
                                        const style = getComputedStyle(el);
                                        return {{
                                            text: (el.innerText || el.textContent || '').trim(),
                                            testid: el.getAttribute('data-testid') || '',
                                            disabled: !!el.disabled,
                                            visible: rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none',
                                        }};
                                    }}).filter((item) => item.visible),
                                }};
                            }})()
                            """,
                            timeout=15.0,
                        )
                        if state_debug is not None:
                            debug_state_path = artifacts_dir / f"azulzinha_export_ready_state_{kind}.json"
                            debug_state_path.write_text(json.dumps(state_debug, ensure_ascii=False, indent=2), encoding="utf-8")
                    except Exception:
                        pass
                    raise
                try:
                    html_debug = await eval_js(
                        session_id,
                        "document.documentElement ? document.documentElement.outerHTML : ''",
                        timeout=15.0,
                    )
                    if html_debug:
                        debug_path = artifacts_dir / f"azulzinha_export_error_{kind}.html"
                        debug_path.write_text(str(html_debug), encoding="utf-8")
                except Exception:
                    pass
                raise RuntimeError(
                    f"A Caixa abriu a pagina de erro ao preparar a exportacao do relatorio de {'PIX' if kind == 'pix' else 'cartoes'}."
                )

            async def tab_has_no_results(
                session_id: str,
                tab_id: str,
                timeout: float = 6.0,
            ) -> bool:
                content_id = f"{tab_id}Content"
                expression = f"""
                (() => {{
                    const content = document.querySelector("#{content_id} [role='tabpanel']");
                    if (!content || content.getAttribute('aria-hidden') === 'true') return '';
                    const visible = (el) => {{
                        if (!el) return false;
                        const rect = el.getBoundingClientRect();
                        const style = getComputedStyle(el);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                    }};
                    const busyNodes = [...content.querySelectorAll('[aria-busy="true"], .ph-item, .ph-picture, .ph-picture-small, .spinner-border, .spinner-grow, .loading, .skeleton, .ant-skeleton')]
                        .filter(visible);
                    if (busyNodes.length) return '';
                    const text = (content.innerText || content.textContent || '')
                        .normalize('NFD')
                        .replace(/[\\u0300-\\u036f]/g, '')
                        .replace(/\\s+/g, ' ')
                        .toLowerCase();
                    if (/nenhum resultado|sem resultado|nao encontramos|nenhuma venda|tente filtrar por outros periodos/.test(text)) {{
                        return 'no-results';
                    }}
                    return 'has-results';
                }})()
                """
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    state = str(await eval_js(session_id, expression, timeout=10.0) or "").strip()
                    if state == "no-results":
                        return True
                    if state == "has-results":
                        return False
                    await asyncio.sleep(0.3)
                return False

            async def click_export(session_id: str, kind: str, tab_id: str | None = None) -> None:
                tab_content_selector = f"#{tab_id}Content [role='tabpanel']" if tab_id else None
                await eval_js(
                    session_id,
                    """
                    (() => {
                        if (window.__codexExportHookInstalled) {
                            if (window.__codexExportSignals) {
                                window.__codexExportSignals.openedUrls = [];
                                window.__codexExportSignals.anchorUrls = [];
                                window.__codexExportSignals.iframeUrls = [];
                                window.__codexExportSignals.lastUrl = '';
                            }
                            return true;
                        }
                        const data = window.__codexExportSignals = {
                            openedUrls: [],
                            anchorUrls: [],
                            iframeUrls: [],
                            lastUrl: '',
                        };
                        const pushUrl = (value) => {
                            const text = String(value || '').trim();
                            if (!text) return;
                            data.lastUrl = text;
                            if (/^https?:/i.test(text) || text.startsWith('/')) {
                                data.openedUrls.push(text);
                            }
                        };
                        const originalOpen = window.open;
                        window.open = function(url, ...args) {
                            pushUrl(url);
                            return originalOpen ? originalOpen.call(this, url, ...args) : null;
                        };
                        const anchorClick = HTMLAnchorElement.prototype.click;
                        HTMLAnchorElement.prototype.click = function(...args) {
                            pushUrl(this.href || this.getAttribute('href') || '');
                            return anchorClick.apply(this, args);
                        };
                        const observer = new MutationObserver(() => {
                            document.querySelectorAll('iframe, embed, object, a[href], a[download]').forEach((el) => {
                                const url = el.src || el.data || el.href || el.getAttribute('href') || '';
                                if (!url) return;
                                if (el.tagName === 'A') data.anchorUrls.push(url);
                                else data.iframeUrls.push(url);
                                data.lastUrl = String(url);
                            });
                        });
                        observer.observe(document.documentElement || document.body, { childList: true, subtree: true, attributes: true, attributeFilter: ['src', 'data', 'href'] });
                        window.__codexExportHookInstalled = true;
                        return true;
                    })()
                    """,
                )
                await eval_js(
                    session_id,
                    """
                    (() => {
                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                        const visible = (el) => {
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const buttons = [...document.querySelectorAll('button, a, [role="button"], div.btn')].filter(visible);
                        const applyButton = buttons.find((el) => {
                            const text = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || '');
                            return text.includes('MOSTRAR RESULTADOS') || text === 'APLICAR';
                        });
                        if (!applyButton) return false;
                        applyButton.scrollIntoView({ block: 'center', inline: 'center' });
                        applyButton.click();
                        return true;
                    })()
                    """,
                )
                try:
                    await wait_for_export_ready(session_id, kind, tab_id=tab_id, timeout=45.0)
                except Exception:
                    pass
                direct_selectors = (
                    ['button[data-testid="exportar-pix-van"]', '[data-testid="exportar-pix-van"]']
                    if kind == "pix"
                    else [
                        'button[data-testid="exportar-historicovendas"]',
                        '[data-testid="exportar-historicovendas"]',
                        'button[data-testid^="exportar-"]',
                        '[data-testid^="exportar-"]',
                    ]
                )
                for selector in direct_selectors:
                    if await click_selector_native(session_id, selector, root_selector=tab_content_selector):
                        if kind == "pix":
                            try:
                                await wait_for_condition(
                                    session_id,
                                    """
                                    (() => {
                                        const text = (document.body?.innerText || '')
                                            .normalize('NFD')
                                            .replace(/[\\u0300-\\u036f]/g, '')
                                            .toUpperCase();
                                        return text.includes('ESCOLHA COMO DESEJA EXPORTAR O RELATORIO') ||
                                            !!document.querySelector('[data-testid="pix-van-gerar-arquivo"]');
                                    })()
                                    """,
                                    timeout=8.0,
                                    step=0.25,
                                )
                                await eval_js(
                                    session_id,
                                    """
                                    (() => {
                                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                                        const visible = (el) => {
                                            const rect = el.getBoundingClientRect();
                                            const style = getComputedStyle(el);
                                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                        };
                                        const all = [...document.querySelectorAll('button, a, [role="button"], [role="option"], [role="menuitem"], label, div, span')].filter(visible);
                                        const openSelector = all.find((el) => {
                                            const text = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || '');
                                            return text.includes('TIPO DE ARQUIVO') || text === 'EXCEL' || text.includes('FORMATO');
                                        });
                                        (openSelector?.closest('button, a, [role="button"], label, div, span') || openSelector)?.click();
                                        return true;
                                    })()
                                    """,
                                )
                                await asyncio.sleep(0.5)
                                await eval_js(
                                    session_id,
                                    """
                                    (() => {
                                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                                        const visible = (el) => {
                                            const rect = el.getBoundingClientRect();
                                            const style = getComputedStyle(el);
                                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                        };
                                        const excelNode = [...document.querySelectorAll('button, a, [role="button"], [role="option"], [role="menuitem"], label, div, span, input')]
                                            .filter(visible)
                                            .find((el) => {
                                                const text = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || el.getAttribute('value') || '');
                                                const attrs = norm(`${el.id || ''} ${el.name || ''} ${el.value || ''}`);
                                                return (
                                                    text === 'EXCEL' ||
                                                    text.includes('XLSX') ||
                                                    text.includes('PLANILHA') ||
                                                    attrs.includes('EXCEL') ||
                                                    attrs.includes('XLSX')
                                                );
                                            });
                                        const target = excelNode?.closest('button, a, [role="button"], [role="option"], [role="menuitem"], label, div, span') || excelNode;
                                        target?.click();
                                        if (excelNode && excelNode.tagName === 'INPUT') {
                                            excelNode.checked = true;
                                            excelNode.dispatchEvent(new Event('input', { bubbles: true }));
                                            excelNode.dispatchEvent(new Event('change', { bubbles: true }));
                                        }
                                        return !!target;
                                    })()
                                    """,
                                )
                                await asyncio.sleep(0.6)
                                clicked_generate = await click_selector_native(session_id, '[data-testid="pix-van-gerar-arquivo"]')
                                if not clicked_generate:
                                    clicked_generate = await click_by_text(session_id, ["Gerar arquivo", "Baixar arquivo", "Download"], timeout=4.0)
                                if clicked_generate:
                                    await asyncio.sleep(1.0)
                                    return
                                raise RuntimeError("Não foi possível confirmar a geração do arquivo PIX na Azulzinha/Caixa.")
                            except Exception:
                                pass
                            await asyncio.sleep(1.0)
                            continue
                        else:
                            try:
                                await wait_for_condition(
                                    session_id,
                                    """
                                    (() => {
                                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                                        const visible = (el) => {
                                            const rect = el.getBoundingClientRect();
                                            const style = getComputedStyle(el);
                                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                        };
                                        const text = norm(document.body?.innerText || '');
                                        if (text.includes('ESCOLHA COMO DESEJA EXPORTAR')) return true;
                                        return [...document.querySelectorAll('button, a, [role="button"]')]
                                            .filter(visible)
                                            .some((el) => {
                                                const value = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || el.title || '');
                                                return value.includes('PDF') || value.includes('GERAR ARQUIVO') || value.includes('BAIXAR ARQUIVO');
                                            });
                                    })()
                                    """,
                                    timeout=6.0,
                                    step=0.25,
                                )
                                await asyncio.sleep(0.5)
                                await eval_js(
                                    session_id,
                                    """
                                    (() => {
                                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                                        const visible = (el) => {
                                            const rect = el.getBoundingClientRect();
                                            const style = getComputedStyle(el);
                                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                        };
                                        const clickBest = (targets) => {
                                            const nodes = [...document.querySelectorAll('button, a, [role="button"], label, div, span')].filter(visible);
                                            for (const target of targets) {
                                                const node = nodes.find((el) => norm(el.innerText || el.textContent || el.getAttribute('aria-label') || '').includes(target));
                                                if (node) {
                                                    (node.closest('button, a, [role="button"], label, div') || node).click();
                                                    return true;
                                                }
                                            }
                                            return false;
                                        };
                                        return (
                                            clickBest(['PDF']) ||
                                            clickBest(['EXCEL', 'XLSX', 'PLANILHA']) ||
                                            false
                                        );
                                    })()
                                    """,
                                )
                                await asyncio.sleep(0.7)
                                if not await click_selector_native(session_id, '[data-testid*="gerar-arquivo"]'):
                                    if not await click_selector_native(session_id, '[data-testid*="baixar-arquivo"]'):
                                        if not await click_selector_native(session_id, '[data-testid*="download"]'):
                                            await click_by_text(session_id, ["Gerar arquivo", "Baixar arquivo", "Download"], timeout=4.0)
                                await asyncio.sleep(1.0)
                                return
                            except Exception:
                                continue
                clicked = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                        const visible = (el) => {{
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const wantCsv = {kind == 'pix'};
                        const directSelectors = wantCsv
                            ? ['button[data-testid="exportar-pix-van"]', '[data-testid="exportar-pix-van"]']
                            : ['button[data-testid^="exportar-"]', '[data-testid^="exportar-"]'];
                        const root = {tab_content_selector!r} ? document.querySelector({tab_content_selector!r}) : document;
                        if (!root) return false;
                        const explicit = directSelectors
                            .flatMap((selector) => [...root.querySelectorAll(selector)])
                            .find((el) => el && !el.disabled && visible(el));
                        if (explicit) {{
                            explicit.scrollIntoView({{ block: 'center', inline: 'center' }});
                            explicit.dispatchEvent(new MouseEvent('mousedown', {{ bubbles: true, cancelable: true, view: window }}));
                            explicit.click();
                            explicit.dispatchEvent(new MouseEvent('mouseup', {{ bubbles: true, cancelable: true, view: window }}));
                            return true;
                        }}
                        const buttons = [...root.querySelectorAll('button, a, [role="button"]')].filter(visible);
                        const preferred = buttons.find((el) => {{
                            const text = norm(el.innerText || el.textContent || el.getAttribute('aria-label') || el.getAttribute('mattooltip') || el.title || '');
                            return !el.disabled && (text.includes('EXPORTAR') || text.includes('IMPRIMIR') || text.includes(wantCsv ? 'CSV' : 'PDF'));
                        }}) || buttons.find((el) => {{
                            const text = norm(el.getAttribute('aria-label') || el.getAttribute('mattooltip') || el.title || '');
                            return !el.disabled && (wantCsv ? text.includes('CSV') || text.includes('DATABASE') : text.includes('PDF') || text.includes('DOWNLOAD'));
                        }});
                        if (!preferred) return false;
                        preferred.scrollIntoView({{ block: 'center', inline: 'center' }});
                        preferred.click();
                        return true;
                    }})()
                    """,
                )
                if not clicked:
                    try:
                        state_debug = await eval_js(
                            session_id,
                            """
                            (() => {
                                const items = [...document.querySelectorAll('button, a, [role="button"]')].map((el) => {
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return {
                                        tag: el.tagName,
                                        text: (el.innerText || el.textContent || '').trim(),
                                        testid: el.getAttribute('data-testid') || '',
                                        disabled: !!el.disabled,
                                        ariaLabel: el.getAttribute('aria-label') || '',
                                        title: el.title || '',
                                        visible: rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none',
                                        width: rect.width,
                                        height: rect.height,
                                    };
                                });
                                return items.filter((item) =>
                                    (item.testid || '').toLowerCase().includes('export') ||
                                    (item.text || '').toUpperCase().includes('EXPORT') ||
                                    (item.text || '').toUpperCase().includes('CSV') ||
                                    (item.text || '').toUpperCase().includes('PDF')
                                );
                            })()
                            """,
                            timeout=15.0,
                        )
                        if state_debug is not None:
                            debug_state_path = artifacts_dir / f"azulzinha_export_state_{kind}.json"
                            debug_state_path.write_text(json.dumps(state_debug, ensure_ascii=False, indent=2), encoding="utf-8")
                    except Exception:
                        pass
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_export_debug_{kind}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    raise RuntimeError("Não foi possível acionar o botão de exportação no portal Azulzinha/Caixa.")

            async def ensure_login(session_id: str, auth_restart_count: int = 0) -> None:
                _emit_pix_status(on_status, "Acessando Azulzinha/Caixa...")
                await navigate(session_id, credenciais["login_url"])
                if await eval_js(
                    session_id,
                    """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const hasSalesTabs = Boolean(
                            document.querySelector('header[role="tablist"]') ||
                            document.querySelector('#HistoricoVendas button[role="tab"]') ||
                            document.querySelector('#Pix button[role="tab"]')
                        );
                        const onLoginPage = (
                            visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                            visible(document.querySelector('#b2-b1-Input_Password'))
                        ) || text.includes('ACESSE SUA CONTA');
                        return !onLoginPage && (
                            hasSalesTabs ||
                            text.includes('HISTORICO DE VENDAS') ||
                            text.includes('PAGAMENTO INSTANTANEO') ||
                            text.includes('PIX')
                        );
                    })()
                    """,
                ):
                    return
                _emit_pix_status(on_status, "Autenticando na Azulzinha/Caixa...")
                login_selectors = await wait_for_condition(
                    session_id,
                    """
                    (() => {
                        const visible = (el) => {
                            if (!el || el.disabled) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const userCandidates = [
                            document.querySelector('#b2-b1-b4-InputMask'),
                            ...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])'),
                        ].filter(visible);
                        const passwordCandidates = [
                            document.querySelector('#b2-b1-Input_Password'),
                            ...document.querySelectorAll('input[type="password"]'),
                        ].filter(visible);
                        const user = userCandidates[0];
                        const password = passwordCandidates[0];
                        if (!user || !password) return null;
                        user.setAttribute('data-codex-login-user', '1');
                        password.setAttribute('data-codex-login-pass', '1');
                        return {
                            user: user.id ? `#${user.id}` : '[data-codex-login-user="1"]',
                            password: password.id ? `#${password.id}` : '[data-codex-login-pass="1"]',
                        };
                    })()
                    """,
                    timeout=60.0,
                    description="A Caixa não exibiu a tela de login para informar CNPJ e senha",
                )
                login_user_selector = str((login_selectors or {}).get("user") or "#b2-b1-b4-InputMask")
                login_password_selector = str((login_selectors or {}).get("password") or "#b2-b1-Input_Password")
                cnpj_digits = re.sub(r"\D", "", str(credenciais["cnpj"] or ""))
                password_text = str(credenciais["password"] or "")
                try:
                    await insert_text(session_id, login_user_selector, cnpj_digits)
                except Exception:
                    pass
                try:
                    await insert_text(session_id, login_password_selector, password_text)
                except Exception:
                    pass
                await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const currentDigits = (el) => String(el?.value || el?.getAttribute('value') || '').replace(/\\D/g, '');
                        const currentValue = (el) => String(el?.value || el?.getAttribute('value') || '');
                        const setNativeValue = (el, value) => {{
                            const proto = el instanceof HTMLTextAreaElement ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
                            const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
                            if (setter) setter.call(el, value); else el.value = value;
                            el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            el.dispatchEvent(new KeyboardEvent('keyup', {{ bubbles: true, key: '0' }}));
                            el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                        }};
                        const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                        const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                        if (!user || !password) return false;
                        user.focus();
                        setNativeValue(user, {cnpj_digits!r});
                        password.focus();
                        setNativeValue(password, {password_text!r});
                        return true;
                    }})()
                    """,
                    timeout=15.0,
                )
                credential_fill_state = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                        const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                        const userValue = String(user?.value || user?.getAttribute('value') || '').replace(/\\D/g, '');
                        const passwordValue = String(password?.value || password?.getAttribute('value') || '');
                        return {{
                            userLen: userValue.length,
                            passwordLen: passwordValue.length,
                        }};
                    }})()
                    """,
                ) or {}
                if int(credential_fill_state.get("userLen") or 0) < len(cnpj_digits) or int(credential_fill_state.get("passwordLen") or 0) < len(password_text):
                    await eval_js(
                        session_id,
                        f"""
                        (() => {{
                            const visible = (el) => {{
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            }};
                            const setNativeValue = (el, value) => {{
                                const proto = el instanceof HTMLTextAreaElement ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
                                const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
                                if (setter) setter.call(el, value); else el.value = value;
                                el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                                el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                                el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                            }};
                            const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                            const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                            if (!user || !password) return false;
                            user.focus();
                            setNativeValue(user, {cnpj_digits!r});
                            password.focus();
                            setNativeValue(password, {password_text!r});
                            return true;
                        }})()
                        """,
                    )
                credential_fill_state = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                        const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                        const userValue = String(user?.value || user?.getAttribute('value') || '').replace(/\\D/g, '');
                        const passwordValue = String(password?.value || password?.getAttribute('value') || '');
                        return {{
                            userLen: userValue.length,
                            passwordLen: passwordValue.length,
                        }};
                    }})()
                    """,
                ) or {}
                if int(credential_fill_state.get("userLen") or 0) < len(cnpj_digits) or int(credential_fill_state.get("passwordLen") or 0) < len(password_text):
                    await capture_portal_html_debug_v2(session_id, "azulzinha_login_fill_debug.html")
                    raise RuntimeError("Não foi possível preencher o login e a senha da Azulzinha/Caixa.")
                await press_tab(session_id)
                await wait_for_condition(
                    session_id,
                    """
                    (() => {
                        const botao = document.querySelector('#b2-b1-confirmar');
                        return botao && !botao.disabled;
                    })()
                    """,
                    timeout=20.0,
                )
                clicou = await eval_js(
                    session_id,
                    """
                    (() => {
                        const botao = document.querySelector('#b2-b1-confirmar');
                        if (!botao || botao.disabled) return false;
                        botao.click();
                        return true;
                    })()
                    """,
                )
                if not clicou:
                    raise RuntimeError("Não foi possível confirmar o login da Azulzinha/Caixa.")

                state = await wait_for_condition(
                    session_id,
                    """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const hasSalesTabs = Boolean(
                            document.querySelector('header[role="tablist"]') ||
                            document.querySelector('#HistoricoVendas button[role="tab"]') ||
                            document.querySelector('#Pix button[role="tab"]')
                        );
                        const onLoginPage = (
                            visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                            visible(document.querySelector('#b2-b1-Input_Password'))
                        ) || text.includes('ACESSE SUA CONTA');
                        const tokenInputs = [...document.querySelectorAll('input')].filter((el) => {
                            const type = (el.type || '').toLowerCase();
                            return type !== 'hidden' && type !== 'password' && !el.disabled && visible(el);
                        });
                        if (!onLoginPage && (hasSalesTabs || text.includes('HISTORICO DE VENDAS') || text.includes('PAGAMENTO INSTANTANEO') || text.includes('PIX'))) return 'logged';
                        if (!onLoginPage && text.includes('SELECIONE O DISPOSITIVO')) return 'device';
                        if (!onLoginPage && (text.includes('ESCOLHA POR ONDE DESEJA RECEBER') || text.includes('RECEBER POR E-MAIL') || text.includes('@GMAIL.COM'))) return 'token';
                        if (!onLoginPage && tokenInputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO'))) return 'token';
                        return '';
                    })()
                    """,
                    timeout=90.0,
                    description="A Caixa não concluiu a etapa inicial do login",
                )
                if state == "logged":
                    return
                if state == "device":
                    _emit_pix_status(on_status, "Selecionando dispositivo da Caixa...")
                    if not await click_card_by_text(session_id, _azulzinha_device_aliases(company_label), timeout=30.0):
                        raise RuntimeError(f"Não foi possível selecionar o dispositivo da {company_label} na Azulzinha/Caixa.")
                    state = await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const visible = (el) => {
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const hasSalesTabs = Boolean(
                                document.querySelector('header[role="tablist"]') ||
                                document.querySelector('#HistoricoVendas button[role="tab"]') ||
                                document.querySelector('#Pix button[role="tab"]')
                            );
                            const onLoginPage = (
                                visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                                visible(document.querySelector('#b2-b1-Input_Password'))
                            ) || text.includes('ACESSE SUA CONTA');
                            const tokenInputs = [...document.querySelectorAll('input')].filter((el) => {
                                const type = (el.type || '').toLowerCase();
                                return type !== 'hidden' && type !== 'password' && !el.disabled && visible(el);
                            });
                            if (!onLoginPage && (hasSalesTabs || text.includes('HISTORICO DE VENDAS') || text.includes('PAGAMENTO INSTANTANEO') || text.includes('PIX'))) return 'logged';
                            if (!onLoginPage && text.includes('INFORME O TOKEN DO APLICATIVO')) return 'token_app';
                            if (!onLoginPage && (text.includes('ESCOLHA POR ONDE DESEJA RECEBER') || text.includes('RECEBER POR E-MAIL') || text.includes('@GMAIL.COM'))) return 'token_delivery';
                            if (!onLoginPage && tokenInputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO'))) return 'token';
                            return '';
                        })()
                        """,
                        timeout=45.0,
                        description="A Caixa não avançou após a seleção do dispositivo",
                    )
                if state == "logged":
                    return

                async def request_token_via_email(session_id: str, current_state: str | None = None) -> str:
                    state_local = str(current_state or "").strip()
                    if state_local in {"token", "token_app"}:
                        token_screen_ready = await eval_js(
                            session_id,
                            """
                            (() => {
                                const text = (document.body?.innerText || '')
                                    .normalize('NFD')
                                    .replace(/[\u0300-\u036f]/g, '')
                                    .toUpperCase();
                                const visible = (el) => {
                                    if (!el) return false;
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                };
                                const onLoginPage = (
                                    visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                                    visible(document.querySelector('#b2-b1-Input_Password'))
                                ) || text.includes('ACESSE SUA CONTA');
                                const tokenInputs = [...document.querySelectorAll('input')].filter((el) => {
                                    const type = (el.type || '').toLowerCase();
                                    return type !== 'hidden' && type !== 'password' && !el.disabled && visible(el);
                                });
                                return !onLoginPage && (
                                    text.includes('ESCOLHA POR ONDE DESEJA RECEBER') ||
                                    text.includes('RECEBER POR E-MAIL') ||
                                    text.includes('@GMAIL.COM') ||
                                    (tokenInputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO')))
                                );
                            })()
                            """,
                        )
                        if not token_screen_ready:
                            state_local = ""
                    if state_local in {"token", "token_app"}:
                        abriu = await eval_js(
                            session_id,
                            """
                            (() => {
                                const link = document.querySelector('a.bold.font-universe.cor-preto');
                                if (!link) return false;
                                link.click();
                                return true;
                            })()
                            """,
                        )
                        if not abriu and not await click_by_text(
                            session_id,
                            [
                                "Receber codigo por e-mail ou SMS",
                                "Receber código por e-mail ou SMS",
                                "Reenviar codigo",
                                "Reenviar token",
                            ],
                            timeout=20.0,
                        ):
                            return state_local
                        state_local = await wait_for_condition(
                            session_id,
                            """
                            (() => {
                                const text = (document.body?.innerText || '').toUpperCase();
                                const inputs = [...document.querySelectorAll('input')]
                                    .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                                if (text.includes('ESCOLHA POR ONDE DESEJA RECEBER')) return 'token_delivery';
                                if (text.includes('RECEBER POR E-MAIL') || text.includes('@GMAIL.COM')) return 'token_delivery';
                                if (inputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO'))) return 'token';
                                return '';
                            })()
                            """,
                            timeout=30.0,
                        )
                        await asyncio.sleep(1.0)

                    if state_local == "token_delivery":
                        selecionou_email = await eval_js(
                            session_id,
                            """
                            (() => {
                                const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                                const visible = (el) => {
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                };
                                const candidates = [...document.querySelectorAll('[id$="-Content"], .card-content, .ph.card.card-content')]
                                    .filter(visible)
                                    .map((el) => {
                                        const text = norm(el.innerText || el.textContent || '');
                                        if (!text.includes('RECEBER POR E-MAIL') && !text.includes('@GMAIL.COM')) return null;
                                        const className = (el.className || '').toString().toUpperCase();
                                        const isCard = className.includes('CARD-CONTENT') || className.includes('PH CARD');
                                        const textLength = text.length || 9999;
                                        return { el, score: (isCard ? 1000 : 0) - textLength };
                                    })
                                    .filter(Boolean)
                                    .sort((a, b) => b.score - a.score);
                                const match = candidates.length ? candidates[0].el : null;
                                if (!match) return false;
                                const text = norm(match.innerText || match.textContent || '');
                                if (!text.includes('RECEBER POR E-MAIL') && !text.includes('@GMAIL.COM')) return false;
                                const clickable = match.closest('[id$="-Content"], .card-content, .ph.card.card-content') || match;
                                clickable.scrollIntoView({ block: 'center', inline: 'center' });
                                clickable.click();
                                return true;
                            })()
                            """,
                        )
                        if not selecionou_email and not await click_card_by_text(session_id, ["RECEBER POR E-MAIL", "@GMAIL.COM"], timeout=20.0):
                            if not await click_by_text(session_id, ["Receber por e-mail", "@gmail.com"], timeout=20.0):
                                raise RuntimeError("Nao foi possivel selecionar o envio do token por e-mail na Azulzinha/Caixa.")
                        await asyncio.sleep(1.0)
                        await wait_for_condition(
                            session_id,
                            """
                            (() => {
                                const text = (document.body?.innerText || '')
                                    .normalize('NFD')
                                    .replace(/[\\u0300-\\u036f]/g, '')
                                    .toUpperCase();
                                const inputs = [...document.querySelectorAll('input')].filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                                return inputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO'));
                            })()
                            """,
                            timeout=30.0,
                        )
                        return "token"

                    return state_local

                token_email_grace_seconds = 15.0

                async def wait_for_token_email_delivery_grace() -> None:
                    _emit_pix_status(
                        on_status,
                        f"Aguardando {int(token_email_grace_seconds)}s para o e-mail do token chegar...",
                    )
                    await asyncio.sleep(token_email_grace_seconds)

                _emit_pix_status(on_status, "Solicitando token por e-mail...")
                token_requested_at = time.time()
                state = await request_token_via_email(session_id, state)
                if state == "token":
                    await wait_for_token_email_delivery_grace()
                if False and state in {"token", "token_app"}:
                    abriu = await eval_js(
                        session_id,
                        """
                        (() => {
                            const link = document.querySelector('a.bold.font-universe.cor-preto');
                            if (!link) return false;
                            link.click();
                            return true;
                        })()
                        """,
                    )
                    if not abriu and not await click_by_text(
                        session_id,
                        [
                            "Receber codigo por e-mail ou SMS",
                            "Receber código por e-mail ou SMS",
                        ],
                        timeout=20.0,
                    ):
                        raise RuntimeError("Nao foi possivel abrir a escolha de envio do token na Azulzinha/Caixa.")
                    state = await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '').toUpperCase();
                            if (text.includes('ESCOLHA POR ONDE DESEJA RECEBER')) return 'token_delivery';
                            if (text.includes('RECEBER POR E-MAIL') || text.includes('@GMAIL.COM')) return 'token_delivery';
                            return '';
                        })()
                        """,
                        timeout=30.0,
                    )
                    await asyncio.sleep(1.0)
                if False and state == "token_delivery":
                    selecionou_email = await eval_js(
                        session_id,
                        """
                        (() => {
                            const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                            const visible = (el) => {
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const candidates = [...document.querySelectorAll('[id$="-Content"], .card-content, .ph.card.card-content')]
                                .filter(visible)
                                .map((el) => {
                                    const text = norm(el.innerText || el.textContent || '');
                                    if (!text.includes('RECEBER POR E-MAIL') && !text.includes('@GMAIL.COM')) return null;
                                    const className = (el.className || '').toString().toUpperCase();
                                    const isCard = className.includes('CARD-CONTENT') || className.includes('PH CARD');
                                    const textLength = text.length || 9999;
                                    return { el, score: (isCard ? 1000 : 0) - textLength };
                                })
                                .filter(Boolean)
                                .sort((a, b) => b.score - a.score);
                            const match = candidates.length ? candidates[0].el : null;
                            if (!match) return false;
                            const text = norm(match.innerText || match.textContent || '');
                            if (!text.includes('RECEBER POR E-MAIL') && !text.includes('@GMAIL.COM')) return false;
                            const clickable = match.closest('[id$="-Content"], .card-content, .ph.card.card-content') || match;
                            clickable.scrollIntoView({ block: 'center', inline: 'center' });
                            clickable.click();
                            return true;
                        })()
                        """,
                    )
                    if not selecionou_email and not await click_card_by_text(session_id, ["RECEBER POR E-MAIL", "@GMAIL.COM"], timeout=20.0):
                        if not await click_by_text(session_id, ["Receber por e-mail", "@gmail.com"], timeout=20.0):
                            await capture_portal_html_debug_v2(session_id, f"azulzinha_token_delivery_select_{company_norm}.html")
                            raise RuntimeError("Nao foi possivel selecionar o envio do token por e-mail na Azulzinha/Caixa.")
                    await asyncio.sleep(1.0)
                    await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const inputs = [...document.querySelectorAll('input')].filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                            return inputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO'));
                        })()
                        """,
                        timeout=30.0,
                    )
                await wait_for_condition(
                    session_id,
                    """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const hasSalesTabs = Boolean(
                            document.querySelector('header[role="tablist"]') ||
                            document.querySelector('#HistoricoVendas button[role="tab"]') ||
                            document.querySelector('#Pix button[role="tab"]')
                        );
                        const onLoginPage = (
                            visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                            visible(document.querySelector('#b2-b1-Input_Password'))
                        ) || text.includes('ACESSE SUA CONTA');
                        const inputs = [...document.querySelectorAll('input')].filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                        return (!onLoginPage && (hasSalesTabs || text.includes('HISTORICO DE VENDAS') || text.includes('PAGAMENTO INSTANTANEO') || text.includes('PIX'))) || (!onLoginPage && inputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO')));
                    })()
                    """,
                    timeout=60.0,
                )
                if await eval_js(
                    session_id,
                    """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const onLoginPage = (
                            visible(document.querySelector('#b2-b1-b4-InputMask')) &&
                            visible(document.querySelector('#b2-b1-Input_Password'))
                        ) || text.includes('ACESSE SUA CONTA');
                        return Boolean(
                            !onLoginPage && (
                                document.querySelector('header[role="tablist"]') ||
                                document.querySelector('#HistoricoVendas button[role="tab"]') ||
                                document.querySelector('#Pix button[role="tab"]') ||
                                text.includes('HISTORICO DE VENDAS') ||
                                text.includes('PAGAMENTO INSTANTANEO') ||
                                text.includes('PIX')
                            )
                        );
                    })()
                    """,
                ):
                    return
                ultimo_token_usado = ""
                tokens_descartados: set[str] = set()
                for tentativa_token in range(3):
                    if tentativa_token > 0:
                        espera_extra_apos_rejeicao = 5.0
                        _emit_pix_status(
                            on_status,
                            f"Token rejeitado pela Caixa; descartando o codigo anterior e aguardando {int(espera_extra_apos_rejeicao)}s por um novo e-mail...",
                        )
                        await asyncio.sleep(espera_extra_apos_rejeicao)
                        try:
                            state = await request_token_via_email(session_id, "token")
                            if state == "token":
                                token_requested_at = time.time()
                                await wait_for_token_email_delivery_grace()
                        except Exception:
                            pass
                    inicio_busca_token = token_requested_at
                    espera_token = 180.0 if tentativa_token == 0 else 150.0
                    token = str(
                        await asyncio.to_thread(
                            _fetch_fiserv_token_from_gmail,
                            inicio_busca_token,
                            espera_token,
                            on_status,
                            tokens_descartados,
                            tentativa_token == 0,
                            cancel_event,
                        )
                        or ""
                    ).strip()
                    if (not token or token == ultimo_token_usado or token in tokens_descartados) and callable(token_callback):
                        token = str(token_callback("Informe o token enviado por e-mail pela Azulzinha/Caixa") or "").strip()
                    if token in tokens_descartados:
                        _emit_pix_status(on_status, "O token informado ja foi rejeitado anteriormente pela Caixa.")
                        token = ""
                    if not token:
                        if tentativa_token >= 2:
                            raise RuntimeError("Nao foi possivel obter um token novo enviado por e-mail pela Caixa.")
                        _emit_pix_status(on_status, "Ainda nao chegou um token novo da Caixa; aguardando mais um pouco antes da proxima tentativa.")
                        continue

                    ultimo_token_usado = token
                    _emit_pix_status(on_status, f"Confirmando token da Caixa: {token}...")
                    confirmed = False
                    token_inputs = await eval_js(
                        session_id,
                        """
                        (() => {
                            return [...document.querySelectorAll('input')]
                                .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled)
                                .map((el) => ({
                                    selector: el.id ? `#${el.id}` : '',
                                    maxLength: Number(el.maxLength || 0),
                                }));
                        })()
                        """,
                    ) or []
                    token_selectors = [
                        str(item.get("selector") or "").strip()
                        for item in token_inputs
                        if str(item.get("selector") or "").strip()
                    ]
                    token_digitos = list(str(token))
                    if token_selectors and len(token_selectors) > 1 and len(token_digitos) >= len(token_selectors):
                        for idx, selector in enumerate(token_selectors):
                            if not await focus_selector(session_id, selector):
                                continue
                            await eval_js(
                                session_id,
                                f"""
                                (() => {{
                                    const el = document.querySelector({selector!r});
                                    if (!el) return false;
                                    el.value = '';
                                    el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                                    return true;
                                }})()
                                """,
                            )
                            await cdp("Input.insertText", {"text": token_digitos[idx]}, session_id=session_id)
                            await asyncio.sleep(0.08)
                        confirmed = True
                    else:
                        confirmed = await eval_js(
                            session_id,
                            f"""
                            (() => {{
                                const token = {token!r};
                                const setNativeValue = (el, value) => {{
                                    const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value')?.set;
                                    if (setter) setter.call(el, value); else el.value = value;
                                    el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                                    el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                                    el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                                }};
                                const inputs = [...document.querySelectorAll('input')].filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                                if (inputs.length) {{
                                    setNativeValue(inputs[inputs.length - 1], '');
                                    setNativeValue(inputs[inputs.length - 1], token);
                                    return true;
                                }}
                                return false;
                            }})()
                            """,
                        )
                    if not confirmed:
                        raise RuntimeError("Nao foi possivel preencher o token da Azulzinha/Caixa.")
                    await asyncio.sleep(0.4)
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const buttons = [...document.querySelectorAll('button, input[type="submit"], a')];
                            const button = buttons.find((el) => /CONFIRMAR|VALIDAR|ENTRAR|CONTINUAR/i.test(el.innerText || el.value || '')) || buttons[0];
                            button?.click();
                            return true;
                        })()
                        """,
                    )

                    _emit_pix_status(on_status, "Aguardando a Caixa validar o token...")
                    await asyncio.sleep(1.5)
                    sales_ready_expression = """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const hasSalesTabs = Boolean(
                            document.querySelector('header[role="tablist"]') ||
                            document.querySelector('#HistoricoVendas button[role="tab"]') ||
                            document.querySelector('#Pix button[role="tab"]')
                        );
                        return hasSalesTabs || text.includes('HISTORICO DE VENDAS') || text.includes('PAGAMENTO INSTANTANEO') || text.includes('PIX');
                    })()
                    """
                    post_token_state_expression = """
                    (() => {
                        const text = (document.body?.innerText || '')
                            .normalize('NFD')
                            .replace(/[\\u0300-\\u036f]/g, '')
                            .toUpperCase();
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        const hasSalesTabs = Boolean(
                            document.querySelector('header[role="tablist"]') ||
                            document.querySelector('#HistoricoVendas button[role="tab"]') ||
                            document.querySelector('#Pix button[role="tab"]')
                        );
                        const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                        const passwordInput = document.querySelector('#b2-b1-Input_Password');
                        const tokenInputs = [...document.querySelectorAll('input')]
                            .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el));
                        if (
                            text.includes('CODIGO INVALIDO') ||
                            text.includes('TOKEN INVALIDO') ||
                            text.includes('TOKEN EXPIRADO') ||
                            text.includes('TENTATIVAS')
                        ) return 'invalid';
                        if ((visible(loginInput) && visible(passwordInput)) || (text.includes('ACESSE SUA CONTA') && visible(loginInput))) return 'login';
                        if (hasSalesTabs || text.includes('HISTORICO DE VENDAS') || text.includes('PAGAMENTO INSTANTANEO') || text.includes('PIX')) return 'sales';
                        if (tokenInputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO') || text.includes('E-MAIL') || text.includes('EMAIL'))) return 'token';
                        return '';
                    })()
                    """
                    try:
                        resultado_token = await wait_for_condition(
                            session_id,
                            post_token_state_expression,
                            timeout=150.0,
                            description="A Caixa nao concluiu a validacao do token",
                        )
                    except Exception:
                        resultado_token = ""
                    if resultado_token == "login":
                        if auth_restart_count >= 2:
                            raise RuntimeError("A Caixa voltou para a tela de login apos validar o token repetidas vezes.")
                        _emit_pix_status(
                            on_status,
                            "A Caixa voltou para a tela de login apos validar o token; refazendo a autenticacao...",
                        )
                        await asyncio.sleep(2.0)
                        await ensure_login(session_id, auth_restart_count + 1)
                        return
                    if resultado_token != "sales" and resultado_token != "invalid":
                        try:
                            await navigate(session_id, credenciais["sales_url"])
                            resultado_token = await wait_for_condition(
                                session_id,
                                post_token_state_expression,
                                timeout=60.0,
                                description="A Caixa nao abriu a area de vendas apos validar o token",
                            )
                        except Exception:
                            pass
                    if resultado_token == "sales":
                        break
                    if tentativa_token >= 2:
                        raise RuntimeError("O token informado pela Caixa nao foi aceito apos multiplas tentativas.")
                    tokens_descartados.add(token)
                await wait_for_condition(
                    session_id,
                    sales_ready_expression,
                    timeout=90.0,
                    description="A Caixa nao abriu a area de vendas apos validar o token",
                )

            sales_area_state_expression = """
            (() => {
                const text = (document.body?.innerText || '')
                    .normalize('NFD')
                    .replace(/[\u0300-\u036f]/g, '')
                    .toUpperCase();
                const href = String(location.href || '').toUpperCase();
                const visible = (el) => {
                    if (!el) return false;
                    const rect = el.getBoundingClientRect();
                    const style = getComputedStyle(el);
                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                };
                const hasAuthenticatedNav = Boolean(
                    [...document.querySelectorAll('a, button, span, div')]
                        .filter(visible)
                        .find((el) => {
                            if (el.closest('.om-footer, footer')) return false;
                            const label = String(el.innerText || el.textContent || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const linkHref = String(el.getAttribute?.('href') || '').toUpperCase();
                            return (
                                linkHref.includes('/MINHASVENDAS') ||
                                linkHref.includes('ROUTER=0') ||
                                label.includes('RELATORIOS DE VENDA') ||
                                label.includes('MINHAS VENDAS') ||
                                label.includes('HISTORICO DE VENDAS') ||
                                label.includes('PAGAMENTO INSTANTANEO') ||
                                label.includes('PIX') ||
                                label.includes('SAIR')
                            );
                        })
                );
                const hasSalesTabs = Boolean(
                    visible(document.querySelector('header[role="tablist"]')) ||
                    [...document.querySelectorAll('header[role="tablist"] button[role="tab"], #HistoricoVendas button[role="tab"], #Pix button[role="tab"], #HistoricoVendas [role="tabpanel"], #Pix [role="tabpanel"]')]
                        .some(visible) ||
                    visible(document.querySelector('[data-testid="vendas-btn-exportar"]')) ||
                    visible(document.querySelector('[data-testid="vendas-periodo-hoje"]'))
                );
                const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                const passwordInput = document.querySelector('#b2-b1-Input_Password');
                const tokenInputs = [...document.querySelectorAll('input')]
                    .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el));
                const deviceVisible = text.includes('SELECIONE O DISPOSITIVO');
                const tokenDeliveryVisible = (
                    text.includes('ESCOLHA POR ONDE DESEJA RECEBER') ||
                    text.includes('RECEBER POR E-MAIL') ||
                    text.includes('@GMAIL.COM')
                );
                const invalidVisible = (
                    text.includes('CODIGO INVALIDO') ||
                    text.includes('TOKEN INVALIDO') ||
                    text.includes('TOKEN EXPIRADO') ||
                    text.includes('TENTATIVAS')
                );
                const tokenVisible = tokenInputs.length > 0 && (
                    text.includes('TOKEN') ||
                    text.includes('CODIGO') ||
                    text.includes('E-MAIL') ||
                    text.includes('EMAIL')
                );
                const loginTextVisible = (
                    text.includes('ACESSE SUA CONTA') ||
                    (text.includes('CNPJ, CPF OU USUARIO') && text.includes('SENHA'))
                );
                const loginVisible = (
                    href.includes('ISTIMEOUT=TRUE') ||
                    (visible(loginInput) && visible(passwordInput)) ||
                    (
                        loginTextVisible &&
                        !deviceVisible &&
                        !tokenDeliveryVisible &&
                        !tokenVisible &&
                        !invalidVisible
                    )
                );
                if (href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST')) return 'portal_error';
                if (hasSalesTabs) return 'sales';
                if (loginVisible) return 'login';
                if (deviceVisible) return 'device';
                if (tokenDeliveryVisible) return 'token';
                if (tokenVisible) return 'token';
                return '';
            })()
            """

            async def ensure_sales_area(session_id: str, kind: str, context_label: str, auth_retry_count: int = 0) -> None:
                try:
                    current_state = str(await eval_js(session_id, sales_area_state_expression, timeout=15.0) or "").strip()
                except Exception:
                    current_state = ""
                if current_state == "sales":
                    return
                if current_state == "portal_error":
                    if auth_retry_count >= 2:
                        raise RuntimeError(f"A Caixa abriu a pagina de erro ao acessar {context_label} repetidas vezes.")
                    _emit_pix_status(
                        on_status,
                        f"A Caixa abriu a pagina de erro ao acessar {context_label}; recarregando o portal...",
                    )
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_portal_error_{kind}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    await asyncio.sleep(2.0)
                    await navigate(session_id, credenciais["sales_url"])
                    await ensure_sales_area(session_id, kind, context_label, auth_retry_count + 1)
                    return
                if current_state in {"login", "device", "token"}:
                    if auth_retry_count >= 2:
                        raise RuntimeError(f"A Caixa perdeu a sessao ao abrir {context_label} repetidas vezes.")
                    _emit_pix_status(
                        on_status,
                        f"A sessao da Caixa expirou ao abrir {context_label}; refazendo a autenticacao...",
                    )
                    await ensure_login(session_id)
                    try:
                        current_state = str(await eval_js(session_id, sales_area_state_expression, timeout=15.0) or "").strip()
                    except Exception:
                        current_state = ""
                    if current_state == "sales":
                        return
                await navigate(session_id, credenciais["sales_url"])
                await wait_for_condition(session_id, "document.body && document.body.innerText.length > 20", timeout=60.0)
                try:
                    state_after_navigation = await wait_for_condition(
                        session_id,
                        sales_area_state_expression,
                        timeout=60.0,
                        step=0.5,
                        description=f"A Caixa nao abriu a area de vendas para {context_label}",
                    )
                except Exception:
                    try:
                        html_debug = await eval_js(
                            session_id,
                            "document.documentElement ? document.documentElement.outerHTML : ''",
                            timeout=15.0,
                        )
                        if html_debug:
                            debug_path = artifacts_dir / f"azulzinha_sales_area_debug_{kind}.html"
                            debug_path.write_text(str(html_debug), encoding="utf-8")
                    except Exception:
                        pass
                    raise
                if state_after_navigation == "sales":
                    return
                if state_after_navigation == "portal_error":
                    if auth_retry_count >= 2:
                        raise RuntimeError(f"A Caixa abriu a pagina de erro ao acessar {context_label} repetidas vezes.")
                    _emit_pix_status(
                        on_status,
                        f"A Caixa abriu a pagina de erro ao abrir {context_label}; tentando recarregar o portal...",
                    )
                    await asyncio.sleep(2.0)
                    await navigate(session_id, credenciais["sales_url"])
                    await ensure_sales_area(session_id, kind, context_label, auth_retry_count + 1)
                    return
                if state_after_navigation in {"login", "device", "token"}:
                    if auth_retry_count >= 2:
                        raise RuntimeError(f"A Caixa perdeu a sessao ao abrir {context_label} repetidas vezes.")
                    _emit_pix_status(
                        on_status,
                        f"A Caixa redirecionou para o login ao abrir {context_label}; refazendo a autenticacao...",
                    )
                    await ensure_login(session_id)
                    await ensure_sales_area(session_id, kind, context_label, auth_retry_count + 1)
                    return
                raise RuntimeError(f"A Caixa nao confirmou a area de vendas para {context_label}.")

            token_email_grace_seconds_v2 = 15.0
            tokens_descartados_globais_v2: set[str] = set()

            portal_state_expression_v2 = """
            (() => {
                const text = (document.body?.innerText || '')
                    .normalize('NFD')
                    .replace(/[\\u0300-\\u036f]/g, '')
                    .toUpperCase();
                const href = String(location.href || '').toUpperCase();
                const visible = (el) => {
                    if (!el) return false;
                    const rect = el.getBoundingClientRect();
                    const style = getComputedStyle(el);
                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                };
                const hasAuthenticatedNav = Boolean(
                    [...document.querySelectorAll('a, button, span, div')]
                        .filter(visible)
                        .find((el) => {
                            if (el.closest('.om-footer, footer')) return false;
                            const label = String(el.innerText || el.textContent || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const linkHref = String(el.getAttribute?.('href') || '').toUpperCase();
                            return (
                                linkHref.includes('/MINHASVENDAS') ||
                                linkHref.includes('ROUTER=0') ||
                                label.includes('RELATORIOS DE VENDA') ||
                                label.includes('MINHAS VENDAS') ||
                                label.includes('HISTORICO DE VENDAS') ||
                                label.includes('PAGAMENTO INSTANTANEO') ||
                                label.includes('PIX') ||
                                label.includes('SAIR')
                            );
                        })
                );
                const hasSalesTabs = Boolean(
                    visible(document.querySelector('header[role="tablist"]')) ||
                    [...document.querySelectorAll('header[role="tablist"] button[role="tab"], #HistoricoVendas button[role="tab"], #Pix button[role="tab"], #HistoricoVendas [role="tabpanel"], #Pix [role="tabpanel"]')]
                        .some(visible) ||
                    visible(document.querySelector('[data-testid="vendas-btn-exportar"]')) ||
                    visible(document.querySelector('[data-testid="vendas-periodo-hoje"]'))
                );
                const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                const passwordInput = document.querySelector('#b2-b1-Input_Password');
                const tokenInputs = [...document.querySelectorAll('input')]
                    .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el));
                const deviceVisible = text.includes('SELECIONE O DISPOSITIVO');
                const tokenDeliveryVisible = (
                    text.includes('ESCOLHA POR ONDE DESEJA RECEBER') ||
                    text.includes('RECEBER POR E-MAIL') ||
                    text.includes('@GMAIL.COM')
                );
                const invalidVisible = (
                    text.includes('CODIGO INVALIDO') ||
                    text.includes('TOKEN INVALIDO') ||
                    text.includes('TOKEN EXPIRADO') ||
                    text.includes('TENTATIVAS')
                );
                const tokenVisible = tokenInputs.length > 0 && (
                    text.includes('TOKEN') ||
                    text.includes('CODIGO') ||
                    text.includes('E-MAIL') ||
                    text.includes('EMAIL')
                );
                const genericErrorVisible = (
                    text.includes('OPS, UM ERRO ACONTECEU') ||
                    text.includes('OPS UM ERRO ACONTECEU') ||
                    (text.includes('ERRO ACONTECEU') && text.includes('TENTE NOVAMENTE MAIS TARDE'))
                );
                const loginTextVisible = (
                    text.includes('ACESSE SUA CONTA') ||
                    (text.includes('CNPJ, CPF OU USUARIO') && text.includes('SENHA'))
                );
                const loginVisible = (
                    href.includes('ISTIMEOUT=TRUE') ||
                    (visible(loginInput) && visible(passwordInput)) ||
                    (
                        loginTextVisible &&
                        !deviceVisible &&
                        !tokenDeliveryVisible &&
                        !tokenVisible &&
                        !invalidVisible
                    )
                );
                const homeVisible = (
                    !loginVisible &&
                    !deviceVisible &&
                    !tokenVisible &&
                    !tokenDeliveryVisible &&
                    !invalidVisible &&
                    (href.includes('/HOME') || text.includes('RELATORIOS DE VENDA') || hasAuthenticatedNav)
                );
                const bodyLength = (document.body?.innerText || '').trim().length;
                if (href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST') || genericErrorVisible) return 'portal_error';
                if (hasSalesTabs) return 'sales';
                if (loginVisible) return 'login';
                if (homeVisible) return 'home';
                if (invalidVisible) return 'invalid';
                if (deviceVisible) return 'device';
                if (tokenVisible) return 'token';
                if (tokenDeliveryVisible) return 'token_delivery';
                if (document.readyState !== 'complete' || bodyLength < 20) return 'loading';
                return 'unknown';
            })()
            """

            async def capture_portal_html_debug_v2(session_id: str, filename: str) -> None:
                try:
                    html_debug = await eval_js(
                        session_id,
                        "document.documentElement ? document.documentElement.outerHTML : ''",
                        timeout=15.0,
                    )
                    if html_debug:
                        (artifacts_dir / filename).write_text(str(html_debug), encoding="utf-8")
                except Exception:
                    pass

            async def get_portal_state_v2(session_id: str, timeout: float = 15.0) -> str:
                try:
                    captcha_snapshot = await eval_js(
                        session_id,
                        """
                        (() => JSON.stringify({
                            url: String(location.href || ''),
                            title: String(document.title || ''),
                            text: String(document.body?.innerText || ''),
                            frames: [...document.querySelectorAll('iframe')]
                                .filter((frame) => {
                                    const rect = frame.getBoundingClientRect();
                                    const style = getComputedStyle(frame);
                                    return rect.width > 5 && rect.height > 5 && style.visibility !== 'hidden' && style.display !== 'none';
                                })
                                .map((frame) => String(frame.src || '')),
                        }))()
                        """,
                        timeout=timeout,
                    )
                    captcha_page = json.loads(str(captcha_snapshot or "{}"))
                    if _is_azulzinha_captcha_page(
                        captcha_page.get("url", ""),
                        captcha_page.get("title", ""),
                        captcha_page.get("text", ""),
                        captcha_page.get("frames", ()),
                    ):
                        return "captcha_manual"
                    return str(await eval_js(session_id, portal_state_expression_v2, timeout=timeout) or "").strip()
                except Exception:
                    return ""

            async def wait_for_manual_captcha_resolution_v2(session_id: str) -> str:
                _emit_pix_status(
                    on_status,
                    "A Caixa solicitou uma verificacao CAPTCHA. O navegador foi exibido para resolucao manual; a automacao esta pausada.",
                )
                try:
                    await _show_chromium_window(cdp, target_id)
                    await cdp("Page.bringToFront", session_id=session_id, timeout=5.0)
                except Exception:
                    pass

                deadline = time.time() + 600.0
                while time.time() < deadline:
                    _check_cancelled()
                    state = await get_portal_state_v2(session_id)
                    if state != "captcha_manual":
                        _emit_pix_status(on_status, "A verificacao CAPTCHA foi concluida; retomando a leitura do portal da Caixa.")
                        return state
                    await asyncio.sleep(1.0)

                raise RuntimeError(
                    "A Caixa solicitou uma verificacao CAPTCHA que nao foi concluida em 10 minutos. "
                    "Nenhum relatorio foi baixado e nenhum PDF foi publicado."
                )

            async def wait_for_portal_state_v2(
                session_id: str,
                accepted_states: set[str],
                timeout: float,
                description: str,
                step: float = 0.5,
            ) -> str:
                deadline = time.time() + timeout
                last_state = ""
                while time.time() < deadline:
                    _check_cancelled()
                    state = await get_portal_state_v2(session_id)
                    last_state = state or ""
                    if state in accepted_states:
                        return state
                    await asyncio.sleep(step)
                raise TimeoutError(f"{description} :: ultimo estado={last_state or 'desconhecido'}")

            async def is_app_token_screen_v2(session_id: str) -> bool:
                return bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            return text.includes('INFORME O TOKEN DO APLICATIVO');
                        })()
                        """,
                        timeout=10.0,
                    )
                )

            async def inspect_token_challenge_v2(session_id: str) -> dict:
                return (
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const href = String(location.href || '').toUpperCase();
                            const visible = (el) => {
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                            const passwordInput = document.querySelector('#b2-b1-Input_Password');
                            const tokenInputs = [...document.querySelectorAll('input')].filter((el) => {
                                const type = (el.type || '').toLowerCase();
                                return type !== 'hidden' && type !== 'password' && !el.disabled && visible(el);
                            });
                            const deliveryVisible = (
                                text.includes('ESCOLHA POR ONDE DESEJA RECEBER') ||
                                text.includes('RECEBER POR E-MAIL') ||
                                text.includes('@GMAIL.COM')
                            );
                            const appTokenVisible = text.includes('INFORME O TOKEN DO APLICATIVO');
                            const invalidVisible = (
                                text.includes('CODIGO INVALIDO') ||
                                text.includes('TOKEN INVALIDO') ||
                                text.includes('TOKEN EXPIRADO') ||
                                text.includes('TENTATIVAS')
                            );
                            const emailTokenReady = tokenInputs.length > 0 && (
                                text.includes('TOKEN') ||
                                text.includes('CODIGO') ||
                                text.includes('E-MAIL') ||
                                text.includes('EMAIL')
                            );
                            const loginTextVisible = (
                                text.includes('ACESSE SUA CONTA') ||
                                (text.includes('CNPJ, CPF OU USUARIO') && text.includes('SENHA'))
                            );
                            const onLoginPage = (
                                (visible(loginInput) && visible(passwordInput)) ||
                                (
                                    loginTextVisible &&
                                    !deliveryVisible &&
                                    !appTokenVisible &&
                                    !emailTokenReady &&
                                    !invalidVisible &&
                                    !text.includes('SELECIONE O DISPOSITIVO')
                                )
                            );
                            return {
                                onLoginPage,
                                tokenInputsVisible: !onLoginPage && tokenInputs.length > 0,
                                emailTokenReady: !onLoginPage && emailTokenReady,
                                deliveryVisible: !onLoginPage && deliveryVisible,
                                appTokenVisible: !onLoginPage && appTokenVisible,
                                invalidVisible: !onLoginPage && invalidVisible,
                            };
                        })()
                        """,
                        timeout=10.0,
                    )
                    or {}
                )

            async def wait_for_token_email_delivery_grace_v2() -> None:
                _emit_pix_status(
                    on_status,
                    f"Aguardando {int(token_email_grace_seconds_v2)}s para o e-mail do token chegar...",
                )
                await asyncio.sleep(token_email_grace_seconds_v2)

            async def wait_for_post_token_resolution_v2(session_id: str, timeout: float = 150.0) -> str:
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    snapshot = await eval_js(
                        session_id,
                        """
                        (() => {
                            const text = (document.body?.innerText || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .toUpperCase();
                            const href = String(location.href || '').toUpperCase();
                            const visible = (el) => {
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const bodyLength = (document.body?.innerText || '').trim().length;
                            const tokenInputs = [...document.querySelectorAll('input')]
                                .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el));
                            const hasAuthenticatedNav = Boolean(
                                [...document.querySelectorAll('a, button, span, div')]
                                    .filter(visible)
                                    .find((el) => {
                                        if (el.closest('.om-footer, footer')) return false;
                                        const label = String(el.innerText || el.textContent || '')
                                            .normalize('NFD')
                                            .replace(/[\\u0300-\\u036f]/g, '')
                                            .toUpperCase();
                                        const linkHref = String(el.getAttribute?.('href') || '').toUpperCase();
                                        return (
                                            linkHref.includes('/MINHASVENDAS') ||
                                            linkHref.includes('ROUTER=0') ||
                                            label.includes('RELATORIOS DE VENDA') ||
                                            label.includes('MINHAS VENDAS') ||
                                            label.includes('HISTORICO DE VENDAS') ||
                                            label.includes('PAGAMENTO INSTANTANEO') ||
                                            label.includes('PIX') ||
                                            label.includes('SAIR')
                                        );
                                    })
                            );
                            const hasSalesTabs = Boolean(
                                visible(document.querySelector('header[role="tablist"]')) ||
                                [...document.querySelectorAll('header[role="tablist"] button[role="tab"], #HistoricoVendas button[role="tab"], #Pix button[role="tab"], #HistoricoVendas [role="tabpanel"], #Pix [role="tabpanel"]')]
                                    .some(visible)
                            );
                            const loginInput = document.querySelector('#b2-b1-b4-InputMask');
                            const passwordInput = document.querySelector('#b2-b1-Input_Password');
                            const deviceVisible = text.includes('SELECIONE O DISPOSITIVO');
                            const tokenDeliveryVisible = text.includes('ESCOLHA POR ONDE DESEJA RECEBER') || text.includes('RECEBER POR E-MAIL') || text.includes('@GMAIL.COM');
                            const invalidVisible = (
                                text.includes('CODIGO INVALIDO') ||
                                text.includes('TOKEN INVALIDO') ||
                                text.includes('TOKEN EXPIRADO') ||
                                text.includes('TENTATIVAS')
                            );
                            const tokenVisible = tokenInputs.length > 0 && (text.includes('TOKEN') || text.includes('CODIGO') || text.includes('E-MAIL') || text.includes('EMAIL'));
                            const genericErrorVisible = (
                                text.includes('OPS, UM ERRO ACONTECEU') ||
                                text.includes('OPS UM ERRO ACONTECEU') ||
                                (text.includes('ERRO ACONTECEU') && text.includes('TENTE NOVAMENTE MAIS TARDE'))
                            );
                            const loginTextVisible = text.includes('ACESSE SUA CONTA') || (text.includes('CNPJ, CPF OU USUARIO') && text.includes('SENHA'));
                            const loginVisible = (
                                href.includes('ISTIMEOUT=TRUE') ||
                                (visible(loginInput) && visible(passwordInput)) ||
                                (
                                    loginTextVisible &&
                                    !deviceVisible &&
                                    !tokenDeliveryVisible &&
                                    !tokenVisible &&
                                    !invalidVisible
                                )
                            );
                            return {
                                href,
                                hasSalesTabs,
                                homeVisible: !loginVisible && !deviceVisible && !tokenVisible && !tokenDeliveryVisible && !invalidVisible && (href.includes('/HOME') || text.includes('RELATORIOS DE VENDA') || hasAuthenticatedNav),
                                loginVisible,
                                portalErrorVisible: href.includes('/_ERROR.HTML') || text.includes('ERROR PROCESSING YOUR REQUEST'),
                                genericErrorVisible,
                                invalidVisible,
                                tokenVisible,
                                tokenDeliveryVisible,
                                salesVisible: hasSalesTabs,
                                bodyLength,
                            };
                        })()
                        """,
                        timeout=15.0,
                    ) or {}
                    if bool(snapshot.get("portalErrorVisible")) or bool(snapshot.get("genericErrorVisible")):
                        return "portal_error"
                    if bool(snapshot.get("salesVisible")):
                        return "sales"
                    if bool(snapshot.get("homeVisible")):
                        return "home"
                    if bool(snapshot.get("loginVisible")):
                        return "login"
                    if bool(snapshot.get("invalidVisible")) and (
                        bool(snapshot.get("tokenVisible")) or bool(snapshot.get("tokenDeliveryVisible"))
                    ):
                        return "invalid"
                    await asyncio.sleep(0.5)
                return ""

            async def confirm_sales_access_after_token_v2(session_id: str) -> str:
                try:
                    await navigate(session_id, credenciais["sales_url"])
                    return await wait_for_portal_state_v2(
                        session_id,
                        {"sales", "home", "token", "token_delivery", "login", "portal_error", "invalid"},
                        timeout=90.0,
                        description="A Caixa nao confirmou a sessao ao abrir a area de vendas apos o token",
                    )
                except Exception:
                    return ""

            async def fetch_token_with_portal_watch_v2(
                session_id: str,
                total_timeout: float,
                allow_recent_fallback: bool,
            ) -> tuple[str, str]:
                deadline = time.time() + total_timeout
                first_chunk = True
                while time.time() < deadline:
                    state_before = await get_portal_state_v2(session_id)
                    if state_before in {"sales", "home", "login", "portal_error"}:
                        return "", state_before
                    remaining = max(0.0, deadline - time.time())
                    chunk_timeout = min(12.0, remaining)
                    if chunk_timeout <= 0:
                        break
                    token = str(
                        await asyncio.to_thread(
                            _fetch_fiserv_token_from_gmail,
                            time.time(),
                            chunk_timeout,
                            on_status,
                            tokens_descartados_globais_v2,
                            allow_recent_fallback if first_chunk else False,
                            cancel_event,
                        )
                        or ""
                    ).strip()
                    if token:
                        return token, ""
                    first_chunk = False
                    state_after = await get_portal_state_v2(session_id)
                    if state_after in {"sales", "home", "login", "portal_error"}:
                        return "", state_after
                return "", ""

            async def perform_login_step_v2(session_id: str) -> str:
                _emit_pix_status(on_status, "Autenticando na Azulzinha/Caixa...")
                try:
                    login_selectors = await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const user = document.querySelector('#b2-b1-b4-InputMask');
                            const password = document.querySelector('#b2-b1-Input_Password');
                            if (user && password) {
                                user.setAttribute('data-codex-login-user', '1');
                                password.setAttribute('data-codex-login-pass', '1');
                                return {
                                    user: '#b2-b1-b4-InputMask',
                                    password: '#b2-b1-Input_Password',
                                };
                            }
                            const visible = (el) => {
                                if (!el || el.disabled) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const fallbackUser = [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                            const fallbackPassword = [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                            if (!fallbackUser || !fallbackPassword) return null;
                            fallbackUser.setAttribute('data-codex-login-user', '1');
                            fallbackPassword.setAttribute('data-codex-login-pass', '1');
                            return {
                                user: fallbackUser.id ? `#${fallbackUser.id}` : '[data-codex-login-user="1"]',
                                password: fallbackPassword.id ? `#${fallbackPassword.id}` : '[data-codex-login-pass="1"]',
                            };
                        })()
                        """,
                        timeout=60.0,
                        description="A Caixa nao exibiu a tela de login para informar CNPJ e senha",
                    )
                except Exception:
                    login_selectors = await eval_js(
                        session_id,
                        """
                        (() => {
                            const user = document.querySelector('#b2-b1-b4-InputMask');
                            const password = document.querySelector('#b2-b1-Input_Password');
                            if (!user || !password) return null;
                            user.setAttribute('data-codex-login-user', '1');
                            password.setAttribute('data-codex-login-pass', '1');
                            return {
                                user: '#b2-b1-b4-InputMask',
                                password: '#b2-b1-Input_Password',
                            };
                        })()
                        """,
                        timeout=15.0,
                    )
                    if not login_selectors:
                        try:
                            login_wait_state = await eval_js(
                                session_id,
                                """
                                (() => ({
                                    href: String(location.href || ''),
                                    text: String(document.body?.innerText || '').slice(0, 2000),
                                    hasUser: !!document.querySelector('#b2-b1-b4-InputMask'),
                                    hasPassword: !!document.querySelector('#b2-b1-Input_Password'),
                                    bodyLength: String(document.body?.innerText || '').trim().length,
                                }))()
                                """,
                                timeout=15.0,
                            )
                            if login_wait_state is not None:
                                (artifacts_dir / "azulzinha_login_wait_state.json").write_text(
                                    json.dumps(login_wait_state, ensure_ascii=False, indent=2),
                                    encoding="utf-8",
                                )
                        except Exception:
                            pass
                        await capture_portal_html_debug_v2(session_id, "azulzinha_login_wait_debug.html")
                        raise
                login_user_selector = str((login_selectors or {}).get("user") or "#b2-b1-b4-InputMask")
                login_password_selector = str((login_selectors or {}).get("password") or "#b2-b1-Input_Password")
                cnpj_digits = re.sub(r"\D", "", str(credenciais["cnpj"] or ""))
                password_text = str(credenciais["password"] or "")
                try:
                    await insert_text(session_id, login_user_selector, cnpj_digits)
                except Exception:
                    pass
                try:
                    await insert_text(session_id, login_password_selector, password_text)
                except Exception:
                    pass
                await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const setNativeValue = (el, value) => {{
                            const proto = el instanceof HTMLTextAreaElement ? HTMLTextAreaElement.prototype : HTMLInputElement.prototype;
                            const setter = Object.getOwnPropertyDescriptor(proto, 'value')?.set;
                            if (setter) setter.call(el, value); else el.value = value;
                            el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                        }};
                        const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                        const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                        if (!user || !password) return null;
                        user.focus();
                        if (currentDigits(user).length < {len(cnpj_digits)!r}) {{
                            setNativeValue(user, {cnpj_digits!r});
                        }} else {{
                            user.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            user.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                        }}
                        password.focus();
                        if (currentValue(password).length < {len(password_text)!r}) {{
                            setNativeValue(password, {password_text!r});
                        }} else {{
                            password.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            password.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                        }}
                        const userValue = String(user?.value || user?.getAttribute('value') || '').replace(/\\D/g, '');
                        const passwordValue = String(password?.value || password?.getAttribute('value') || '');
                        return {{
                            userLen: userValue.length,
                            passwordLen: passwordValue.length,
                        }};
                    }})()
                    """,
                    timeout=20.0,
                ) or {}
                credential_fill_state = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const visible = (el) => {{
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        }};
                        const user = document.querySelector({login_user_selector!r}) || [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                        const password = document.querySelector({login_password_selector!r}) || [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                        const userValue = String(user?.value || user?.getAttribute('value') || '').replace(/\\D/g, '');
                        const passwordValue = String(password?.value || password?.getAttribute('value') || '');
                        return {{
                            userLen: userValue.length,
                            passwordLen: passwordValue.length,
                        }};
                    }})()
                    """,
                    timeout=15.0,
                ) or {}
                if int(credential_fill_state.get("userLen") or 0) < len(cnpj_digits) or int(credential_fill_state.get("passwordLen") or 0) < len(password_text):
                    state_after_fill = await get_portal_state_v2(session_id)
                    if state_after_fill in {"device", "token_delivery", "token", "sales", "portal_error"}:
                        return state_after_fill
                    await capture_portal_html_debug_v2(session_id, "azulzinha_login_fill_debug.html")
                    raise RuntimeError("Nao foi possivel preencher o login e a senha da Azulzinha/Caixa.")
                await asyncio.sleep(0.4)
                await press_tab(session_id)
                try:
                    await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const botao = document.querySelector('#b2-b1-confirmar');
                            return botao && !botao.disabled;
                        })()
                        """,
                        timeout=8.0,
                    )
                except Exception:
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const visible = (el) => {
                                if (!el) return false;
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const user = [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                            const password = [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                            for (const el of [user, password]) {
                                if (!el) continue;
                                el.dispatchEvent(new Event('input', { bubbles: true }));
                                el.dispatchEvent(new Event('change', { bubbles: true }));
                                el.dispatchEvent(new KeyboardEvent('keyup', { bubbles: true, key: '0' }));
                                el.dispatchEvent(new Event('blur', { bubbles: true }));
                            }
                            return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                    try:
                        await wait_for_condition(
                            session_id,
                            """
                            (() => {
                                const botao = document.querySelector('#b2-b1-confirmar');
                                return botao && !botao.disabled;
                            })()
                            """,
                            timeout=12.0,
                        )
                    except Exception:
                        state_after_confirm_wait = await get_portal_state_v2(session_id)
                        if state_after_confirm_wait in {"device", "token_delivery", "token", "sales", "home", "portal_error"}:
                            return state_after_confirm_wait
                        try:
                            button_state = await eval_js(
                                session_id,
                                """
                                (() => {
                                    const visible = (el) => {
                                        if (!el) return false;
                                        const rect = el.getBoundingClientRect();
                                        const style = getComputedStyle(el);
                                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                                    };
                                    const user = [...document.querySelectorAll('input:not([type="hidden"]):not([type="password"])')].filter(visible)[0];
                                    const password = [...document.querySelectorAll('input[type="password"]')].filter(visible)[0];
                                    const botao = document.querySelector('#b2-b1-confirmar');
                                    return {
                                        userValue: String(user?.value || ''),
                                        passwordLen: String(password?.value || '').length,
                                        buttonDisabled: botao ? !!botao.disabled : null,
                                        buttonText: botao ? (botao.innerText || botao.textContent || '').trim() : '',
                                    };
                                })()
                                """,
                                timeout=10.0,
                            )
                            if button_state is not None:
                                (artifacts_dir / "azulzinha_login_confirm_state.json").write_text(
                                    json.dumps(button_state, ensure_ascii=False, indent=2),
                                    encoding="utf-8",
                                )
                        except Exception:
                            pass
                        await capture_portal_html_debug_v2(session_id, "azulzinha_login_confirm_debug.html")
                        raise
                login_event_start_index = len(event_log)
                clicou = await click_selector_native(session_id, "#b2-b1-confirmar")
                if not clicou:
                    clicou = await eval_js(
                        session_id,
                        """
                        (() => {
                            const botao = document.querySelector('#b2-b1-confirmar');
                            if (!botao || botao.disabled) return false;
                            botao.focus();
                            botao.click();
                            return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                await asyncio.sleep(0.4)
                state_after_click = await get_portal_state_v2(session_id)
                if state_after_click == "login":
                    await cdp(
                        "Input.dispatchKeyEvent",
                        {"type": "keyDown", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13, "key": "Enter", "code": "Enter"},
                        session_id=session_id,
                    )
                    await cdp(
                        "Input.dispatchKeyEvent",
                        {"type": "keyUp", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13, "key": "Enter", "code": "Enter"},
                        session_id=session_id,
                    )
                if not clicou:
                    raise RuntimeError("Nao foi possivel confirmar o login da Azulzinha/Caixa.")
                login_response = None
                login_response_deadline = time.time() + 25.0
                seen_login_request_ids = set()
                while time.time() < login_response_deadline and login_response is None:
                    for event in list(event_log[login_event_start_index:]):
                        params = event.get("params") or {}
                        response = params.get("response") or {}
                        url = str(response.get("url") or "")
                        request_id = str(params.get("requestId") or "")
                        if (
                            event.get("method") != "Network.responseReceived"
                            or "ActionLoginDevicesApi" not in url
                            or not request_id
                            or request_id in seen_login_request_ids
                        ):
                            continue
                        seen_login_request_ids.add(request_id)
                        try:
                            body_payload = await cdp(
                                "Network.getResponseBody",
                                {"requestId": request_id},
                                session_id=session_id,
                                timeout=10.0,
                            )
                            login_response = json.loads(str(body_payload.get("body") or "{}"))
                            break
                        except Exception:
                            continue
                    if login_response is None:
                        await asyncio.sleep(0.5)
                if isinstance(login_response, dict):
                    login_data = login_response.get("data") or {}
                    login_error = login_data.get("Erro") or login_response.get("Erro") or {}
                    if login_response.get("Success") is False or login_data.get("Success") is False:
                        error_message = str(login_error.get("Mensagem") or "").strip()
                        error_code = str(login_error.get("Codigo") or "").strip()
                        wait_match = re.search(r"(\d+)\s*min", error_message, re.IGNORECASE)
                        if error_code == "423" and wait_match:
                            wait_seconds = (int(wait_match.group(1)) * 60) + 15
                            _emit_pix_status(
                                on_status,
                                f"A Azulzinha bloqueou novas tentativas de login: {error_message} Aguardando {wait_seconds // 60} min...",
                            )
                            await asyncio.sleep(wait_seconds)
                            return "login"
                        if error_message:
                            raise RuntimeError(_format_azulzinha_login_rejected_message(error_message, company_label))
                try:
                    return await wait_for_portal_state_v2(
                        session_id,
                        {"sales", "home", "device", "token_delivery", "token", "portal_error", "invalid"},
                        timeout=90.0,
                        description="A Caixa nao concluiu a etapa inicial do login",
                    )
                except TimeoutError:
                    return await get_portal_state_v2(session_id) or "login"

            async def perform_device_selection_step_v2(session_id: str) -> str:
                _emit_pix_status(on_status, "Selecionando dispositivo da Caixa...")
                if not await click_card_by_text(session_id, _azulzinha_device_aliases(company_label), timeout=30.0):
                    raise RuntimeError(f"Nao foi possivel selecionar o dispositivo da {company_label} na Azulzinha/Caixa.")
                await asyncio.sleep(1.0)
                return await wait_for_portal_state_v2(
                    session_id,
                    {"sales", "home", "token_delivery", "token", "login", "portal_error", "invalid"},
                    timeout=45.0,
                    description="A Caixa nao avancou apos a selecao do dispositivo",
                )

            async def request_token_via_email_v2(
                session_id: str,
                current_state: str | None = None,
                force_refresh: bool = False,
            ) -> str:
                state_local = str(current_state or "").strip() or await get_portal_state_v2(session_id)
                token_challenge = await inspect_token_challenge_v2(session_id)
                if bool(token_challenge.get("emailTokenReady")) and not bool(token_challenge.get("appTokenVisible")):
                    return "token"
                if state_local not in {"token", "token_delivery", "invalid"}:
                    state_local = await wait_for_portal_state_v2(
                        session_id,
                        {"sales", "home", "login", "device", "token_delivery", "token", "portal_error", "invalid", "captcha_manual"},
                        timeout=30.0,
                        description="A Caixa nao exibiu a etapa de token por e-mail",
                    )
                    token_challenge = await inspect_token_challenge_v2(session_id)
                if state_local == "invalid":
                    if bool(token_challenge.get("deliveryVisible")) and not bool(token_challenge.get("emailTokenReady")):
                        state_local = "token_delivery"
                    else:
                        state_local = "token"
                if bool(token_challenge.get("emailTokenReady")) and not bool(token_challenge.get("appTokenVisible")):
                    return "token"
                if state_local == "token" and not force_refresh and not await is_app_token_screen_v2(session_id):
                    return "token"

                abriu = False
                if state_local == "token":
                    abriu = bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                                const link = document.querySelector('a.bold.font-universe.cor-preto');
                                if (!link) return false;
                                link.click();
                                return true;
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                    if not abriu:
                        abriu = await click_by_text(
                            session_id,
                            ["Receber codigo por e-mail ou SMS", "Reenviar codigo", "Reenviar token"],
                            timeout=15.0,
                        )
                    if abriu:
                        state_local = await wait_for_portal_state_v2(
                            session_id,
                            {"sales", "home", "login", "token_delivery", "token", "portal_error", "invalid"},
                            timeout=30.0,
                            description="A Caixa nao abriu a escolha de envio do token",
                        )
                        token_challenge = await inspect_token_challenge_v2(session_id)
                        await asyncio.sleep(1.0)
                        if state_local == "invalid":
                            if bool(token_challenge.get("deliveryVisible")) and not bool(token_challenge.get("emailTokenReady")):
                                state_local = "token_delivery"
                            else:
                                state_local = "token"

                if state_local == "token_delivery":
                    token_challenge = await inspect_token_challenge_v2(session_id)
                    if bool(token_challenge.get("emailTokenReady")) and not bool(token_challenge.get("appTokenVisible")):
                        return "token"
                    selecionou_email = await eval_js(
                        session_id,
                        """
                        (() => {
                            const norm = (v) => (v || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toUpperCase();
                            const visible = (el) => {
                                const rect = el.getBoundingClientRect();
                                const style = getComputedStyle(el);
                                return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                            };
                            const candidates = [...document.querySelectorAll('[id$="-Content"], .card-content, .ph.card.card-content')]
                                .filter(visible)
                                .map((el) => {
                                    const text = norm(el.innerText || el.textContent || '');
                                    if (!text.includes('RECEBER POR E-MAIL') && !text.includes('@GMAIL.COM')) return null;
                                    const className = (el.className || '').toString().toUpperCase();
                                    const isCard = className.includes('CARD-CONTENT') || className.includes('PH CARD');
                                    const textLength = text.length || 9999;
                                    return { el, score: (isCard ? 1000 : 0) - textLength };
                                })
                                .filter(Boolean)
                                .sort((a, b) => b.score - a.score);
                            const match = candidates.length ? candidates[0].el : null;
                            if (!match) return false;
                            const clickable = match.closest('[id$="-Content"], .card-content, .ph.card.card-content') || match;
                            clickable.scrollIntoView({ block: 'center', inline: 'center' });
                            clickable.click();
                            return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                    if not selecionou_email and not await click_card_by_text(session_id, ["RECEBER POR E-MAIL", "@GMAIL.COM"], timeout=20.0):
                        if not await click_by_text(session_id, ["Receber por e-mail", "@gmail.com"], timeout=20.0):
                            raise RuntimeError("Nao foi possivel selecionar o envio do token por e-mail na Azulzinha/Caixa.")
                    await asyncio.sleep(1.0)
                    try:
                        await click_by_text(
                            session_id,
                            ["Continuar", "Confirmar", "Receber codigo", "Enviar codigo"],
                            timeout=4.0,
                        )
                    except Exception:
                        pass
                    await asyncio.sleep(0.8)
                    try:
                        state_local = await wait_for_portal_state_v2(
                            session_id,
                            {"sales", "home", "login", "token", "portal_error", "invalid"},
                            timeout=30.0,
                            description="A Caixa nao exibiu o campo para digitar o token",
                        )
                        token_challenge = await inspect_token_challenge_v2(session_id)
                        if state_local == "invalid":
                            if bool(token_challenge.get("deliveryVisible")) and not bool(token_challenge.get("emailTokenReady")):
                                state_local = "token_delivery"
                            else:
                                state_local = "token"
                    except Exception:
                        await capture_portal_html_debug_v2(session_id, "azulzinha_token_delivery_debug.html")
                        raise
                return state_local

            async def submit_token_value_v2(session_id: str, token: str) -> None:
                confirmed = False
                token_inputs = await eval_js(
                    session_id,
                    """
                    (() => {
                        const visible = (el) => {
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        };
                        return [...document.querySelectorAll('input')]
                            .filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled && visible(el))
                            .map((el) => ({
                                selector: el.id ? `#${el.id}` : '',
                                maxLength: Number(el.maxLength || 0),
                                className: String(el.className || ''),
                            }));
                    })()
                    """,
                    timeout=15.0,
                ) or []
                code_selectors = [
                    str(item.get("selector") or "").strip()
                    for item in token_inputs
                    if str(item.get("selector") or "").strip()
                    and (
                        int(item.get("maxLength") or 0) == 1
                        or "input-code" in str(item.get("className") or "").lower()
                    )
                ]
                token_selectors = code_selectors or [
                    str(item.get("selector") or "").strip()
                    for item in token_inputs
                    if str(item.get("selector") or "").strip()
                ]
                token_digitos = list(str(token))
                if token_selectors and len(token_selectors) > 1 and len(token_digitos) >= len(token_selectors):
                    for idx, selector in enumerate(token_selectors):
                        if not await focus_selector(session_id, selector):
                            continue
                        await eval_js(
                            session_id,
                            f"""
                            (() => {{
                                const el = document.querySelector({selector!r});
                                if (!el) return false;
                                el.value = '';
                                el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                                return true;
                            }})()
                            """,
                            timeout=10.0,
                        )
                        await cdp("Input.insertText", {"text": token_digitos[idx]}, session_id=session_id)
                        await asyncio.sleep(0.08)
                    confirmed = True
                else:
                    confirmed = bool(
                        await eval_js(
                            session_id,
                            f"""
                            (() => {{
                                const token = {token!r};
                                const setNativeValue = (el, value) => {{
                                    const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value')?.set;
                                    if (setter) setter.call(el, value); else el.value = value;
                                    el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                                    el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                                    el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                                }};
                                const inputs = [...document.querySelectorAll('input')].filter((el) => (el.type || '').toLowerCase() !== 'hidden' && !el.disabled);
                                if (inputs.length) {{
                                    setNativeValue(inputs[inputs.length - 1], '');
                                    setNativeValue(inputs[inputs.length - 1], token);
                                    return true;
                                }}
                                return false;
                            }})()
                            """,
                            timeout=15.0,
                        )
                    )
                if not confirmed:
                    raise RuntimeError("Nao foi possivel preencher o token da Azulzinha/Caixa.")
                await asyncio.sleep(0.4)
                try:
                    await wait_for_condition(
                        session_id,
                        """
                        (() => {
                            const botao = document.querySelector('#b2-b1-confirmar');
                            return botao && !botao.disabled;
                        })()
                        """,
                        timeout=5.0,
                    )
                except Exception:
                    pass
                await eval_js(
                    session_id,
                    """
                    (() => {
                        const buttons = [...document.querySelectorAll('button, input[type="submit"], a')];
                        const button = buttons.find((el) => /CONFIRMAR|VALIDAR|ENTRAR|CONTINUAR/i.test(el.innerText || el.value || '')) || buttons[0];
                        button?.click();
                        return true;
                    })()
                    """,
                    timeout=10.0,
                )

            async def complete_token_challenge_v2(session_id: str, initial_state: str) -> str:
                state = str(initial_state or "").strip() or await get_portal_state_v2(session_id)
                ultimo_token_usado = ""
                _emit_pix_status(on_status, "Solicitando token por e-mail...")
                state = await request_token_via_email_v2(session_id, state, force_refresh=False)
                if state == "token":
                    await wait_for_token_email_delivery_grace_v2()
                    state = await get_portal_state_v2(session_id)
                if state in {"sales", "home", "login", "portal_error"}:
                    return state

                for tentativa_token in range(3):
                    if tentativa_token > 0:
                        espera_extra_apos_rejeicao = 5.0
                        _emit_pix_status(
                            on_status,
                            f"Token rejeitado pela Caixa; descartando o codigo anterior e aguardando {int(espera_extra_apos_rejeicao)}s por um novo e-mail...",
                        )
                        await asyncio.sleep(espera_extra_apos_rejeicao)
                        state = await get_portal_state_v2(session_id)
                        if state in {"sales", "home", "login", "portal_error"}:
                            return state
                        if state == "device":
                            state = await perform_device_selection_step_v2(session_id)
                            if state in {"sales", "home", "login", "portal_error"}:
                                return state
                        token_challenge = await inspect_token_challenge_v2(session_id)
                        precisa_reenviar_token = False
                        if state == "token_delivery":
                            precisa_reenviar_token = not bool(token_challenge.get("emailTokenReady"))
                        elif state == "token":
                            precisa_reenviar_token = bool(token_challenge.get("appTokenVisible"))
                        elif state == "invalid":
                            precisa_reenviar_token = bool(token_challenge.get("appTokenVisible")) or (
                                bool(token_challenge.get("deliveryVisible")) and not bool(token_challenge.get("emailTokenReady"))
                            )
                        if precisa_reenviar_token:
                            state = await request_token_via_email_v2(session_id, state, force_refresh=True)
                            if state == "token":
                                state = await get_portal_state_v2(session_id)
                            elif state in {"sales", "home", "login", "portal_error"}:
                                return state
                        else:
                            _emit_pix_status(
                                on_status,
                                "A Caixa manteve a tela de digitacao do token; aguardando um novo e-mail sem reenviar o codigo.",
                            )

                    espera_token = 180.0 if tentativa_token == 0 else 150.0
                    token, portal_state_during_fetch = await fetch_token_with_portal_watch_v2(
                        session_id,
                        espera_token,
                        tentativa_token == 0,
                    )
                    if portal_state_during_fetch in {"sales", "home", "login", "portal_error"}:
                        return portal_state_during_fetch
                    if (not token or token == ultimo_token_usado or token in tokens_descartados_globais_v2) and callable(token_callback):
                        token = str(token_callback("Informe o token enviado por e-mail pela Azulzinha/Caixa") or "").strip()
                    if token in tokens_descartados_globais_v2:
                        _emit_pix_status(on_status, "O token informado ja foi rejeitado anteriormente pela Caixa.")
                        token = ""
                    if not token:
                        if tentativa_token >= 2:
                            raise RuntimeError("Nao foi possivel obter um token novo enviado por e-mail pela Caixa.")
                        _emit_pix_status(on_status, "Ainda nao chegou um token novo da Caixa; aguardando mais um pouco antes da proxima tentativa.")
                        continue

                    state_before_submit = await get_portal_state_v2(session_id)
                    if state_before_submit in {"sales", "home", "login", "portal_error"}:
                        return state_before_submit
                    token_challenge_before_submit = await inspect_token_challenge_v2(session_id)
                    if state_before_submit == "token_delivery" and not bool(token_challenge_before_submit.get("emailTokenReady")):
                        state_before_submit = await request_token_via_email_v2(session_id, state_before_submit, force_refresh=False)
                        if state_before_submit in {"sales", "home", "login", "portal_error"}:
                            return state_before_submit

                    ultimo_token_usado = token
                    _emit_pix_status(on_status, f"Confirmando token da Caixa: {token}...")
                    await submit_token_value_v2(session_id, token)
                    _emit_pix_status(on_status, "Aguardando a Caixa validar o token...")
                    await asyncio.sleep(1.5)
                    resultado_token = await wait_for_post_token_resolution_v2(session_id)
                    if not resultado_token:
                        _emit_pix_status(
                            on_status,
                            "Validando a sessao da Caixa pela abertura de MinhasVendas...",
                        )
                        confirmacao_sessao = await confirm_sales_access_after_token_v2(session_id)
                        if confirmacao_sessao:
                            resultado_token = confirmacao_sessao

                    if resultado_token not in {"sales", "home", "invalid", "token", "token_delivery", "login", "portal_error"}:
                        resultado_token = await confirm_sales_access_after_token_v2(session_id)

                    if resultado_token == "sales":
                        return "sales"
                    if resultado_token == "home":
                        return "home"
                    if resultado_token == "login":
                        _emit_pix_status(
                            on_status,
                            "A Caixa voltou para a tela de login apos validar o token; refazendo a autenticacao...",
                        )
                        return "login"
                    if resultado_token == "portal_error":
                        _emit_pix_status(
                            on_status,
                            "A Caixa exibiu um erro do portal ao confirmar o token; refazendo a autenticacao...",
                        )
                        await capture_portal_html_debug_v2(session_id, "azulzinha_post_token_error.html")
                        return "portal_error"

                    tokens_descartados_globais_v2.add(token)
                    if tentativa_token >= 2:
                        raise RuntimeError("O token informado pela Caixa nao foi aceito apos multiplas tentativas.")
                raise RuntimeError("A Caixa nao concluiu a validacao do token.")

            async def open_sales_area_from_home_v2(session_id: str, context_label: str) -> str:
                _emit_pix_status(on_status, "Abrindo Relatorio de vendas da Caixa...")

                async def _click_sales_report_entry() -> bool:
                    return bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                                const visible = (el) => {
                                    if (!el) return false;
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return (
                                        rect.width > 0 &&
                                        rect.height > 0 &&
                                        rect.bottom > 0 &&
                                        rect.right > 0 &&
                                        rect.top < window.innerHeight &&
                                        rect.left < window.innerWidth &&
                                        style.visibility !== 'hidden' &&
                                        style.display !== 'none'
                                    );
                                };
                                const trigger = (el) => {
                                    if (!el) return false;
                                    const clickable = el.closest('li[opt], a, button, div') || el;
                                    clickable.scrollIntoView({ block: 'center', inline: 'center' });
                                    clickable.focus?.();
                                    clickable.dispatchEvent(new MouseEvent('mousedown', { bubbles: true, cancelable: true, view: window }));
                                    clickable.click();
                                    clickable.dispatchEvent(new MouseEvent('mouseup', { bubbles: true, cancelable: true, view: window }));
                                    return true;
                                };
                                const selectors = [
                                    'a[data-testid="menu-relatorio-vendas"]',
                                    'a[data-testid="m-menu-relatorio-vendas"]',
                                ];
                                for (const selector of selectors) {
                                    const el = document.querySelector(selector);
                                    if (!el || !visible(el)) continue;
                                    return trigger(el);
                                }
                                return false;
                            })()
                            """,
                            timeout=10.0,
                        )
                    )

                abriu_vendas = await _click_sales_report_entry()
                if not abriu_vendas:
                    expanded = bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                                const visible = (el) => {
                                    if (!el) return false;
                                    const rect = el.getBoundingClientRect();
                                    const style = getComputedStyle(el);
                                    return (
                                        rect.width > 0 &&
                                        rect.height > 0 &&
                                        rect.bottom > 0 &&
                                        rect.right > 0 &&
                                        rect.top < window.innerHeight &&
                                        rect.left < window.innerWidth &&
                                        style.visibility !== 'hidden' &&
                                        style.display !== 'none'
                                    );
                                };
                                const trigger = (el) => {
                                    if (!el) return false;
                                    const clickable = el.closest('li[opt], a, button, div') || el;
                                    clickable.scrollIntoView({ block: 'center', inline: 'center' });
                                    clickable.focus?.();
                                    clickable.dispatchEvent(new MouseEvent('mousedown', { bubbles: true, cancelable: true, view: window }));
                                    clickable.click();
                                    clickable.dispatchEvent(new MouseEvent('mouseup', { bubbles: true, cancelable: true, view: window }));
                                    return true;
                                };
                                const selectors = [
                                    'a[data-testid="menu-vendas"]',
                                    'a[data-testid="m-menu-vendas"]',
                                    'a[data-testid="home-card-personalizar-link-vendas"]',
                                ];
                                for (const selector of selectors) {
                                    const el = document.querySelector(selector);
                                    if (!el || !visible(el)) continue;
                                    return trigger(el);
                                }
                                return false;
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                    if expanded:
                        await asyncio.sleep(1.0)
                        abriu_vendas = await _click_sales_report_entry()
                if not abriu_vendas:
                    try:
                        abriu_vendas = await click_by_text(
                            session_id,
                            ["Relatório de vendas", "Relatorio de vendas"],
                            timeout=10.0,
                        )
                    except Exception:
                        abriu_vendas = False
                if abriu_vendas:
                    await asyncio.sleep(1.0)
                    try:
                        state_after_click = await wait_for_portal_state_v2(
                            session_id,
                            {"sales", "login", "device", "token_delivery", "token", "portal_error", "invalid", "captcha_manual"},
                            timeout=60.0,
                            description=f"A Caixa nao abriu o Relatorio de vendas para {context_label}",
                        )
                    except TimeoutError:
                        # A pagina de Vendas as vezes carrega o layout antes dos dados; nao
                        # forcar outra navegacao aqui evita recarregar o portal repetidas
                        # vezes, o que a Caixa trata como comportamento suspeito.
                        state_after_click = "home"
                    _emit_pix_status(on_status, f"Estado do portal apos abrir Relatorio de vendas: {state_after_click or 'desconhecido'}.")
                    if state_after_click != "home":
                        return state_after_click

                await navigate(session_id, credenciais["sales_url"])
                try:
                    state_after_navigation = await wait_for_portal_state_v2(
                        session_id,
                        {"sales", "login", "device", "token_delivery", "token", "portal_error", "invalid", "captcha_manual"},
                        timeout=90.0,
                        description=f"A Caixa nao abriu a area de vendas para {context_label}",
                    )
                except TimeoutError:
                    state_after_navigation = "home"
                _emit_pix_status(on_status, f"Estado do portal apos abrir a URL da area de vendas: {state_after_navigation or 'desconhecido'}.")
                return state_after_navigation

            async def ensure_authenticated_sales_area(session_id: str, kind: str, context_label: str) -> None:
                last_state = ""
                for cycle in range(4):
                    _check_cancelled()
                    state = await get_portal_state_v2(session_id)
                    last_state = state or last_state

                    if state in {"", "loading", "unknown"}:
                        if cycle == 0:
                            _emit_pix_status(on_status, "Acessando Azulzinha/Caixa...")
                            await navigate(session_id, credenciais["login_url"])
                        else:
                            await navigate(session_id, credenciais["sales_url"])
                        state = await wait_for_portal_state_v2(
                            session_id,
                            {"sales", "home", "login", "device", "token_delivery", "token", "portal_error", "invalid", "captcha_manual"},
                            timeout=90.0,
                            description=f"A Caixa nao exibiu a tela esperada para {context_label}",
                        )
                        last_state = state

                    if state == "captcha_manual":
                        state = await wait_for_manual_captcha_resolution_v2(session_id)
                        last_state = state or last_state

                    if state == "portal_error":
                        _emit_pix_status(
                            on_status,
                            f"A Caixa abriu a pagina de erro ao acessar {context_label}; recarregando o portal...",
                        )
                        await capture_portal_html_debug_v2(session_id, f"azulzinha_portal_error_{kind}.html")
                        await asyncio.sleep(2.0)
                        await navigate(session_id, credenciais["login_url"])
                        continue

                    if state in {"login", "device", "token_delivery", "token", "invalid"}:
                        if state == "login":
                            state = await perform_login_step_v2(session_id)
                        if state == "device":
                            state = await perform_device_selection_step_v2(session_id)
                        if state in {"token_delivery", "token", "invalid"}:
                            state = await complete_token_challenge_v2(session_id, state)
                        last_state = state

                    if state == "home":
                        state = await open_sales_area_from_home_v2(session_id, context_label)
                        last_state = state or last_state

                    if state == "sales":
                        try:
                            await wait_for_portal_settle(
                                session_id,
                                timeout=25.0,
                                context_label=f"abrir {context_label}",
                            )
                            return
                        except Exception:
                            state = await get_portal_state_v2(session_id)
                            last_state = state or last_state
                            if state in {"login", "portal_error"}:
                                continue
                            raise

                    if state == "portal_error":
                        _emit_pix_status(
                            on_status,
                            f"A Caixa abriu a pagina de erro durante a autenticacao de {context_label}; tentando novamente...",
                        )
                        await capture_portal_html_debug_v2(session_id, f"azulzinha_auth_error_{kind}.html")
                        await asyncio.sleep(2.0)
                        await navigate(session_id, credenciais["login_url"])
                        continue

                    if state == "login":
                        await asyncio.sleep(2.0)
                        continue

                    # `open_sales_area_from_home_v2` ja foi tentado acima quando state == "home".
                    # Nao tentar de novo aqui: cada tentativa pode envolver uma navegacao completa,
                    # e recarregar o portal repetidas vezes no mesmo ciclo e o que faz a Caixa
                    # escalar para um captcha manual. So aguardar um pouco e deixar o proximo
                    # ciclo reler o estado (a pagina pode so estar terminando de carregar).
                    await asyncio.sleep(2.0)
                    continue

                if AZULZINHA_DEBUG_ARTIFACTS_ENABLED:
                    try:
                        network_events = [
                            {
                                "method": event.get("method"),
                                "requestId": (event.get("params") or {}).get("requestId"),
                                "url": ((event.get("params") or {}).get("request") or {}).get("url")
                                or ((event.get("params") or {}).get("response") or {}).get("url"),
                                "status": ((event.get("params") or {}).get("response") or {}).get("status"),
                                "type": (event.get("params") or {}).get("type"),
                                "errorText": (event.get("params") or {}).get("errorText"),
                            }
                            for event in event_log
                            if str(event.get("method") or "").startswith("Network.")
                        ]
                        (artifacts_dir / f"azulzinha_network_debug_{kind}.json").write_text(
                            json.dumps(network_events[-200:], ensure_ascii=False, indent=2),
                            encoding="utf-8",
                        )
                        response_bodies = []
                        seen_request_ids = set()
                        for event in event_log:
                            params = event.get("params") or {}
                            response = params.get("response") or {}
                            url = str(response.get("url") or "")
                            request_id = str(params.get("requestId") or "")
                            if not request_id or request_id in seen_request_ids:
                                continue
                            if "ActionLoginDevicesApi" not in url:
                                continue
                            seen_request_ids.add(request_id)
                            try:
                                body = await cdp("Network.getResponseBody", {"requestId": request_id}, session_id=session_id, timeout=10.0)
                            except Exception as exc:
                                body = {"error": str(exc)}
                            response_bodies.append({"url": url, "requestId": request_id, "body": body})
                        if response_bodies:
                            (artifacts_dir / f"azulzinha_login_response_debug_{kind}.json").write_text(
                                json.dumps(response_bodies[-10:], ensure_ascii=False, indent=2),
                                encoding="utf-8",
                            )
                    except Exception:
                        pass
                await capture_portal_html_debug_v2(session_id, f"azulzinha_sales_area_debug_{kind}.html")
                raise RuntimeError(
                    f"A Caixa não concluiu a autenticação para abrir {context_label}. Último estado observado: {last_state or 'desconhecido'}."
                )

            _new_vendas_unified_cache: dict[str, dict[str, str | None]] = {}

            async def click_selector_native_retry(
                session_id: str,
                selector: str,
                attempts: int = 6,
                delay: float = 0.5,
            ) -> bool:
                # A tela nova de Vendas re-renderiza trechos da UI apos filtros/aplicacoes
                # (ex.: trocar o periodo), entao um elemento que acabou de ficar visivel pode
                # sumir por um instante durante o re-render. Uma unica tentativa de clique e
                # fragil aqui; repetir por alguns instantes cobre esse intervalo.
                for _ in range(attempts):
                    if await click_selector_native(session_id, selector):
                        return True
                    await asyncio.sleep(delay)
                return False

            async def dismiss_new_vendas_onboarding_v2(session_id: str) -> None:
                # Em perfis de navegador novos a Caixa mostra um tour de onboarding
                # ("Menu de vendas ainda melhor!") sobre a tela de Vendas, que bloqueia
                # os cliques em Exportar/Gerar arquivo ate ser dispensado.
                try:
                    await click_by_text(session_id, ["Pular", "Fechar", "Entendi"], timeout=3.0)
                except Exception:
                    pass
                return False

            async def is_new_vendas_screen_v2(session_id: str) -> bool:
                return bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                            const el = document.querySelector('[data-testid="vendas-btn-exportar"]');
                            if (!el) return false;
                            const rect = el.getBoundingClientRect();
                            const style = getComputedStyle(el);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                        })()
                        """,
                        timeout=10.0,
                    )
                )

            async def set_new_vendas_period_v2(session_id: str) -> None:
                today_br = datetime.now().strftime("%d/%m/%Y")
                if data_br == today_br:
                    await click_selector_native_retry(session_id, '[data-testid="vendas-periodo-hoje"]')
                    await asyncio.sleep(0.4)
                    return
                opened = await click_selector_native_retry(session_id, '[data-testid="vendas-periodo-outros"]')
                if not opened:
                    raise RuntimeError("Não foi possível abrir o seletor de período na nova tela de Vendas da Caixa.")
                await asyncio.sleep(0.6)
                await insert_text(session_id, 'input[id$="FilterDateInit"]', data_br)
                await insert_text(session_id, 'input[id$="FilterDateEnd"]', data_br)
                applied = await click_selector_native_retry(session_id, '[data-testid="generic-calendar-button-aplicar"]')
                if not applied:
                    raise RuntimeError("Não foi possível aplicar o período selecionado na nova tela de Vendas da Caixa.")
                await asyncio.sleep(1.0)

            async def export_new_vendas_report_v2(session_id: str) -> str:
                await dismiss_new_vendas_onboarding_v2(session_id)
                opened = await click_selector_native_retry(session_id, '[data-testid="vendas-btn-exportar"]')
                if not opened:
                    raise RuntimeError("Não foi possível abrir o modal de exportação na nova tela de Vendas da Caixa.")
                await asyncio.sleep(0.6)
                await dismiss_new_vendas_onboarding_v2(session_id)
                started_at = _download_start_time()
                gerar = await click_selector_native_retry(session_id, '[data-testid="historico-vendas-gerar-arquivo"]')
                if not gerar:
                    raise RuntimeError("Não foi possível clicar em 'Gerar arquivo' na nova tela de Vendas da Caixa.")

                deadline = time.time() + 90.0
                downloaded: Path | None = None
                while time.time() < deadline:
                    _check_cancelled()
                    try:
                        candidates = sorted(
                            Path(browser_download_dir).glob("Relatorio_Simplificado_Vendas_*.xlsx"),
                            key=lambda item: item.stat().st_mtime,
                            reverse=True,
                        )
                    except Exception:
                        candidates = []
                    for candidate in candidates:
                        try:
                            if candidate.stat().st_mtime >= started_at - 2:
                                downloaded = candidate
                                break
                        except Exception:
                            continue
                    if downloaded:
                        break
                    await asyncio.sleep(0.6)
                if not downloaded:
                    raise RuntimeError("A Caixa não entregou o arquivo da nova tela de Vendas.")
                return str(downloaded)

            async def get_new_vendas_report_paths_v2(session_id: str) -> dict[str, str | None]:
                cache_key = f"{company_norm}:{data_br}"
                cached = _new_vendas_unified_cache.get(cache_key)
                if cached is not None:
                    return cached
                await dismiss_new_vendas_onboarding_v2(session_id)
                await set_new_vendas_period_v2(session_id)
                try:
                    await wait_for_portal_settle(
                        session_id,
                        timeout=20.0,
                        context_label="carregar a lista de vendas apos aplicar o periodo",
                    )
                except Exception:
                    pass
                downloaded_path = await export_new_vendas_report_v2(session_id)
                result = _write_azulzinha_unified_report_files(downloaded_path, data_br, company_norm, download_dir)
                _new_vendas_unified_cache[cache_key] = result
                return result

            async def download_report(session_id: str, kind: str) -> str | None:
                context_label = f"o relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'}"
                export_ready_timeout = 60.0 if kind == "pix" else 35.0
                captured_timeout = 25.0 if kind == "pix" else 12.0
                download_timeout = 120.0 if kind == "pix" else 80.0
                today_br = datetime.now().strftime("%d/%m/%Y")
                use_today_tab = kind == "cartoes" and data_br == today_br
                active_tab_id = "Hoje" if use_today_tab else ("HistoricoVendas" if kind == "cartoes" else "Pix")
                last_error = None

                def _copy_establishment_variant(saved_path: str, establishment_id: str) -> str | None:
                    try:
                        source = Path(saved_path)
                    except Exception:
                        return None
                    if not source.exists():
                        return None
                    target = source.with_name(f"{source.stem}_est{establishment_id}{source.suffix}")
                    try:
                        shutil.copy2(source, target)
                        return str(target)
                    except Exception:
                        return None

                def _combine_establishment_reports(
                    captured_paths: list[tuple[str, str]],
                    report_kind: str,
                ) -> str | None:
                    if not captured_paths:
                        return None
                    if len(captured_paths) == 1:
                        return captured_paths[0][0]
                    if report_kind == "cartoes":
                        columns = [
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
                            "Final do cartão",
                            "Cód. Ref. Cartão",
                        ]
                        rows_out: list[dict[str, object]] = []
                        seen: set[tuple[str, str, float, str, str]] = set()
                        for path_value, establishment_id in captured_paths:
                            reports = _build_card_reports_from_caixa(path_value, data_br)
                            for report_key, produto in (
                                ("cartao_credito_caixa", "Crédito"),
                                ("cartao_debito_caixa", "Débito"),
                            ):
                                for item in list((reports.get(report_key) or {}).get("itens_autorizados") or []):
                                    numero = str(item.get("numero") or "").strip()
                                    data_venda = str(item.get("data_venda") or "").strip()
                                    valor = round(float(item.get("valor_bruto", 0.0) or 0.0), 2)
                                    dedupe_key = (numero, data_venda, valor, produto, str(establishment_id or "").strip())
                                    if dedupe_key in seen:
                                        continue
                                    seen.add(dedupe_key)
                                    rows_out.append(
                                        {
                                            "Data da venda": data_venda,
                                            "Cód. de autorização": numero,
                                            "Comprovante da venda": item.get("numero_exibicao") or numero,
                                            "Produto": produto,
                                            "Parcelado": "-",
                                            "Bandeira": "",
                                            "Canal": "",
                                            "Terminal": "",
                                            "Valor bruto": valor,
                                            "Status": "Autorizada",
                                            "Número do estabelecimento": establishment_id,
                                            "Final do cartão": "",
                                            "Cód. Ref. Cartão": "",
                                        }
                                    )
                        if not rows_out:
                            return None
                        final_path = artifacts_dir / f"Historico_Simplificado_de_vendas_{data_br.replace('/', '-')}_{company_norm}_auto.xlsx"
                        import pandas as pd

                        pd.DataFrame(rows_out, columns=columns).to_excel(final_path, index=False)
                        return str(final_path)

                    headers = ["Data da venda", "Cód. de autorização", "Valor bruto", "Status"]
                    rows_out: list[dict[str, object]] = []
                    seen: set[tuple[str, str, float, str]] = set()
                    for path_value, _establishment_id in captured_paths:
                        suffix = _effective_local_report_suffix(path_value)
                        if suffix == ".csv":
                            report = _build_pix_report_from_caixa_csv(path_value, data_br)
                        elif suffix in {".xlsx", ".xls"}:
                            report = _build_pix_report_from_caixa_xlsx(path_value, data_br)
                        else:
                            report = _build_pix_report_from_caixa_pdf(path_value, data_br)
                        for item in list(report.get("itens_autorizados") or []):
                            data_venda = str(item.get("data_venda") or "").strip()
                            codigo = str(item.get("nome") or "").strip()
                            valor = round(float(item.get("valor_bruto", 0.0) or 0.0), 2)
                            status = str(item.get("situacao") or "").strip() or "APROVADA"
                            dedupe_key = (data_venda, codigo, valor, status)
                            if dedupe_key in seen:
                                continue
                            seen.add(dedupe_key)
                            rows_out.append(
                                {
                                    "Data da venda": data_venda,
                                    "Cód. de autorização": codigo,
                                    "Valor bruto": valor,
                                    "Status": status,
                                }
                            )
                    if not rows_out:
                        return None
                    final_path = artifacts_dir / f"Relatorio_de_Vendas_Pix_{data_br.replace('/', '-')}_{company_norm}_auto.csv"
                    with open(final_path, "w", encoding="utf-8-sig", newline="") as handle:
                        writer = csv.DictWriter(handle, fieldnames=headers, delimiter=";")
                        writer.writeheader()
                        for row in rows_out:
                            writer.writerow(row)
                    return str(final_path)

                async def export_current_selection(
                    *,
                    captured_timeout_override: float | None = None,
                    download_timeout_override: float | None = None,
                ) -> str | None:
                    await wait_for_export_ready(session_id, kind, tab_id=active_tab_id, timeout=export_ready_timeout)
                    await asyncio.sleep(0.25)
                    started_at = _download_start_time()
                    event_start_index = len(event_log)
                    _emit_pix_status(on_status, f"Solicitando arquivo de {'cartões' if kind == 'cartoes' else 'PIX'} para a Caixa...")
                    await click_export(session_id, "pix" if kind == "pix" else "cartoes", tab_id=active_tab_id)
                    captured = await wait_for_captured_report(
                        session_id,
                        kind,
                        event_start_index,
                        started_at,
                        timeout=captured_timeout_override if captured_timeout_override is not None else captured_timeout,
                    )
                    if captured:
                        _emit_pix_status(on_status, f"Relatório de {'cartões' if kind == 'cartoes' else 'PIX'} recebido e validado.")
                        return captured
                    _emit_pix_status(on_status, f"Aguardando o download final do relatório de {'cartões' if kind == 'cartoes' else 'PIX'}...")
                    return _persist_downloaded_report(
                        _wait_for_downloaded_report(
                            browser_download_dir,
                            data_br,
                            kind,
                            started_at,
                            timeout=download_timeout_override if download_timeout_override is not None else download_timeout,
                        ),
                        kind,
                    )

                for attempt in range(2):
                    try:
                        await ensure_authenticated_sales_area(session_id, kind, context_label)
                        if await is_new_vendas_screen_v2(session_id):
                            _emit_pix_status(
                                on_status,
                                f"Usando a nova tela de Vendas da Caixa para baixar o relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'}...",
                            )
                            paths = await get_new_vendas_report_paths_v2(session_id)
                            saved = paths.get(kind)
                            if saved:
                                return saved
                            raise RuntimeError(
                                f"A nova tela de Vendas da Caixa não retornou transações de {'cartões' if kind == 'cartoes' else 'PIX'} para o período solicitado."
                            )
                        if kind == "cartoes":
                            _emit_pix_status(on_status, "Baixando relatorio de cartoes da Caixa...")
                            await activate_sales_tab(session_id, active_tab_id, timeout=35.0)
                            await wait_for_tab_content(session_id, active_tab_id, timeout=45.0)
                            await wait_for_portal_settle(
                                session_id,
                                tab_id=active_tab_id,
                                timeout=20.0,
                                context_label=f"estabilizar a aba {active_tab_id}",
                            )
                        else:
                            _emit_pix_status(on_status, "Baixando relatório PIX da Caixa...")
                            await activate_sales_tab(session_id, active_tab_id, timeout=35.0)
                            await wait_for_tab_content(session_id, active_tab_id, timeout=60.0)
                            await wait_for_portal_settle(
                                session_id,
                                tab_id=active_tab_id,
                                timeout=25.0,
                                context_label=f"estabilizar a aba {active_tab_id}",
                            )
                        await asyncio.sleep(1.0)
                        if use_today_tab:
                            _emit_pix_status(on_status, "Usando a aba Hoje da Caixa para baixar o relatório de cartões do dia corrente...")
                        else:
                            _emit_pix_status(on_status, f"Aplicando filtro de data do relatório de {'cartões' if kind == 'cartoes' else 'PIX'}...")
                            await set_date_inputs(session_id)
                            await wait_for_portal_settle(
                                session_id,
                                tab_id=active_tab_id,
                                timeout=25.0 if kind == "pix" else 20.0,
                                context_label=f"aplicar a data do relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'}",
                            )
                        establishment_options = await list_establishment_filter_options(
                            session_id,
                            active_tab_id,
                            timeout=25.0,
                        )
                        if company_norm == "mva" and len(establishment_options) > 1:
                            _emit_pix_status(
                                on_status,
                                f"Baixando o relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'} separadamente para cada estabelecimento da MVA...",
                            )
                            captured_paths: list[tuple[str, str]] = []
                            for establishment_id in establishment_options:
                                _emit_pix_status(
                                    on_status,
                                    f"Aplicando o estabelecimento {establishment_id} na Caixa antes da exportacao...",
                                )
                                applied_count = await apply_establishment_filter_selection(
                                    session_id,
                                    active_tab_id,
                                    [establishment_id],
                                    timeout=25.0,
                                )
                                if applied_count <= 0:
                                    continue
                                if await tab_has_no_results(session_id, active_tab_id, timeout=6.0):
                                    _emit_pix_status(
                                        on_status,
                                        f"O estabelecimento {establishment_id} nao tem resultados na Caixa; pulando a exportacao.",
                                    )
                                    if captured_paths:
                                        _emit_pix_status(
                                            on_status,
                                            "A MVA ja tinha um estabelecimento valido; ignorando os estabelecimentos restantes sem resultado.",
                                        )
                                        break
                                    continue
                                _emit_pix_status(on_status, f"Preparando exportacao do relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'}...")
                                per_establishment_captured_timeout = captured_timeout
                                per_establishment_download_timeout = download_timeout
                                if captured_paths:
                                    per_establishment_captured_timeout = min(
                                        captured_timeout,
                                        12.0 if kind == "cartoes" else 15.0,
                                    )
                                    per_establishment_download_timeout = min(
                                        download_timeout,
                                        15.0 if kind == "cartoes" else 20.0,
                                    )
                                try:
                                    saved = await export_current_selection(
                                        captured_timeout_override=per_establishment_captured_timeout,
                                        download_timeout_override=per_establishment_download_timeout,
                                    )
                                except Exception as exc:
                                    _emit_pix_status(
                                        on_status,
                                        f"A Caixa não devolveu um arquivo válido para o estabelecimento {establishment_id}; seguindo com os demais. Motivo: {exc}",
                                    )
                                    if captured_paths:
                                        _emit_pix_status(
                                            on_status,
                                            "A MVA já tinha um estabelecimento válido; ignorando os estabelecimentos restantes que falharam.",
                                        )
                                        break
                                    continue
                                if not saved:
                                    _emit_pix_status(
                                        on_status,
                                        f"O estabelecimento {establishment_id} não gerou arquivo aproveitável na Caixa; seguindo com os demais.",
                                    )
                                    if captured_paths:
                                        _emit_pix_status(
                                            on_status,
                                            "A MVA já tinha um estabelecimento válido; ignorando os estabelecimentos restantes que não geraram arquivo.",
                                        )
                                        break
                                    continue
                                variant_path = _copy_establishment_variant(saved, establishment_id)
                                if variant_path:
                                    captured_paths.append((variant_path, establishment_id))
                            combined = _combine_establishment_reports(captured_paths, kind)
                            if combined:
                                return combined
                            raise RuntimeError(
                                f"A Caixa não entregou um arquivo válido do relatório de {'cartões' if kind == 'cartoes' else 'PIX'} para os estabelecimentos da MVA."
                            )
                        establishments_applied = await ensure_all_establishments_selected(
                            session_id,
                            active_tab_id,
                            timeout=25.0,
                        )
                        if establishments_applied:
                            _emit_pix_status(
                                on_status,
                                "Aplicados todos os estabelecimentos disponiveis no filtro da Caixa antes da exportacao...",
                            )
                        _emit_pix_status(on_status, f"Preparando exportacao do relatorio de {'cartoes' if kind == 'cartoes' else 'PIX'}...")
                        saved = await export_current_selection()
                        if saved:
                            return saved
                        raise RuntimeError(
                            f"A Caixa não entregou o arquivo final do relatório de {'cartões' if kind == 'cartoes' else 'PIX'}."
                        )
                    except Exception as exc:
                        last_error = exc
                        if attempt >= 1:
                            raise
                        try:
                            current_state = str(await eval_js(session_id, sales_area_state_expression, timeout=10.0) or "").strip()
                        except Exception:
                            current_state = ""
                        if current_state == "portal_error" or "_error.html" in str(exc).lower():
                            retry_message = (
                                f"A Caixa abriu a página de erro ao gerar o relatório de {'cartões' if kind == 'cartoes' else 'PIX'}; tentando novamente..."
                            )
                        else:
                            retry_message = (
                                f"A Caixa demorou para gerar o relatório de {'cartões' if kind == 'cartoes' else 'PIX'}; tentando novamente..."
                            )
                        _emit_pix_status(
                            on_status,
                            retry_message,
                        )
                        await asyncio.sleep(2.0)
                if last_error:
                    raise last_error
                return None

            try:
                target_id = (await cdp("Target.createTarget", {"url": "about:blank"})).get("targetId")
                if not target_id:
                    raise RuntimeError("Não foi possível abrir a aba da Azulzinha/Caixa.")
                try:
                    await cdp("Target.activateTarget", {"targetId": target_id}, timeout=5.0)
                except Exception:
                    pass
                session_id = (await cdp("Target.attachToTarget", {"targetId": target_id, "flatten": True})).get("sessionId")
                if not session_id:
                    raise RuntimeError("Não foi possível anexar a aba da Azulzinha/Caixa.")
                await cdp("Page.enable", session_id=session_id)
                await cdp("Runtime.enable", session_id=session_id)
                try:
                    await cdp("Page.bringToFront", session_id=session_id, timeout=5.0)
                except Exception:
                    pass
                if not browser_visible_debug:
                    await _hide_chromium_window(cdp, target_id)
                try:
                    await cdp("Network.enable", {}, session_id=session_id)
                except Exception:
                    pass
                try:
                    await cdp("Browser.setDownloadBehavior", {"behavior": "allow", "downloadPath": browser_download_dir, "eventsEnabled": True})
                except Exception:
                    pass
                try:
                    await cdp(
                        "Page.setDownloadBehavior",
                        {"behavior": "allow", "downloadPath": browser_download_dir},
                        session_id=session_id,
                    )
                except Exception:
                    pass
                await ensure_authenticated_sales_area(session_id, company_norm, "a area de vendas")
                resultado = {"pix": None, "cartoes": None, "avisos": []}
                if need_cartoes and not resultado["cartoes"]:
                    resultado["cartoes"] = await download_report(session_id, "cartoes")
                    if not resultado["cartoes"]:
                        resultado["avisos"].append("Não foi possível baixar o relatório de cartões da Azulzinha/Caixa.")
                if need_pix and not resultado["pix"]:
                    resultado["pix"] = await download_report(session_id, "pix")
                    if not resultado["pix"]:
                        resultado["avisos"].append("Não foi possível baixar o relatório PIX da Azulzinha/Caixa.")
                return resultado
            finally:
                recv_task.cancel()
                try:
                    await recv_task
                except BaseException:
                    pass

    _emit_pix_status(on_status, "Abrindo portal da Caixa...")
    proc = _launch_browser_process(chrome_args)
    try:
        return asyncio.run(asyncio.wait_for(_run(), timeout=480.0))
    finally:
        try:
            proc.terminate()
            proc.wait(timeout=5)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass
        shutil.rmtree(profile_dir, ignore_errors=True)
        shutil.rmtree(browser_download_dir, ignore_errors=True)
        _cleanup_azulzinha_debug_artifacts()


def _cielo_report_looks_detailed(path: str | Path) -> bool:
    report_path = Path(path)
    name_norm = _normalize_ascii_text(report_path.name)
    if any(marker in name_norm for marker in ("detalh", "detalhe", "detalhado")):
        return True
    try:
        suffix = _effective_local_report_suffix(report_path)
        if suffix == ".csv":
            text = _read_text_file(str(report_path))[:8000]
            text_norm = _normalize_ascii_text(text)
            return (
                "detalhado de vendas cielo" in text_norm
                or (
                    "data da venda" in text_norm
                    and "hora da venda" in text_norm
                    and any(marker in text_norm for marker in ("codigo de autorizacao", "nsu/doc", "codigo da venda"))
                )
            )
        if suffix == ".xlsx":
            try:
                rows = _collect_card_rows_from_cielo_xlsx(str(report_path))
            except Exception:
                rows = []
            if rows:
                header_text = _normalize_ascii_text(" ".join(str(key) for key in rows[0].keys()))
                return "hora da venda" in header_text and any(
                    marker in header_text for marker in ("codigo de autorizacao", "nsu/doc", "codigo da venda")
                )
    except Exception:
        return False
    return False


def _cielo_report_has_exact_sale_date_range(path: str | Path, data_br: str) -> bool:
    report_path = Path(path)
    suffix = _effective_local_report_suffix(report_path)
    if suffix != ".csv":
        return True
    target = str(data_br or "").strip()
    if not target:
        return True
    data_digits = re.sub(r"\D", "", target)
    exact_iso_range = ""
    if len(data_digits) == 8:
        data_iso_digits = f"{data_digits[4:8]}{data_digits[2:4]}{data_digits[0:2]}"
        exact_iso_range = f"{data_iso_digits}-{data_iso_digits}"
    try:
        text = _read_text_file(str(report_path))[:8000]
    except Exception:
        return False
    for line in text.splitlines()[:40]:
        if "Data da venda:" not in line:
            continue
        dates = re.findall(r"\b\d{2}/\d{2}/\d{4}\b", line)
        return len(dates) >= 2 and dates[0] == target and dates[1] == target
    name_norm = _normalize_ascii_text(report_path.name)
    return bool(exact_iso_range and exact_iso_range in name_norm)


def _wait_for_cielo_downloaded_report(
    download_dir: str,
    data_br: str,
    started_at: float,
    timeout: float = 90.0,
    require_detailed: bool = False,
) -> str | None:
    data_digits = re.sub(r"\D", "", str(data_br or ""))
    data_iso_digits = ""
    if len(data_digits) == 8:
        data_iso_digits = f"{data_digits[4:8]}{data_digits[2:4]}{data_digits[0:2]}"

    def _matches_requested_date(path: Path) -> bool:
        name_norm = _normalize_ascii_text(path.name)
        if data_digits and data_digits in re.sub(r"\D", "", path.name):
            return True
        if data_iso_digits and data_iso_digits in re.sub(r"\D", "", path.name):
            return True
        if data_iso_digits and f"{data_iso_digits}-{data_iso_digits}" in name_norm:
            return True
        return False

    def _find_once() -> str | None:
        fallback: str | None = None
        for pattern in ("*.csv", "*.xlsx", "*.crdownload"):
            candidates = sorted(
                Path(download_dir).glob(pattern),
                key=lambda item: item.stat().st_mtime,
                reverse=True,
            )
            for path in candidates:
                try:
                    if path.stat().st_mtime < started_at - 1:
                        continue
                    effective_suffix = _effective_local_report_suffix(path)
                    if effective_suffix not in {".csv", ".xlsx"} or path.name.endswith(".tmp"):
                        continue
                    normalized_path = _finalize_local_report_path(path)
                    if require_detailed and not _cielo_report_looks_detailed(normalized_path):
                        continue
                    try:
                        reports = _build_card_reports_from_cielo(normalized_path, data_br)
                    except Exception:
                        reports = {}
                    if any((report.get("itens_autorizados") or []) for report in reports.values()):
                        return normalized_path
                    if fallback is None and not require_detailed and _matches_requested_date(Path(normalized_path)):
                        fallback = normalized_path
                except Exception:
                    continue
        return fallback

    found = _find_once()
    if found:
        return found
    deadline = time.time() + timeout
    while time.time() < deadline:
        found = _find_once()
        if found:
            return found
        time.sleep(0.6)
    return None


def _persist_cielo_auto_report(source_path: str, data_br: str) -> str:
    source = Path(source_path)
    suffix = _effective_local_report_suffix(source) or source.suffix.lower() or ".csv"
    safe_date = re.sub(r"\D", "", str(data_br or "")) or datetime.now().strftime("%Y%m%d")
    target_dir = Path(_active_report_dir())
    target_dir.mkdir(parents=True, exist_ok=True)
    target = target_dir / f"cielo_cartoes_{safe_date}_mva_auto{suffix}"
    if target.exists():
        target = target_dir / f"cielo_cartoes_{safe_date}_{int(time.time())}_mva_auto{suffix}"
    try:
        shutil.move(str(source), str(target))
    except Exception:
        shutil.copy2(str(source), str(target))
    return str(target)


def baixar_relatorio_cielo_mva(
    data_br: str,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
) -> dict[str, object]:
    cancel_event = cancel_event or threading.Event()
    cielo_debug_log_path = _new_cielo_debug_log_path(data_br, "MVA") if CIELO_DEBUG_LOGS_ENABLED else None

    def cielo_log(event: str, **details) -> None:
        _write_cielo_debug_log(cielo_debug_log_path, event, **details)

    cielo_log("run_start", data_br=data_br)

    def _check_cancelled() -> None:
        if cancel_event.is_set():
            cielo_log("cancel_requested")
            raise RuntimeError("__cancelled__")

    credenciais = _load_cielo_credentials("MVA")
    if not credenciais:
        cielo_log("credentials_missing")
        return {
            "cartoes": None,
            "avisos": ["As credenciais da Cielo da MVA não foram encontradas no credenciais.txt."],
            "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
        }

    navegador = _find_chromium_browser_path()
    if not navegador:
        cielo_log("browser_missing")
        return {
            "cartoes": None,
            "avisos": ["Nenhum navegador Chromium compatível foi encontrado para baixar o relatório da Cielo."],
            "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
        }

    try:
        data_iso = datetime.strptime(str(data_br or "").strip(), "%d/%m/%Y").strftime("%Y-%m-%d")
    except ValueError as exc:
        cielo_log("invalid_date", data_br=data_br)
        raise ValueError("A data da consulta Cielo é inválida.") from exc
    cielo_log(
        "credentials_loaded",
        email=credenciais.get("email"),
        password_length=len(str(credenciais.get("password") or "")),
        browser=os.path.basename(str(navegador)),
        data_iso=data_iso,
    )

    profile_root = _cielo_browser_profile_dir("MVA")
    profile_dir = tempfile.mkdtemp(prefix="run_mva_", dir=profile_root)
    browser_download_dir = tempfile.mkdtemp(prefix="downloads_mva_", dir=profile_root)
    _prepare_chromium_profile(profile_dir, browser_download_dir)
    port = _pick_free_local_port()
    cielo_log("browser_profile_prepared", port=port, profile_dir=profile_dir, download_dir=browser_download_dir)
    chrome_args = [
        navegador,
        f"--remote-debugging-port={port}",
        f"--user-data-dir={profile_dir}",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-background-networking",
        "--disable-background-timer-throttling",
        "--disable-backgrounding-occluded-windows",
        "--disable-component-update",
        "--disable-popup-blocking",
        "--disable-notifications",
        "--disable-renderer-backgrounding",
        "--deny-permission-prompts",
        "--disable-save-password-bubble",
        "--disable-features=PasswordManagerOnboarding,AutofillServerCommunication",
        "--window-size=1400,900",
        "--window-position=80,60",
        "--disable-gpu",
        str(credenciais.get("login_url") or "https://minhaconta2.cielo.com.br/site/acessos/login"),
    ]

    async def _run() -> dict[str, object]:
        import websockets

        _check_cancelled()
        meta = _wait_for_devtools_ready(port)
        ws_url = str(meta.get("webSocketDebuggerUrl") or "").strip()
        if not ws_url:
            cielo_log("devtools_missing_ws_url", meta=meta)
            raise RuntimeError("Não foi possível conectar ao Chromium para acessar a Cielo.")
        cielo_log("devtools_ready", browser_url=meta.get("Browser"), ws_url_present=bool(ws_url))

        async with websockets.connect(ws_url, max_size=50_000_000) as conn:
            next_id = 0
            pending = {}

            async def recv_loop():
                while True:
                    _check_cancelled()
                    mensagem = json.loads(await conn.recv())
                    if "id" in mensagem and mensagem["id"] in pending:
                        pending.pop(mensagem["id"]).set_result(mensagem)

            recv_task = asyncio.create_task(recv_loop())

            async def cdp(method: str, params: dict | None = None, session_id: str | None = None, timeout: float = 45.0):
                nonlocal next_id
                _check_cancelled()
                next_id += 1
                future = asyncio.get_running_loop().create_future()
                pending[next_id] = future
                mensagem = {"id": next_id, "method": method}
                if params is not None:
                    mensagem["params"] = params
                if session_id:
                    mensagem["sessionId"] = session_id
                await conn.send(json.dumps(mensagem))
                try:
                    resposta = await asyncio.wait_for(future, timeout=timeout)
                finally:
                    pending.pop(next_id, None)
                if "error" in resposta:
                    raise RuntimeError(resposta["error"])
                return resposta.get("result") or {}

            async def eval_js(session_id: str, expression: str, timeout: float = 30.0):
                result = await cdp(
                    "Runtime.evaluate",
                    {"expression": expression, "awaitPromise": True, "returnByValue": True},
                    session_id=session_id,
                    timeout=timeout,
                )
                value = result.get("result") or {}
                return value.get("value")

            async def save_cielo_page_snapshot(session_id: str, label: str) -> None:
                if not CIELO_DEBUG_LOGS_ENABLED:
                    return
                safe_label = re.sub(r"[^a-z0-9_]+", "_", _normalize_ascii_text(label)).strip("_") or "snapshot"
                safe_date = re.sub(r"\D", "", str(data_br or "")) or datetime.now().strftime("%Y%m%d")
                base_path = Path(_active_report_dir()) / f"cielo_snapshot_{safe_date}_{safe_label}_{datetime.now().strftime('%H%M%S')}"
                html_path = base_path.with_suffix(".html")
                png_path = base_path.with_suffix(".png")
                saved: dict[str, str] = {}
                try:
                    html_text = await eval_js(
                        session_id,
                        "document.documentElement ? document.documentElement.outerHTML : ''",
                        timeout=10.0,
                    )
                    html_path.write_text(str(html_text or ""), encoding="utf-8")
                    saved["html"] = str(html_path)
                except Exception as exc:
                    saved["html_error"] = f"{type(exc).__name__}: {exc}"
                try:
                    screenshot = await cdp(
                        "Page.captureScreenshot",
                        {"format": "png", "captureBeyondViewport": False},
                        session_id=session_id,
                        timeout=15.0,
                    )
                    raw_png = base64.b64decode(str(screenshot.get("data") or ""))
                    if raw_png:
                        png_path.write_bytes(raw_png)
                        saved["png"] = str(png_path)
                except Exception as exc:
                    saved["png_error"] = f"{type(exc).__name__}: {exc}"
                cielo_log("page_snapshot_saved", label=label, saved=saved)

            async def dispatch_cielo_native_click(session_id: str, click_result: dict | None) -> bool:
                if not isinstance(click_result, dict):
                    return False
                try:
                    x = float(click_result.get("clickX"))
                    y = float(click_result.get("clickY"))
                except Exception:
                    return False
                if not (0 <= x <= 10000 and 0 <= y <= 10000):
                    return False
                try:
                    await cdp(
                        "Input.dispatchMouseEvent",
                        {"type": "mouseMoved", "x": x, "y": y, "button": "none"},
                        session_id=session_id,
                        timeout=15.0,
                    )
                    await cdp(
                        "Input.dispatchMouseEvent",
                        {"type": "mousePressed", "x": x, "y": y, "button": "left", "clickCount": 1},
                        session_id=session_id,
                        timeout=15.0,
                    )
                    await cdp(
                        "Input.dispatchMouseEvent",
                        {"type": "mouseReleased", "x": x, "y": y, "button": "left", "clickCount": 1},
                        session_id=session_id,
                        timeout=15.0,
                    )
                    return True
                except Exception as exc:
                    cielo_log("native_click_failed", error=str(exc)[:300], error_type=type(exc).__name__, click_result=click_result)
                    return False

            async def visible_text(session_id: str) -> str:
                text = await eval_js(session_id, "document.body ? document.body.innerText : ''", timeout=10.0)
                return str(text or "")

            async def show_cielo_banner(session_id: str, message: str, color: str = "#1d4ed8") -> None:
                try:
                    await eval_js(
                        session_id,
                        f"""
                        (() => {{
                          let banner = document.getElementById('pdfreader-cielo-manual-banner');
                          if (!banner) {{
                            banner = document.createElement('div');
                            banner.id = 'pdfreader-cielo-manual-banner';
                            document.documentElement.appendChild(banner);
                          }}
                          Object.assign(banner.style, {{
                            position: 'fixed',
                            left: '24px',
                            right: '24px',
                            top: '18px',
                            zIndex: '2147483647',
                            padding: '14px 18px',
                            borderRadius: '12px',
                            background: {json.dumps(color)},
                            color: '#fff',
                            font: '700 17px Arial, sans-serif',
                            textAlign: 'center',
                            whiteSpace: 'pre-wrap',
                            boxShadow: '0 14px 36px rgba(0,0,0,.32)'
                          }});
                          banner.textContent = {json.dumps(message)};
                          return true;
                        }})()
                        """,
                        timeout=10.0,
                    )
                except Exception:
                    pass

            async def hide_cielo_banner(session_id: str) -> None:
                try:
                    await eval_js(
                        session_id,
                        "(() => { const banner = document.getElementById('pdfreader-cielo-manual-banner'); if (banner) banner.remove(); return true; })()",
                        timeout=10.0,
                    )
                except Exception:
                    pass

            async def cielo_manual_challenge_present(session_id: str) -> bool:
                try:
                    return bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                              const href = String(location.href || '').toLowerCase();
                              if (href.includes('minhaconta2.cielo.com.br') && !href.includes('acessos/login')) return false;
                              const banner = document.getElementById('pdfreader-cielo-manual-banner');
                              const ownBannerText = banner ? String(banner.innerText || '') : '';
                              const recaptchaResponseFields = [...document.querySelectorAll('textarea[name="g-recaptcha-response"], textarea#g-recaptcha-response, input[name="g-recaptcha-response"]')];
                              const hasRecaptchaResponse = recaptchaResponseFields.some(e => String(e.value || '').trim().length > 20);
                              let grecaptchaResponse = '';
                              try {
                                if (window.grecaptcha && typeof window.grecaptcha.getResponse === 'function') {
                                  grecaptchaResponse = String(window.grecaptcha.getResponse() || '').trim();
                                }
                              } catch (_) {}
                              if (hasRecaptchaResponse || grecaptchaResponse.length > 20) return false;
                              let pageText = String(document.body && document.body.innerText || '');
                              if (ownBannerText) pageText = pageText.replace(ownBannerText, '');
                              const text = pageText
                                .normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                              if (/precisamos validar seu acesso|selecione uma das formas de validacao|e-?mail para|gmail\\.com|digite o codigo|digite o token|codigo enviado|validar codigo|validar token|verificar codigo|verificar token/.test(text)) return false;
                              if (/nao sou um robo|i'm not a robot|recaptcha|captcha|verificacao de seguranca/.test(text)) return true;
                              const selectors = [
                                'iframe[src*="recaptcha"]',
                                'iframe[title*="reCAPTCHA"]',
                                'iframe[src*="captcha"]',
                                '.g-recaptcha',
                                '[data-sitekey]'
                              ];
                              return selectors.some(selector =>
                                [...document.querySelectorAll(selector)].some(e => !e.closest('#pdfreader-cielo-manual-banner'))
                              );
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                except Exception:
                    return False

            async def cielo_submit_enabled(session_id: str) -> bool:
                try:
                    return bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                              const visible = e => !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                              const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                              const disabled = e => !!(
                                e.disabled
                                || e.getAttribute('aria-disabled') === 'true'
                                || /\bdisabled\b|desabilitado|bloqueado/.test(norm(e.className || ''))
                              );
                              const actionable = e => visible(e) && !disabled(e) && !e.closest('#pdfreader-cielo-manual-banner');
                              const primary = document.querySelector('#bt-submit');
                              const button = actionable(primary) ? primary : [...document.querySelectorAll('button,input[type=submit],input[type=button],a,[role=button],[tabindex],.button,.btn,[class*="button"],[class*="btn"]')]
                                .find(e => actionable(e) && /entrar|acessar|continuar|enviar|validar|verificar|confirmar|prosseguir|avancar/.test(norm(e.innerText || e.value || e.getAttribute('aria-label') || '')));
                              return !!button;
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                except Exception:
                    return False

            async def cielo_token_input_present(session_id: str) -> bool:
                try:
                    return bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                              const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                              const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                              const bodyText = norm(document.body && document.body.innerText || '');
                              const inputs = [...document.querySelectorAll('input')]
                                .filter(visible)
                                .filter(e => !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()));
                              if (inputs.length >= 4 && inputs.every(e => {
                                const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                                const width = Math.round(e.getBoundingClientRect().width || 0);
                                return maxLength === 1 || width <= 90;
                              })) return true;
                              if (inputs.length && /codigo|token|otp|mfa|verificacao|validacao|autenticacao|verificar/.test(bodyText)) return true;
                              const hasVerifyButton = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                                .filter(visible)
                                .some(e => /verificar|validar codigo|validar token|confirmar codigo|confirmar token/.test(norm(e.innerText || e.value || e.getAttribute('aria-label') || '')));
                              if (inputs.length && hasVerifyButton) return true;
                              return inputs.some(e => {
                                  const text = norm([
                                    e.type,
                                    e.name,
                                    e.id,
                                    e.placeholder,
                                    e.getAttribute('aria-label'),
                                    e.getAttribute('autocomplete'),
                                    e.getAttribute('inputmode')
                                  ].join(' '));
                                  const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                                  return /codigo|token|otp|mfa|verificacao|validacao|autenticacao|one-time-code|numeric/.test(text)
                                    || (maxLength >= 4 && maxLength <= 8 && /text|tel|number|password/.test((e.type || '').toLowerCase()));
                                });
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                except Exception:
                    return False

            async def cielo_token_challenge_present(session_id: str, text_norm: str | None = None) -> bool:
                text_norm = text_norm if text_norm is not None else _normalize_ascii_text(await visible_text(session_id))
                if await cielo_token_input_present(session_id):
                    return True
                return any(
                    marker in text_norm
                    for marker in (
                        "digite o codigo",
                        "digite o token",
                        "informe o codigo",
                        "informe o token",
                        "codigo enviado",
                        "codigo de verificacao",
                        "insira o codigo",
                        "validar codigo",
                        "validar token",
                        "verificar codigo",
                        "verificar token",
                        "verificar",
                    )
                )

            def cielo_public_site_url(current_url: str) -> bool:
                url = str(current_url or "").lower()
                return "://www.cielo.com.br" in url or "://cielo.com.br" in url

            def cielo_authenticated_portal_url(current_url: str) -> bool:
                url = str(current_url or "").lower()
                return "minhaconta2.cielo.com.br" in url and "acessos/login" not in url

            async def wait_for_manual_cielo_challenge(session_id: str, context_label: str, timeout: float = 600.0) -> None:
                challenge_visible = await cielo_manual_challenge_present(session_id)
                if not challenge_visible:
                    return
                _emit_pix_status(
                    on_status,
                    f"Resolva manualmente a verificacao 'nao sou um robo' da Cielo na janela aberta ({context_label}).",
                )
                await show_cielo_banner(
                    session_id,
                    "Ação manual necessária\nResolva o reCAPTCHA / 'não sou um robô' nesta janela.\nDepois que o botão Entrar liberar, o app continuará automaticamente.",
                    "#92400e",
                )
                deadline = time.time() + timeout
                while time.time() < deadline:
                    _check_cancelled()
                    current_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    text_norm = _normalize_ascii_text(await visible_text(session_id))
                    if await cielo_token_challenge_present(session_id, text_norm):
                        await hide_cielo_banner(session_id)
                        return
                    if any(
                        marker in text_norm
                        for marker in (
                            "e-mail para",
                            "email para",
                            "gmail.com",
                            "receber por e-mail",
                            "receber por email",
                            "enviar por e-mail",
                            "enviar por email",
                        )
                    ):
                        await hide_cielo_banner(session_id)
                        return
                    if not await cielo_manual_challenge_present(session_id):
                        await hide_cielo_banner(session_id)
                        return
                    if "acessos/login" not in current_url:
                        if cielo_public_site_url(current_url):
                            cielo_log("auth_manual_challenge_public_site_redirect", current_url=current_url, context=context_label)
                            await hide_cielo_banner(session_id)
                            raise RuntimeError(
                                "A Cielo redirecionou para o site publico apos o reCAPTCHA, sem abrir a area autenticada."
                            )
                        await hide_cielo_banner(session_id)
                        return
                    await asyncio.sleep(2.0)
                raise RuntimeError("A verificacao manual da Cielo nao foi concluida dentro do tempo limite.")

            async def fill_visible_input(session_id: str, index: int, value: str) -> bool:
                script = """
                ((idx, value) => {
                  const inputs = [...document.querySelectorAll('input')]
                    .filter(e => e.type !== 'hidden' && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const input = inputs[idx];
                  if (!input) return false;
                  input.scrollIntoView({block: 'center'});
                  input.focus();
                  const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                  setter.call(input, '');
                  input.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                  setter.call(input, value);
                  input.dispatchEvent(new InputEvent('input', {bubbles: true, composed: true, inputType: 'insertText', data: value}));
                  input.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                  input.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true}));
                  input.blur();
                  return true;
                })
                """
                return bool(await eval_js(session_id, f"{script}({index}, {json.dumps(value)})", timeout=10.0))

            async def focus_cielo_login_input(session_id: str) -> bool:
                return bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                          const visible = e => !!(e && !e.disabled && !e.readOnly && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const inputs = [...document.querySelectorAll('input')]
                            .filter(e => visible(e) && !/hidden|password|checkbox|radio|submit|button/.test((e.type || '').toLowerCase()));
                          const target = inputs.find(e => /login|email|usuario|user|cpf|cnpj|estabelecimento|document/.test([
                            e.type,
                            e.name,
                            e.id,
                            e.placeholder,
                            e.getAttribute('aria-label'),
                            e.parentElement && e.parentElement.innerText
                          ].join(' ').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').toLowerCase())) || inputs[0];
                          if (!target) return false;
                          target.scrollIntoView({block: 'center'});
                          target.focus();
                          const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                          setter.call(target, '');
                          target.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                          target.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                          return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                )

            async def fill_cielo_login_input(session_id: str, value: str) -> bool:
                if not await focus_cielo_login_input(session_id):
                    return False
                try:
                    await cdp("Input.insertText", {"text": str(value or "")}, session_id=session_id, timeout=10.0)
                except Exception:
                    return await fill_visible_input(session_id, 0, value)
                await asyncio.sleep(0.5)
                return bool(
                    await eval_js(
                        session_id,
                        f"""
                        (() => {{
                          const expectedValue = {json.dumps(str(value or ""))};
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          return [...document.querySelectorAll('input')]
                            .filter(e => visible(e) && !/hidden|password|checkbox|radio|submit|button/.test((e.type || '').toLowerCase()))
                            .some(e => String(e.value || '') === expectedValue);
                        }})()
                        """,
                        timeout=10.0,
                    )
                )

            async def cielo_login_input_state(session_id: str, expected: str) -> dict:
                try:
                    state = await eval_js(
                        session_id,
                        f"""
                        (() => {{
                          const expectedValue = {json.dumps(str(expected or ""))};
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const inputs = [...document.querySelectorAll('input')]
                            .filter(e => visible(e) && !/hidden|password|checkbox|radio|submit|button/.test((e.type || '').toLowerCase()));
                          const values = inputs.map(e => String(e.value || ''));
                          return {{
                            present: inputs.length > 0,
                            anyValue: values.some(Boolean),
                            matches: values.some(v => v === expectedValue),
                            firstValueLength: values.length ? values[0].length : 0
                          }};
                        }})()
                        """,
                        timeout=10.0,
                    )
                    return state if isinstance(state, dict) else {}
                except Exception:
                    return {}

            async def fill_cielo_token(session_id: str, token: str) -> bool:
                digits = re.sub(r"\D+", "", str(token or ""))
                if not digits:
                    return False
                focus_script = """
                ((value) => {
                  const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                  const inputs = [...document.querySelectorAll('input')]
                    .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()));
                  const candidates = inputs.filter(e => {
                    const text = norm([
                      e.type,
                      e.name,
                      e.id,
                      e.placeholder,
                      e.getAttribute('aria-label'),
                      e.getAttribute('autocomplete'),
                      e.getAttribute('inputmode')
                    ].join(' '));
                    const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                    return /codigo|token|otp|mfa|verificacao|validacao|autenticacao|one-time-code|numeric|number|tel/.test(text)
                      || (maxLength >= 1 && maxLength <= 8);
                  });
                  const singleDigitInputs = candidates.filter(e => {
                    const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                    const width = Math.round(e.getBoundingClientRect().width || 0);
                    return maxLength === 1 || width <= 80;
                  });
                  if (singleDigitInputs.length >= value.length) {
                    singleDigitInputs.forEach(e => { e.value = ''; e.dispatchEvent(new Event('input', {bubbles: true, composed: true})); });
                    singleDigitInputs[0].scrollIntoView({block: 'center'});
                    singleDigitInputs[0].focus();
                    return {mode: 'split'};
                  }
                  const target = candidates.find(e => /one-time-code|otp|token|codigo|numeric|number|tel/.test(norm([
                    e.name,
                    e.id,
                    e.placeholder,
                    e.getAttribute('aria-label'),
                    e.getAttribute('autocomplete'),
                    e.getAttribute('inputmode')
                  ].join(' ')))) || candidates[candidates.length - 1] || inputs[inputs.length - 1];
                  if (!target) return {mode: 'none'};
                  target.value = '';
                  target.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                  target.scrollIntoView({block: 'center'});
                  target.focus();
                  return {mode: 'single'};
                })
                """
                prepared = await eval_js(session_id, f"{focus_script}({json.dumps(digits)})", timeout=10.0)
                if isinstance(prepared, dict) and prepared.get("mode") in {"split", "single"}:
                    try:
                        await cdp("Input.insertText", {"text": digits}, session_id=session_id, timeout=10.0)
                        await asyncio.sleep(0.6)
                        typed_ok = bool(
                            await eval_js(
                                session_id,
                                f"""
                                (() => {{
                                  const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                                  const value = {json.dumps(digits)};
                                  const values = [...document.querySelectorAll('input')]
                                    .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()))
                                    .map(e => String(e.value || '').replace(/\\D+/g, ''))
                                    .filter(Boolean);
                                  return values.join('').includes(value) || values.some(v => v === value);
                                }})()
                                """,
                                timeout=10.0,
                            )
                        )
                        if typed_ok:
                            return True
                    except Exception:
                        pass
                fallback_script = """
                ((value) => {
                  const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                  const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                  const setValue = (input, val) => {
                    input.scrollIntoView({block: 'center'});
                    input.focus();
                    setter.call(input, '');
                    input.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                    setter.call(input, val);
                    input.dispatchEvent(new InputEvent('input', {bubbles: true, composed: true, inputType: 'insertText', data: val}));
                    input.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                    input.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true}));
                  };
                  const inputs = [...document.querySelectorAll('input')]
                    .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()));
                  const candidates = inputs.filter(e => {
                    const text = norm([
                      e.type,
                      e.name,
                      e.id,
                      e.placeholder,
                      e.getAttribute('aria-label'),
                      e.getAttribute('autocomplete'),
                      e.getAttribute('inputmode')
                    ].join(' '));
                    const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                    return /codigo|token|otp|mfa|verificacao|validacao|autenticacao|one-time-code|numeric|number|tel/.test(text)
                      || (maxLength >= 1 && maxLength <= 8);
                  });
                  const singleDigitInputs = candidates.filter(e => {
                    const maxLength = Number(e.getAttribute('maxlength') || e.maxLength || 0);
                    const width = Math.round(e.getBoundingClientRect().width || 0);
                    return maxLength === 1 || width <= 80;
                  });
                  if (singleDigitInputs.length >= value.length) {
                    value.split('').forEach((digit, idx) => setValue(singleDigitInputs[idx], digit));
                    singleDigitInputs[Math.min(value.length, singleDigitInputs.length) - 1].blur();
                    return true;
                  }
                  const target = candidates.find(e => /one-time-code|otp|token|codigo|numeric|number|tel/.test(norm([
                    e.name,
                    e.id,
                    e.placeholder,
                    e.getAttribute('aria-label'),
                    e.getAttribute('autocomplete'),
                    e.getAttribute('inputmode')
                  ].join(' ')))) || candidates[candidates.length - 1] || inputs[inputs.length - 1];
                  if (!target) return false;
                  setValue(target, value);
                  target.blur();
                  return true;
                })
                """
                return bool(await eval_js(session_id, f"{fallback_script}({json.dumps(digits)})", timeout=10.0))

            async def fill_password_input(session_id: str, value: str) -> bool:
                focused_password = bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                          const visible = e => !!(e && !e.disabled && !e.readOnly && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const inputs = [...document.querySelectorAll('input')]
                            .filter(e => e.type === 'password' && visible(e));
                          const input = inputs[0];
                          if (!input) return false;
                          input.scrollIntoView({block: 'center'});
                          input.focus();
                          const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                          setter.call(input, '');
                          input.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                          input.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                          return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                )
                if focused_password:
                    try:
                        await cdp("Input.insertText", {"text": str(value or "")}, session_id=session_id, timeout=10.0)
                        await asyncio.sleep(0.5)
                        typed_ok = bool(
                            await eval_js(
                                session_id,
                                f"""
                                (() => {{
                                  const expectedLength = {len(str(value or ""))};
                                  const expectedValue = {json.dumps(str(value or ""))};
                                  const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                                  return [...document.querySelectorAll('input')]
                                    .filter(e => e.type === 'password' && visible(e))
                                    .some(e => String(e.value || '') === expectedValue && String(e.value || '').length === expectedLength);
                                }})()
                                """,
                                timeout=10.0,
                            )
                        )
                        if typed_ok:
                            return True
                    except Exception:
                        pass
                script = """
                ((value) => {
                  const inputs = [...document.querySelectorAll('input')]
                    .filter(e => e.type !== 'hidden' && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const input = inputs.find(e => e.type === 'password') || inputs[inputs.length - 1];
                  if (!input) return false;
                  input.scrollIntoView({block: 'center'});
                  input.focus();
                  const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                  setter.call(input, '');
                  input.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                  setter.call(input, value);
                  input.dispatchEvent(new InputEvent('input', {bubbles: true, composed: true, inputType: 'insertText', data: value}));
                  input.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                  input.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true}));
                  input.blur();
                  return true;
                })
                """
                return bool(await eval_js(session_id, f"{script}({json.dumps(value)})", timeout=10.0))

            cielo_resend_reject_markers = (
                "reenviar",
                "reenvie",
                "novo codigo",
                "novo código",
                "novo token",
                "pedir novo",
                "solicitar novo",
                "gerar novo",
                "outro codigo",
                "outro código",
                "outro token",
                "enviar novamente",
                "receber novamente",
                "envie novamente",
            )

            async def click_by_text(
                session_id: str,
                markers: tuple[str, ...],
                timeout: float = 12.0,
                reject_markers: tuple[str, ...] = (),
            ) -> bool:
                deadline = time.time() + timeout
                markers_json = json.dumps([_normalize_ascii_text(marker) for marker in markers])
                reject_markers_json = json.dumps([_normalize_ascii_text(marker) for marker in reject_markers])
                while time.time() < deadline:
                    script = """
                        (() => {
                          const markers = __MARKERS__;
                          const rejectMarkers = __REJECT_MARKERS__;
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                          const rejected = text => rejectMarkers.some(marker => marker && text.includes(marker));
                          const rawCandidates = [...document.querySelectorAll('button,a,label,span,div,input[type=button],input[type=submit],[role=button],[role=option],[role=menuitem],[role=radio]')]
                            .filter(visible)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                            .filter(([e, text]) => text && markers.some(marker => text.includes(marker)) && !rejected(text));
                          const seen = new Set();
                          const candidates = rawCandidates
                            .map(([e, text]) => {
                              const clickable = e.closest('button,a,label,[role=button],[role=option],[role=menuitem],[role=radio],input[type=button],input[type=submit]') || e;
                              const clickableText = norm(clickable.innerText || clickable.value || clickable.getAttribute('aria-label') || text);
                              return [clickable, clickableText || text];
                            })
                            .filter(([e, text]) => {
                              if (!visible(e) || rejected(text)) return false;
                              const rect = e.getBoundingClientRect();
                              const key = [e.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                              if (seen.has(key)) return false;
                              seen.add(key);
                              return true;
                            })
                            .map(([e, text]) => {
                              const rect = e.getBoundingClientRect();
                              const area = Math.max(1, rect.width * rect.height);
                              const exact = markers.some(marker => text === marker) ? 5000 : 0;
                              const starts = markers.some(marker => text.startsWith(marker)) ? 1000 : 0;
                              const tagBonus = /^(BUTTON|A|LABEL|INPUT)$/.test(e.tagName) || e.getAttribute('role') ? 500 : 0;
                              const shortBonus = Math.max(0, 400 - text.length);
                              const areaPenalty = Math.min(1000, Math.log10(area) * 120);
                              return {e, text, score: exact + starts + tagBonus + shortBonus - areaPenalty};
                            })
                            .sort((a, b) => b.score - a.score);
                          if (!candidates.length) return false;
                          const chosen = candidates[0].e;
                          chosen.scrollIntoView({block: 'center'});
                          chosen.focus && chosen.focus();
                          chosen.click();
                          return true;
                        })()
                    """.replace("__MARKERS__", markers_json).replace("__REJECT_MARKERS__", reject_markers_json)
                    clicked = await eval_js(
                        session_id,
                        script,
                        timeout=10.0,
                    )
                    if clicked:
                        return True
                    await asyncio.sleep(0.5)
                return False

            async def click_submit(session_id: str, reject_markers: tuple[str, ...] = ()) -> bool:
                reject_markers_json = json.dumps([_normalize_ascii_text(marker) for marker in reject_markers])
                script = """
                (() => {
                  const rejectMarkers = __REJECT_MARKERS__;
                  const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                  const visible = e => !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const disabled = e => !!(
                    e.disabled
                    || e.getAttribute('aria-disabled') === 'true'
                    || /\bdisabled\b|desabilitado|bloqueado/.test(norm(e.className || ''))
                  );
                  const rejected = e => rejectMarkers.some(marker => marker && norm(e.innerText || e.value || e.getAttribute('aria-label') || '').includes(marker));
                  const actionable = e => visible(e) && !disabled(e) && !rejected(e) && !e.closest('#pdfreader-cielo-manual-banner');
                  const primary = document.querySelector('#bt-submit');
                  const candidates = [
                    primary,
                    ...document.querySelectorAll('button,input[type=submit],input[type=button],a,[role=button],[tabindex],.button,.btn,[class*="button"],[class*="btn"]')
                  ].filter(Boolean);
                  const button = candidates.find(e => actionable(e) && /entrar|acessar|continuar|enviar|validar|verificar|confirmar|consultar|pesquisar|buscar|exportar|baixar|prosseguir|avancar/.test(norm(e.innerText || e.value || e.getAttribute('aria-label') || '')));
                  if (!button) return false;
                  button.scrollIntoView({block: 'center'});
                  button.focus();
                  button.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                  button.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                  button.click();
                  return true;
                })()
                """.replace("__REJECT_MARKERS__", reject_markers_json)
                return bool(
                    await eval_js(
                        session_id,
                        script,
                        timeout=10.0,
                    )
                )

            async def force_cielo_login_submit(session_id: str) -> dict:
                result = await eval_js(
                    session_id,
                    """
                    (() => {
                      const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                      const visible = e => {
                        if (!e || e.closest('#pdfreader-cielo-manual-banner')) return false;
                        const rect = e.getBoundingClientRect();
                        const style = getComputedStyle(e);
                        return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                      };
                      const textOf = e => norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                      const clickableSelector = 'button,input[type=submit],input[type=button],a,[role=button],[tabindex],.button,.btn,[class*="button"],[class*="btn"]';
                      const primary = document.querySelector('#bt-submit');
                      const nodes = [
                        primary,
                        ...document.querySelectorAll(clickableSelector),
                        ...[...document.querySelectorAll('span,div,p')].map(e => e.closest(clickableSelector) || e)
                      ].filter(Boolean).filter(visible);
                      const seen = new Set();
                      const candidates = nodes
                        .map(e => {
                          const text = textOf(e);
                          const rect = e.getBoundingClientRect();
                          return {e, text, rect};
                        })
                        .filter(item => {
                          const key = [item.e.tagName, item.text, Math.round(item.rect.left), Math.round(item.rect.top)].join(':');
                          if (seen.has(key)) return false;
                          seen.add(key);
                          if (item.e === primary) return true;
                          return /entrar|acessar|continuar|prosseguir|avancar|enviar/.test(item.text);
                        })
                        .sort((a, b) => {
                          const ap = a.e === primary ? 10000 : 0;
                          const bp = b.e === primary ? 10000 : 0;
                          const at = /^entrar$/.test(a.text) ? 5000 : /entrar/.test(a.text) ? 3000 : 0;
                          const bt = /^entrar$/.test(b.text) ? 5000 : /entrar/.test(b.text) ? 3000 : 0;
                          return (bp + bt) - (ap + at);
                        });
                      const chosen = candidates[0];
                      if (!chosen) return {clicked: false, reason: 'not_found'};
                      const e = chosen.e;
                      e.scrollIntoView({block: 'center', inline: 'center'});
                      e.focus && e.focus();
                      e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                      e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                      e.click();
                      try {
                        const form = e.closest('form') || document.querySelector('form');
                        if (form && typeof form.requestSubmit === 'function') form.requestSubmit(e.matches('button,input') ? e : undefined);
                      } catch (_) {}
                      const rect = e.getBoundingClientRect();
                      return {
                        clicked: true,
                        targetText: chosen.text,
                        tag: e.tagName,
                        id: e.id || '',
                        disabled: !!e.disabled,
                        ariaDisabled: e.getAttribute('aria-disabled') || '',
                        x: Math.round(rect.left + rect.width / 2),
                        y: Math.round(rect.top + rect.height / 2),
                      };
                    })()
                    """,
                    timeout=10.0,
                )
                result = result if isinstance(result, dict) else {"clicked": bool(result)}
                if result.get("clicked"):
                    try:
                        x = int(result.get("x") or 0)
                        y = int(result.get("y") or 0)
                        if x > 0 and y > 0:
                            await cdp(
                                "Input.dispatchMouseEvent",
                                {"type": "mousePressed", "x": x, "y": y, "button": "left", "clickCount": 1},
                                session_id=session_id,
                                timeout=5.0,
                            )
                            await cdp(
                                "Input.dispatchMouseEvent",
                                {"type": "mouseReleased", "x": x, "y": y, "button": "left", "clickCount": 1},
                                session_id=session_id,
                                timeout=5.0,
                            )
                    except Exception:
                        pass
                return result

            async def click_cielo_filter_apply(session_id: str) -> dict:
                script = """
                (() => {
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const wanted = ['aplicar', 'filtrar', 'consultar', 'pesquisar', 'buscar'];
                  const rejected = text => [
                    'filtrar mais',
                    'mais filtros',
                    'data da venda',
                    'data de venda',
                    'historico',
                    'hoje',
                    'exportar',
                    'reenviar',
                    'novo codigo',
                    'novo token',
                  ].some(marker => text.includes(marker));
                  const seen = new Set();
                  const candidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const clickable = e.closest('button,a,[role=button],input[type=button],input[type=submit],label') || e;
                      const text = norm(clickable.innerText || clickable.value || clickable.getAttribute('aria-label') || e.innerText || e.textContent || '');
                      return [clickable, text];
                    })
                    .filter(([e, text]) => {
                      if (!text || rejected(text)) return false;
                      if (!wanted.some(marker => text === marker || text.startsWith(marker + ' '))) return false;
                      const rect = e.getBoundingClientRect();
                      const key = [e.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(([e, text]) => {
                      const rect = e.getBoundingClientRect();
                      const exact = wanted.some(marker => text === marker) ? 5000 : 0;
                      const tagBonus = /^(BUTTON|A|LABEL|INPUT)$/.test(e.tagName) || e.getAttribute('role') ? 700 : 0;
                      const shortBonus = Math.max(0, 200 - text.length);
                      const areaPenalty = Math.min(800, Math.log10(Math.max(1, rect.width * rect.height)) * 90);
                      return {
                        e,
                        text,
                        score: exact + tagBonus + shortBonus - areaPenalty,
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 8).map(({text, tag, role, x, y, w, h, score}) => ({text, tag, role, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  chosen.e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.click();
                  return {clicked: true, targetText: chosen.text, tag: chosen.tag, role: chosen.role, candidates: summary};
                })()
                """
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_sales_detail_after_filter(session_id: str) -> dict:
                script = """
                (() => {
                  const dataBr = __DATA_BR__;
                  const dataIso = __DATA_ISO__;
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    const vw = window.innerWidth || document.documentElement.clientWidth || 0;
                    const vh = window.innerHeight || document.documentElement.clientHeight || 0;
                    return rect.width > 0 && rect.height > 0
                      && rect.right > 0 && rect.bottom > 0 && rect.left < vw && rect.top < vh
                      && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const clickSelector = 'button,a,[role=button],label,input[type=button],input[type=submit]';
                  const ancestorText = e => {
                    let current = e;
                    let best = norm(e.innerText || e.textContent || '');
                    for (let depth = 0; current && depth < 8; depth++, current = current.parentElement) {
                      const text = norm(current.innerText || current.textContent || '');
                      if (!text || text.length > 900) continue;
                      if (text.includes(dataBr) || text.includes(dataIso)) return text;
                      if (text.length > best.length) best = text;
                    }
                    return best;
                  };
                  const candidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const target = e.closest(clickSelector) || e;
                      const text = norm(target.innerText || target.value || target.getAttribute('aria-label') || target.getAttribute('title') || e.innerText || e.textContent || '');
                      const rowText = ancestorText(target);
                      return {e: target, text, rowText};
                    })
                    .filter(item => {
                      if (!visible(item.e)) return false;
                      if (!item.text || item.text.length > 80) return false;
                      if (!/detalhar/.test(item.text)) return false;
                      if (/detalhado|resumo detalhado|calendario|relatorios|exportar|filtrar|filtro/.test(item.text)) return false;
                      return true;
                    })
                    .map(item => {
                      const rect = item.e.getBoundingClientRect();
                      const dataMatch = item.rowText.includes(dataBr) || item.rowText.includes(dataIso);
                      const exact = /^(detalhar|detalhar este dia|detalhar dia)$/.test(item.text);
                      const tagBonus = /^(BUTTON|A|LABEL|INPUT)$/.test(item.e.tagName) || item.e.getAttribute('role') ? 1200 : 0;
                      return {
                        ...item,
                        score: (dataMatch ? 5000 : 0) + (exact ? 2500 : 800) + tagBonus + Math.max(0, 1000 - rect.top),
                        tag: item.e.tagName,
                        role: item.e.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 8).map(({text, rowText, tag, role, x, y, w, h, score}) => ({text, rowText: rowText.slice(0, 260), tag, role, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary, href: location.href};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  const clickRect = chosen.e.getBoundingClientRect();
                  return {
                    clicked: true,
                    targetText: chosen.text,
                    rowText: chosen.rowText.slice(0, 260),
                    tag: chosen.tag,
                    role: chosen.role,
                    href: location.href,
                    clickX: Math.round(clickRect.left + clickRect.width / 2),
                    clickY: Math.round(clickRect.top + clickRect.height / 2),
                    candidates: summary
                  };
                })()
                """.replace("__DATA_BR__", json.dumps(data_br)).replace("__DATA_ISO__", json.dumps(data_iso))
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_export_format(session_id: str) -> dict:
                script = """
                (() => {
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const overlaySelector = '[role=dialog], [class*="modal"], [class*="Modal"], [class*="overlay"], [class*="Overlay"], [class*="popover"], [class*="Popover"]';
                  const seen = new Set();
                  const candidates = [...document.querySelectorAll('label,button,a,[role=button],[role=radio],[role=option],input,span,div')]
                    .filter(visible)
                    .map(e => {
                      const clickable = e.closest('label,button,a,[role=button],[role=radio],[role=option]') || e;
                      const text = norm(clickable.innerText || clickable.value || clickable.getAttribute('aria-label') || e.innerText || e.textContent || '');
                      const input = clickable.querySelector && clickable.querySelector('input[type=radio],input[type=checkbox]');
                      return [clickable, text, input];
                    })
                    .filter(([e, text]) => {
                      if (!text) return false;
                      if (!/excel|xlsx|csv/.test(text)) return false;
                      if (/exportar relatorios|selecione o formato|fechar|avancar|filtrar/.test(text) && text.length > 40) return false;
                      const rect = e.getBoundingClientRect();
                      const key = [e.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(([e, text, input]) => {
                      const rect = e.getBoundingClientRect();
                      const inOverlay = !!e.closest(overlaySelector);
                      const csv = text === 'csv';
                      const xlsx = /excel|xlsx/.test(text);
                      const exact = /^(excel|excel\\(\\.xlsx\\)|xlsx|csv)$/.test(text);
                      const checked = !!(input && input.checked);
                      const tagBonus = /^(LABEL|BUTTON|A|INPUT)$/.test(e.tagName) || e.getAttribute('role') ? 900 : 0;
                      const cardBonus = e.tagName === 'DIV' && rect.width > 80 && rect.height > 60 ? 1200 : 0;
                      const shortBonus = Math.max(0, 240 - text.length);
                      const areaPenalty = Math.min(800, Math.log10(Math.max(1, rect.width * rect.height)) * 80);
                      return {
                        e,
                        input,
                        text,
                        score: (inOverlay ? 2500 : 0) + (csv ? 2400 : xlsx ? 1200 : 700) + (exact ? 1500 : 0) + (checked ? 300 : 0) + tagBonus + cardBonus + shortBonus - areaPenalty,
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        inOverlay,
                        checked,
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 10).map(({text, tag, role, inOverlay, checked, x, y, w, h, score}) => ({text, tag, role, inOverlay, checked, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  const target = chosen.input || chosen.e;
                  target.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                  target.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                  target.click();
                  target.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                  return {clicked: true, targetText: chosen.text, tag: chosen.tag, role: chosen.role, inOverlay: chosen.inOverlay, checked: chosen.checked, candidates: summary};
                })()
                """
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_export_confirm(session_id: str, require_overlay: bool = False) -> dict:
                require_overlay_js = "true" if require_overlay else "false"
                script = """
                (() => {
                  const requireOverlay = __REQUIRE_OVERLAY__;
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const overlaySelector = '[role=dialog], [class*="modal"], [class*="Modal"], [class*="overlay"], [class*="Overlay"], [class*="popover"], [class*="Popover"]';
                  const textOf = e => norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                  const nodes = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')].filter(visible);
                  const seen = new Set();
                  const candidates = nodes
                    .map(e => [e, textOf(e)])
                    .filter(([e, text]) => {
                      const inOverlay = !!e.closest(overlaySelector);
                      if (requireOverlay && !inOverlay) return false;
                      if (!text || text.length > 45) return false;
                      if (!/^(avancar|avançar|exportar|baixar|download|gerar arquivo|confirmar|concluir|solicitar)$/.test(text)) return false;
                      if (/filtrar|data da venda|historico|hoje|inicio|recebiveis|pix|sair|notificacoes/.test(text)) return false;
                      const rect = e.getBoundingClientRect();
                      const key = [e.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(([e, text]) => {
                      const rect = e.getBoundingClientRect();
                      const inOverlay = !!e.closest(overlaySelector);
                      const priority =
                        /^(avancar|avançar)$/.test(text) ? 7000 :
                        /^exportar$/.test(text) ? 5000 :
                        /^(baixar|download|gerar arquivo)$/.test(text) ? 4500 :
                        3500;
                      return {
                        e,
                        text,
                        score: priority + (inOverlay ? 2500 : 0) - Math.min(600, Math.log10(Math.max(1, rect.width * rect.height)) * 70),
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        inOverlay,
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 10).map(({text, tag, role, inOverlay, x, y, w, h, score}) => ({text, tag, role, inOverlay, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  chosen.e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.click();
                  return {clicked: true, targetText: chosen.text, tag: chosen.tag, role: chosen.role, inOverlay: chosen.inOverlay, candidates: summary};
                })()
                """.replace("__REQUIRE_OVERLAY__", require_overlay_js)
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_reports_cta(session_id: str) -> dict:
                script = """
                (() => {
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    const vw = window.innerWidth || document.documentElement.clientWidth || 0;
                    const vh = window.innerHeight || document.documentElement.clientHeight || 0;
                    return rect.width > 0 && rect.height > 0
                      && rect.right > 0 && rect.bottom > 0 && rect.left < vw && rect.top < vh
                      && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const overlaySelector = '[role=dialog], [class*="modal"], [class*="Modal"], [class*="overlay"], [class*="Overlay"], [class*="popover"], [class*="Popover"], [class*="toast"], [class*="Toast"], [class*="snackbar"], [class*="Snackbar"]';
                  const clickableSelector = 'button,a,[role=button],input[type=button],input[type=submit],label';
                  const clickAtCenter = e => {
                    const rect = e.getBoundingClientRect();
                    const x = Math.max(1, Math.min((window.innerWidth || document.documentElement.clientWidth || 1) - 1, rect.left + rect.width / 2));
                    const y = Math.max(1, Math.min((window.innerHeight || document.documentElement.clientHeight || 1) - 1, rect.top + rect.height / 2));
                    const pointed = document.elementFromPoint(x, y);
                    return (pointed && pointed.closest(clickableSelector)) || pointed || e;
                  };
                  const nodes = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const text = norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                      const clickTarget = e.closest(clickableSelector) || e.closest('[class*="button"],[class*="Button"],[class*="btn"],[class*="Btn"]') || clickAtCenter(e);
                      return [e, clickTarget, text];
                    })
                    .filter(([e, clickTarget, text]) => {
                      if (!text || text.length > 45) return false;
                      if (!/relatorio|relatorios/.test(text)) return false;
                      if (/exportar relatorios|selecione o formato|planilha|csv|excel|xlsx/.test(text)) return false;
                      return /^(acessar relatorios|ver relatorios|ir para relatorios|acompanhar relatorios|consultar relatorios)$/.test(text);
                    })
                    .filter(([e, clickTarget]) => visible(clickTarget))
                    .map(([e, clickTarget, text]) => {
                      const rect = e.getBoundingClientRect();
                      const inOverlay = !!e.closest(overlaySelector);
                      const targetRect = clickTarget.getBoundingClientRect();
                      const tagBonus = /^(BUTTON|A|LABEL|INPUT)$/.test(clickTarget.tagName) || clickTarget.getAttribute('role') ? 1200 : 0;
                      const exactish = text === 'acessar relatorios' ? 3500 : 2500;
                      return {
                        e,
                        clickTarget,
                        text,
                        score: (inOverlay ? 2000 : 0) + tagBonus + exactish + Math.max(0, 180 - text.length),
                        tag: clickTarget.tagName,
                        role: clickTarget.getAttribute('role') || '',
                        nodeTag: e.tagName,
                        inOverlay,
                        x: Math.round(targetRect.x),
                        y: Math.round(targetRect.y),
                        w: Math.round(targetRect.width),
                        h: Math.round(targetRect.height),
                        textX: Math.round(rect.x),
                        textY: Math.round(rect.y),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = nodes[0];
                  const summary = nodes.slice(0, 10).map(({text, tag, role, nodeTag, inOverlay, x, y, w, h, textX, textY, score}) => ({text, tag, role, nodeTag, inOverlay, x, y, w, h, textX, textY, score}));
                  if (!chosen) return {clicked: false, candidates: summary};
                  const target = chosen.clickTarget;
                  target.scrollIntoView({block: 'center', inline: 'center'});
                  const clickRect = target.getBoundingClientRect();
                  const clickX = Math.round(clickRect.left + clickRect.width / 2);
                  const clickY = Math.round(clickRect.top + clickRect.height / 2);
                  target.focus && target.focus();
                  return {
                    clicked: true,
                    targetText: chosen.text,
                    tag: chosen.tag,
                    role: chosen.role,
                    inOverlay: chosen.inOverlay,
                    href: location.href,
                    clickX,
                    clickY,
                    candidates: summary
                  };
                })()
                """
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_ready_report_download(session_id: str) -> dict:
                script = """
                (() => {
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    const vw = window.innerWidth || document.documentElement.clientWidth || 0;
                    const docHeight = Math.max(
                      document.documentElement.scrollHeight || 0,
                      document.body?.scrollHeight || 0,
                      window.innerHeight || 0
                    );
                    return rect.width > 0 && rect.height > 0
                      && rect.left >= 0 && rect.top >= 0 && rect.right > 0 && rect.left < vw && rect.top < docHeight
                      && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const bodyText = norm(document.body?.innerText || '');
                  const href = norm(location.href || '');
                  const requestedDate = __DATA_BR__;
                  const parseDate = value => {
                    const match = String(value || '').match(/([0-9]{2})[/]([0-9]{2})[/]([0-9]{4})/);
                    if (!match) return null;
                    return Number(`${match[3]}${match[2]}${match[1]}`);
                  };
                  const requestedDateValue = parseDate(requestedDate);
                  const rowMatchesRequestedDate = rowText => {
                    const dates = [...rowText.matchAll(/\b[0-9]{2}[/][0-9]{2}[/][0-9]{4}\b/g)]
                      .map(match => parseDate(match[0]))
                      .filter(Boolean);
                    if (!requestedDateValue || dates.length < 2) return false;
                    for (let index = 0; index < dates.length - 1; index += 1) {
                      const start = dates[index];
                      const end = dates[index + 1];
                      if (start === requestedDateValue && end === requestedDateValue) return true;
                    }
                    return false;
                  };
                  const reportTextCount = rowText => (rowText.match(/vendas cielo/g) || []).length;
                  const rowLooksLikeExactReport = rowText => {
                    if (!rowText || rowText.length > 700) return false;
                    if (!rowMatchesRequestedDate(rowText)) return false;
                    if (!/vendas cielo|historico|hist.rico/.test(rowText)) return false;
                    return reportTextCount(rowText) <= 1;
                  };
                  const reportRowForIcon = icon => {
                    let current = icon;
                    for (let depth = 0; current && depth < 12; depth += 1, current = current.parentElement) {
                      const rowText = norm(current.innerText || current.textContent || '');
                      if (rowLooksLikeExactReport(rowText)) {
                        return {row: current, rowText};
                      }
                    }
                    return null;
                  };
                  const matchingReportRows = [...document.querySelectorAll('tr')]
                    .map(row => ({row, rowText: norm(row.innerText || row.textContent || '')}))
                    .filter(({row, rowText}) => visible(row) && rowLooksLikeExactReport(rowText))
                    .map(({row, rowText}) => {
                      const target = row.querySelector('td:last-child') || row.lastElementChild || row;
                      const rect = target.getBoundingClientRect();
                      const rowRect = row.getBoundingClientRect();
                      if (rect.width <= 0 || rect.height <= 0) return null;
                      return {
                        target,
                        rowText: rowText.slice(0, 260),
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                        rowY: Math.round(rowRect.y),
                        clickX: Math.round(rect.left + rect.width / 2),
                        clickY: Math.round(rect.top + rect.height / 2),
                        score: Math.max(0, 1600 - rowRect.top) + Math.max(0, rect.left),
                      };
                    })
                    .filter(Boolean)
                    .sort((a, b) => b.score - a.score);
                  const matchingReportRow = matchingReportRows[0];
                  if (matchingReportRow) {
                    matchingReportRow.target.scrollIntoView({block: 'center', inline: 'center'});
                    return {
                      clicked: true,
                      method: 'matching_report_row_last_cell',
                      targetText: 'download-cell',
                      rowText: matchingReportRow.rowText,
                      tag: matchingReportRow.target.tagName,
                      role: matchingReportRow.target.getAttribute('role') || '',
                      href: location.href,
                      clickX: matchingReportRow.clickX,
                      clickY: matchingReportRow.clickY,
                      candidates: matchingReportRows.slice(0, 8).map(({rowText, x, y, w, h, rowY, score, clickX, clickY}) => ({rowText, x, y, w, h, rowY, score, clickX, clickY}))
                    };
                  }
                  const directIconMatches = [...document.querySelectorAll('i[name="download"], [name="download"].icon-download, .icon-download, svg, path, use, [class*="download"], [class*="Download"], [aria-label*="download" i], [title*="download" i], [aria-label*="baixar" i], [title*="baixar" i]')]
                    .filter(icon => visible(icon) || visible(icon.closest('td') || icon.parentElement))
                    .map(icon => {
                      const rowInfo = reportRowForIcon(icon);
                      if (!rowInfo) return null;
                      const {row, rowText} = rowInfo;
                      const iconRect = icon.getBoundingClientRect();
                      const clickable = icon.closest('button,a,[role=button]')
                        || ((iconRect.width > 0 && iconRect.height > 0) ? icon : (icon.closest('td') || icon.parentElement));
                      const rect = clickable.getBoundingClientRect();
                      const rowRect = row.getBoundingClientRect();
                      const ready = !/processando|gerando|aguarde|pendente|em andamento|solicitado/.test(rowText);
                      const detailBonus = /historico detalhado|hist.rico detalhado|detalhado/.test(rowText) ? 5000 : 0;
                      const summaryPenalty = /historico resumo|hist.rico resumo/.test(rowText) ? 1200 : 0;
                      return {
                        e: clickable,
                        text: norm(clickable.innerText || clickable.getAttribute('aria-label') || clickable.getAttribute('title') || icon.getAttribute('name') || icon.className || 'download'),
                        rowText: rowText.slice(0, 260),
                        score: (ready ? 3000 : -1500) + detailBonus - summaryPenalty + Math.max(0, 1600 - rowRect.top) + Math.max(0, rect.left),
                        tag: clickable.tagName,
                        role: clickable.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                        rowY: Math.round(rowRect.y),
                        clickX: Math.round(rect.left + rect.width / 2),
                        clickY: Math.round(rect.top + rect.height / 2),
                        source: 'direct-icon'
                      };
                    })
                    .filter(Boolean)
                    .sort((a, b) => b.score - a.score);
                  const directIconChosen = directIconMatches[0];
                  if (directIconChosen) {
                    directIconChosen.e.scrollIntoView({block: 'center', inline: 'center'});
                    directIconChosen.e.focus && directIconChosen.e.focus();
                    return {
                      clicked: true,
                      method: 'direct_download_icon',
                      nativeClickRequired: true,
                      targetText: directIconChosen.text,
                      rowText: directIconChosen.rowText,
                      tag: directIconChosen.tag,
                      role: directIconChosen.role,
                      href: location.href,
                      clickX: directIconChosen.clickX,
                      clickY: directIconChosen.clickY,
                      candidates: directIconMatches.slice(0, 8).map(({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}) => ({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}))
                    };
                  }
                  const reportsAreaText = /meus relatorios|seus relatorios|relatorios solicitados|central de relatorios|historico de relatorios|relatorios gerados|arquivos gerados|baixar relatorio|download do relatorio|relatorio pronto|tipo de relatorio|data da solicitacao|relatorio inicio|vendas cielo historico resumo|vendas cielo historico detalhado/.test(bodyText);
                  const strongReportsArea = /tipo de relatorio|data da solicitacao|relatorio inicio|vendas cielo historico resumo|vendas cielo historico detalhado/.test(bodyText);
                  const onReportsArea = /\\/site\\/relatorio|\\/relatorios|\\/reports/.test(href) || reportsAreaText;
                  if (!onReportsArea || /seu relatorio ja esta em processamento/.test(bodyText)) {
                    return {clicked: false, wrongPage: true, processing: /processando|gerando|aguarde|pendente|em andamento|solicitado/.test(bodyText), candidates: [], bodyText: bodyText.slice(0, 500), href: location.href};
                  }
                  const seen = new Set();
                  let reportRows = [...document.querySelectorAll('tr,li,[role=row],section,article,div')]
                    .filter(visible)
                    .map(row => {
                      const rect = row.getBoundingClientRect();
                      const rowText = norm(row.innerText || row.textContent || '');
                      return {row, rect, rowText};
                    })
                    .filter(({rect, rowText}) => {
                      if (!rowText || rowText.length > 260) return false;
                      if (rect.top < 90 || rect.height < 28 || rect.height > 140 || rect.width < 220) return false;
                      if (!rowMatchesRequestedDate(rowText)) return false;
                      if (reportTextCount(rowText) > 1) return false;
                      return /vendas cielo|historico resumo|historico detalhado|histórico resumo|histórico detalhado|csv|xls|xlsx/.test(rowText);
                    })
                    .map(({row, rect, rowText}) => {
                      const controls = [...row.querySelectorAll('button,a,[role=button],svg,i,img,[name="download"],[class*="download"],[class*="Download"],[class*="icon-download"],[aria-label*="download" i],[title*="download" i],[aria-label*="baixar" i],[title*="baixar" i]')]
                        .map(e => e.closest('button,a,[role=button]') || e)
                        .filter((e, index, arr) => arr.indexOf(e) === index)
                        .filter(visible)
                        .filter(e => {
                          const text = norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                          return !/fechar|filtro|tipo de relatorio|gerenciar recorrencias|agendar recorrencia|atualizar/.test(text);
                        })
                        .sort((a, b) => b.getBoundingClientRect().left - a.getBoundingClientRect().left);
                      const target = controls[0];
                      if (!target) return null;
                      const targetRect = target.getBoundingClientRect();
                      const ready = !/processando|gerando|aguarde|pendente|em andamento|solicitado/.test(rowText);
                      const detailBonus = /historico detalhado|histórico detalhado|detalhado/.test(rowText) ? 5000 : 0;
                      const summaryPenalty = /historico resumo|histórico resumo/.test(rowText) ? 1200 : 0;
                      return {
                        e: target,
                        text: norm(target.innerText || target.value || target.getAttribute('aria-label') || target.getAttribute('title') || 'download'),
                        rowText: rowText.slice(0, 220),
                        score: (ready ? 3000 : -1500) + detailBonus - summaryPenalty + Math.max(0, 1600 - rect.top) + Math.max(0, targetRect.left),
                        tag: target.tagName,
                        role: target.getAttribute('role') || '',
                        x: Math.round(targetRect.x),
                        y: Math.round(targetRect.y),
                        w: Math.round(targetRect.width),
                        h: Math.round(targetRect.height),
                        rowY: Math.round(rect.y),
                      };
                    })
                    .filter(Boolean)
                    .sort((a, b) => b.score - a.score);
                  if (!reportRows.length) {
                    const fallbackSeen = new Set();
                    const fallbackRows = [...document.querySelectorAll('p,span,td,div')]
                      .filter(visible)
                      .map(e => {
                        const text = norm(e.innerText || e.textContent || '');
                        if (!text || text.length > 180) return null;
                        if (!/vendas cielo|historico|hist.rico|detalhado|resumo/.test(text)) return null;
                        const row = e.closest('tr,[role=row],li,section,article') || e.parentElement;
                        if (!row) return null;
                        const rect = row.getBoundingClientRect();
                        const rowText = norm(row.innerText || row.textContent || '');
                        if (!rowText || rowText.length > 700) return null;
                        if (rect.bottom <= 0 || rect.height < 10 || rect.height > 260 || rect.width < 120) return null;
                        if (rect.top >= (window.innerHeight || document.documentElement.clientHeight || 0)) return null;
                        if (!rowMatchesRequestedDate(rowText)) return null;
                        if (reportTextCount(rowText) > 1) return null;
                        if (!/vendas cielo|historico|hist.rico|detalhado|resumo|csv|xls|xlsx/.test(rowText)) return null;
                        const key = [Math.round(rect.left), Math.round(rect.top), Math.round(rect.width), rowText.slice(0, 120)].join(':');
                        if (fallbackSeen.has(key)) return null;
                        fallbackSeen.add(key);
                        const controls = [...row.querySelectorAll('button,a,[role=button],svg,i,img,[name="download"],[class*="download"],[class*="Download"],[class*="icon-download"],[aria-label*="download" i],[title*="download" i],[aria-label*="baixar" i],[title*="baixar" i]')]
                          .map(node => node.closest('button,a,[role=button]') || node)
                          .filter((node, index, arr) => arr.indexOf(node) === index)
                          .filter(visible)
                          .sort((a, b) => b.getBoundingClientRect().left - a.getBoundingClientRect().left);
                        const target = controls.find(node => {
                          const attrs = norm([
                            node.innerText || '',
                            node.value || '',
                            node.getAttribute('aria-label') || '',
                            node.getAttribute('title') || '',
                            node.getAttribute('name') || '',
                            node.className || ''
                          ].join(' '));
                          return /download|baixar|icon-download/.test(attrs);
                        }) || controls[0] || row;
                        const targetRect = target === row ? null : target.getBoundingClientRect();
                        const ready = !/processando|gerando|aguarde|pendente|em andamento|solicitado/.test(rowText);
                        const detailBonus = /historico detalhado|hist.rico detalhado|detalhado/.test(rowText) ? 5000 : 0;
                        const summaryPenalty = /historico resumo|hist.rico resumo/.test(rowText) ? 1200 : 0;
                        const clickX = targetRect ? Math.round(targetRect.left + targetRect.width / 2) : Math.round(rect.right - 22);
                        const clickY = targetRect ? Math.round(targetRect.top + targetRect.height / 2) : Math.round(rect.top + rect.height / 2);
                        return {
                          e: target,
                          text: target === row ? 'row-right-edge' : norm(target.innerText || target.value || target.getAttribute('aria-label') || target.getAttribute('title') || target.getAttribute('name') || 'download'),
                          rowText: rowText.slice(0, 260),
                          score: (ready ? 3000 : -1500) + detailBonus - summaryPenalty + Math.max(0, 1600 - rect.top) + Math.max(0, clickX) + (target === row ? 0 : 800),
                          tag: target.tagName,
                          role: target.getAttribute('role') || '',
                          x: targetRect ? Math.round(targetRect.x) : Math.round(rect.right - 44),
                          y: targetRect ? Math.round(targetRect.y) : Math.round(rect.y),
                          w: targetRect ? Math.round(targetRect.width) : 44,
                          h: targetRect ? Math.round(targetRect.height) : Math.round(rect.height),
                          rowY: Math.round(rect.y),
                          clickX,
                          clickY,
                          source: 'text-fallback'
                        };
                      })
                      .filter(Boolean)
                      .sort((a, b) => b.score - a.score);
                    reportRows = fallbackRows;
                  }
                  const iconChosen = reportRows[0];
                  const iconSummary = reportRows.slice(0, 8).map(({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}) => ({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}));
                  if (iconChosen) {
                    iconChosen.e.scrollIntoView({block: 'center', inline: 'center'});
                    iconChosen.e.focus && iconChosen.e.focus();
                    const clickRect = iconChosen.e.getBoundingClientRect();
                    return {
                      clicked: true,
                      method: 'latest_report_icon',
                      targetText: iconChosen.text,
                      rowText: iconChosen.rowText,
                      tag: iconChosen.tag,
                      role: iconChosen.role,
                      href: location.href,
                      clickX: Math.round(Number.isFinite(iconChosen.clickX) ? iconChosen.clickX : clickRect.left + clickRect.width / 2),
                      clickY: Math.round(Number.isFinite(iconChosen.clickY) ? iconChosen.clickY : clickRect.top + clickRect.height / 2),
                      candidates: iconSummary
                    };
                  }
                  const exactTextRows = [...document.querySelectorAll('div,span,p,td,li,section,article')]
                    .filter(e => {
                      const rect = e.getBoundingClientRect();
                      const style = getComputedStyle(e);
                      return rect.width > 0 && rect.height > 0 && rect.top >= 0
                        && rect.top < (window.innerHeight || document.documentElement.clientHeight || 0)
                        && style.visibility !== 'hidden' && style.display !== 'none';
                    })
                    .map(e => {
                      const text = norm(e.innerText || e.textContent || '');
                      if (!rowLooksLikeExactReport(text)) return null;
                      let row = e;
                      for (let depth = 0; row && depth < 8; depth += 1, row = row.parentElement) {
                        const rowRect = row.getBoundingClientRect();
                        const rowText = norm(row.innerText || row.textContent || '');
                        if (
                          rowLooksLikeExactReport(rowText)
                          && rowRect.width >= 220
                          && rowRect.height >= 24
                          && rowRect.height <= 140
                          && rowRect.top >= 0
                          && rowRect.top < (window.innerHeight || document.documentElement.clientHeight || 0)
                        ) {
                          const clickX = Math.round(Math.min((window.innerWidth || document.documentElement.clientWidth || rowRect.right) - 18, rowRect.right - 24));
                          const clickY = Math.round(rowRect.top + rowRect.height / 2);
                          return {
                            e: row,
                            text: 'row-right-edge',
                            rowText: rowText.slice(0, 260),
                            tag: row.tagName,
                            role: row.getAttribute('role') || '',
                            x: Math.round(rowRect.x),
                            y: Math.round(rowRect.y),
                            w: Math.round(rowRect.width),
                            h: Math.round(rowRect.height),
                            rowY: Math.round(rowRect.y),
                            clickX,
                            clickY,
                            score: Math.max(0, 1600 - rowRect.top) + Math.max(0, clickX),
                            source: 'exact-row-right-edge'
                          };
                        }
                      }
                      const rect = e.getBoundingClientRect();
                      const clickX = Math.round(Math.min((window.innerWidth || document.documentElement.clientWidth || rect.right) - 18, rect.right + 90));
                      const clickY = Math.round(rect.top + rect.height / 2);
                      return {
                        e,
                        text: 'text-right-edge',
                        rowText: text.slice(0, 260),
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                        rowY: Math.round(rect.y),
                        clickX,
                        clickY,
                        score: Math.max(0, 1200 - rect.top) + Math.max(0, clickX),
                        source: 'exact-text-right-edge'
                      };
                    })
                    .filter(Boolean)
                    .sort((a, b) => b.score - a.score);
                  const exactRowChosen = exactTextRows[0];
                  if (exactRowChosen) {
                    return {
                      clicked: true,
                      method: 'exact_report_row_right_edge',
                      targetText: exactRowChosen.text,
                      rowText: exactRowChosen.rowText,
                      tag: exactRowChosen.tag,
                      role: exactRowChosen.role,
                      href: location.href,
                      clickX: exactRowChosen.clickX,
                      clickY: exactRowChosen.clickY,
                      candidates: exactTextRows.slice(0, 8).map(({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}) => ({text, rowText, tag, role, x, y, w, h, rowY, score, source, clickX, clickY}))
                    };
                  }
                  if (!strongReportsArea) {
                    return {clicked: false, wrongPage: true, processing: /processando|gerando|aguarde|pendente|em andamento|solicitado/.test(bodyText), candidates: [], iconCandidates: iconSummary, bodyText: bodyText.slice(0, 500), href: location.href};
                  }
                  const nodes = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],label')]
                    .filter(visible)
                    .map(e => {
                      const text = norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                      return [e, text];
                    })
                    .filter(([e, text]) => {
                      if (!text || text.length > 80) return false;
                      if (/^exportar$/.test(text)) return false;
                      if (!/baixar|download|arquivo|excel|xlsx|csv|planilha/.test(text)) return false;
                      if (/filtrar|filtro|data da venda|historico|hoje|exportar relatorios|selecione o formato|avancar|fechar|acessar relatorios/.test(text)) return false;
                      const rect = e.getBoundingClientRect();
                      if (rect.left < 0 || rect.top < 0) return false;
                      const key = [e.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(([e, text]) => {
                      const rect = e.getBoundingClientRect();
                      const rowText = norm(e.closest('tr,li,[role=row],section,article,div')?.innerText || '');
                      const ready = !/processando|gerando|aguarde|pendente|em andamento|solicitado/.test(rowText);
                      const dataMatch = rowText.includes(__DATA_BR__) || rowText.includes(__DATA_DASH__) || rowText.includes(__DATA_ISO__);
                      const downloadText = /baixar|download/.test(text);
                      const fileText = /excel|xlsx|csv|planilha|arquivo/.test(text);
                      const tagBonus = /^(BUTTON|A|LABEL|INPUT)$/.test(e.tagName) || e.getAttribute('role') ? 1000 : 0;
                      return {
                        e,
                        text,
                        rowText: rowText.slice(0, 220),
                        score: (ready ? 2500 : -1500) + (dataMatch ? 1600 : 0) + (downloadText ? 1400 : 0) + (fileText ? 700 : 0) + tagBonus + Math.max(0, 160 - text.length) + Math.max(0, 1000 - rect.y / 2),
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = nodes[0];
                  const summary = nodes.slice(0, 12).map(({text, rowText, tag, role, x, y, w, h, score}) => ({text, rowText, tag, role, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, processing: /processando|gerando|aguarde|pendente|em andamento|solicitado/.test(bodyText), candidates: summary, iconCandidates: iconSummary, bodyText: bodyText.slice(0, 500)};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  const clickRect = chosen.e.getBoundingClientRect();
                  return {
                    clicked: true,
                    targetText: chosen.text,
                    rowText: chosen.rowText,
                    tag: chosen.tag,
                    role: chosen.role,
                    href: location.href,
                    clickX: Math.round(clickRect.left + clickRect.width / 2),
                    clickY: Math.round(clickRect.top + clickRect.height / 2),
                    candidates: summary
                  };
                })()
                """.replace("__DATA_BR__", json.dumps(data_br)).replace("__DATA_DASH__", json.dumps(data_br.replace("/", "-"))).replace("__DATA_ISO__", json.dumps(data_iso))
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_sales_reports_tab(session_id: str) -> dict:
                script = """
                (() => {
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    const vw = window.innerWidth || document.documentElement.clientWidth || 0;
                    const vh = window.innerHeight || document.documentElement.clientHeight || 0;
                    return rect.width > 0 && rect.height > 0
                      && rect.right > 0 && rect.bottom > 0 && rect.left < vw && rect.top < vh
                      && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const clickableSelector = 'button,a,[role=button],label';
                  window.scrollTo({top: 0, left: 0, behavior: 'instant'});
                  const seen = new Set();
                  const candidates = [...document.querySelectorAll('button,a,[role=button],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const text = norm(e.innerText || e.getAttribute('aria-label') || e.getAttribute('title') || '');
                      const target = e.closest(clickableSelector) || e;
                      return [e, target, text];
                    })
                    .filter(([e, target, text]) => {
                      if (text !== 'relatorios') return false;
                      if (!visible(target)) return false;
                      const rect = target.getBoundingClientRect();
                      const key = [target.tagName, text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(([e, target, text]) => {
                      const rect = target.getBoundingClientRect();
                      const tagBonus = /^(BUTTON|A|LABEL)$/.test(target.tagName) || target.getAttribute('role') ? 1000 : 0;
                      const navBand = rect.top >= 120 && rect.top <= 320 ? 1200 : 0;
                      return {
                        e: target,
                        text,
                        score: tagBonus + navBand + Math.max(0, 500 - rect.top),
                        tag: target.tagName,
                        role: target.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 8).map(({text, tag, role, x, y, w, h, score}) => ({text, tag, role, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary, href: location.href};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  const clickRect = chosen.e.getBoundingClientRect();
                  return {
                    clicked: true,
                    targetText: chosen.text,
                    tag: chosen.tag,
                    role: chosen.role,
                    href: location.href,
                    clickX: Math.round(clickRect.left + clickRect.width / 2),
                    clickY: Math.round(clickRect.top + clickRect.height / 2),
                    candidates: summary
                  };
                })()
                """
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def click_cielo_sales_detail_tab(session_id: str) -> dict:
                script = """
                (() => {
                  const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                  const visible = e => {
                    if (!e || e.disabled || e.getAttribute('aria-disabled') === 'true') return false;
                    const rect = e.getBoundingClientRect();
                    const style = getComputedStyle(e);
                    const vw = window.innerWidth || document.documentElement.clientWidth || 0;
                    const vh = window.innerHeight || document.documentElement.clientHeight || 0;
                    return rect.width > 0 && rect.height > 0
                      && rect.right > 0 && rect.bottom > 0 && rect.left < vw && rect.top < vh
                      && style.visibility !== 'hidden' && style.display !== 'none';
                  };
                  const clickableSelector = 'button,a,[role=tab],[role=button],label';
                  window.scrollTo({top: 0, left: 0, behavior: 'instant'});
                  const contextText = e => {
                    let current = e;
                    let best = '';
                    for (let depth = 0; current && depth < 5; depth++, current = current.parentElement) {
                      const text = norm(current.innerText || current.textContent || '');
                      if (text && text.length <= 500 && text.length > best.length) best = text;
                    }
                    return best;
                  };
                  const seen = new Set();
                  const candidates = [...document.querySelectorAll('button,a,[role=tab],[role=button],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const target = e.closest(clickableSelector) || e;
                      const text = norm(target.innerText || target.value || target.getAttribute('aria-label') || target.getAttribute('title') || e.innerText || e.textContent || '');
                      const ctx = contextText(target);
                      return {e: target, text, ctx};
                    })
                    .filter(item => {
                      if (!visible(item.e)) return false;
                      if (!item.text || item.text.length > 80) return false;
                      if (!/^(detalhado|detalhamento|vendas detalhadas|detalhado de vendas)$/.test(item.text)) return false;
                      if (/historico detalhado|histórico detalhado|relatorio|relatório|exportar|baixar|download|csv|xlsx/.test(item.text)) return false;
                      const rect = item.e.getBoundingClientRect();
                      const key = [item.e.tagName, item.text, Math.round(rect.x), Math.round(rect.y)].join(':');
                      if (seen.has(key)) return false;
                      seen.add(key);
                      return true;
                    })
                    .map(item => {
                      const rect = item.e.getBoundingClientRect();
                      const tabRole = item.e.getAttribute('role') === 'tab' ? 2500 : 0;
                      const clickableBonus = /^(BUTTON|A|LABEL)$/.test(item.e.tagName) || item.e.getAttribute('role') ? 1200 : 0;
                      const tabContext = item.ctx.includes('resumo') && (item.ctx.includes('calendario') || item.ctx.includes('calendário')) ? 3000 : 0;
                      const navBand = rect.top >= 80 && rect.top <= 420 ? 1000 : 0;
                      const selectedPenalty = item.e.getAttribute('aria-selected') === 'true' || /active|selected|selecionado/.test(String(item.e.className || '')) ? -250 : 0;
                      return {
                        ...item,
                        score: tabContext + tabRole + clickableBonus + navBand + selectedPenalty + Math.max(0, 1000 - rect.top),
                        tag: item.e.tagName,
                        role: item.e.getAttribute('role') || '',
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .sort((a, b) => b.score - a.score);
                  const chosen = candidates[0];
                  const summary = candidates.slice(0, 8).map(({text, ctx, tag, role, x, y, w, h, score}) => ({text, context: ctx.slice(0, 220), tag, role, x, y, w, h, score}));
                  if (!chosen) return {clicked: false, candidates: summary, href: location.href};
                  chosen.e.scrollIntoView({block: 'center', inline: 'center'});
                  chosen.e.focus && chosen.e.focus();
                  chosen.e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                  chosen.e.click();
                  return {
                    clicked: true,
                    targetText: chosen.text,
                    context: chosen.ctx.slice(0, 220),
                    tag: chosen.tag,
                    role: chosen.role,
                    href: location.href,
                    candidates: summary
                  };
                })()
                """
                result = await eval_js(session_id, script, timeout=10.0)
                return result if isinstance(result, dict) else {"clicked": bool(result)}

            async def download_cielo_generated_report_from_reports_area(session_id: str, started_at: float) -> str | None:
                async def navigate_cielo_reports_area(reason: str) -> bool:
                    cielo_log(
                        "export_reports_direct_navigate_skipped",
                        reason=reason,
                        reason_detail="direct_reports_url_redirects_to_login_on_cielo",
                    )
                    return False
                    report_urls = (
                        "https://minhaconta2.cielo.com.br/site/relatorios",
                        "https://minhaconta2.cielo.com.br/site/relatorios/vendas",
                    )
                    markers = (
                        "meus relatorios",
                        "seus relatorios",
                        "relatorios solicitados",
                        "central de relatorios",
                        "historico de relatorios",
                        "relatorios gerados",
                        "arquivos gerados",
                        "tipo de relatorio",
                        "data da solicitacao",
                        "relatorio inicio",
                        "vendas cielo historico",
                    )
                    for url in report_urls:
                        _check_cancelled()
                        try:
                            cielo_log("export_reports_direct_navigate_start", reason=reason, url=url)
                            await cdp("Page.navigate", {"url": url}, session_id=session_id, timeout=10.0)
                            await asyncio.sleep(7.0)
                            state = await eval_js(
                                session_id,
                                """
                                (() => ({
                                  href: location.href,
                                  text: (document.body?.innerText || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase().slice(0, 900)
                                }))()
                                """,
                                timeout=10.0,
                            )
                            state = state if isinstance(state, dict) else {"state": state}
                            state_text = str(state.get("text", ""))
                            current_url = str(state.get("href", ""))
                            opened = "/relatorio" in current_url or "/relatorios" in current_url or any(
                                marker in state_text for marker in markers
                            )
                            cielo_log(
                                "export_reports_direct_navigate_result",
                                reason=reason,
                                requested_url=url,
                                current_url=current_url,
                                opened=opened,
                                state=state,
                            )
                            if opened:
                                return True
                        except Exception as exc:
                            cielo_log(
                                "export_reports_direct_navigate_error",
                                reason=reason,
                                requested_url=url,
                                error=str(exc),
                                error_type=type(exc).__name__,
                            )
                    return False

                reports_cta = {"clicked": False}
                for cta_attempt in range(1, 16):
                    _check_cancelled()
                    downloaded = await asyncio.to_thread(
                        _wait_for_cielo_downloaded_report,
                        browser_download_dir,
                        data_br,
                        started_at,
                        0.5,
                        True,
                    )
                    if downloaded:
                        cielo_log("export_reports_download_detected_while_waiting_cta", attempt=cta_attempt, downloaded=downloaded)
                        return downloaded
                    reports_cta = await click_cielo_reports_cta(session_id)
                    if cta_attempt <= 3 or bool(reports_cta.get("clicked")) or cta_attempt % 5 == 0:
                        cielo_log("export_reports_cta_click", attempt=cta_attempt, result=reports_cta)
                    if bool(reports_cta.get("clicked")):
                        await save_cielo_page_snapshot(session_id, "before_reports_cta_native")
                        native_cta_clicked = await dispatch_cielo_native_click(session_id, reports_cta)
                        cielo_log("export_reports_cta_native_click", attempt=cta_attempt, clicked=native_cta_clicked, result=reports_cta)
                        await asyncio.sleep(6.0)
                        await save_cielo_page_snapshot(session_id, "after_reports_cta_native")
                        try:
                            reports_state = await eval_js(
                                session_id,
                                """
                                (() => ({
                                  href: location.href,
                                  text: (document.body?.innerText || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase().slice(0, 700)
                                }))()
                                """,
                                timeout=10.0,
                            )
                        except Exception as exc:
                            reports_state = {"error": str(exc)}
                        cielo_log("export_reports_after_cta", state=reports_state)
                        drawer_click = await click_cielo_ready_report_download(session_id)
                        cielo_log("export_reports_drawer_download_click_after_cta", attempt=cta_attempt, result=drawer_click)
                        if bool(drawer_click.get("clicked")):
                            native_drawer_clicked = await dispatch_cielo_native_click(session_id, drawer_click)
                            cielo_log(
                                "export_reports_drawer_download_native_click_after_cta",
                                attempt=cta_attempt,
                                clicked=native_drawer_clicked,
                                result=drawer_click,
                            )
                            downloaded = await asyncio.to_thread(
                                _wait_for_cielo_downloaded_report,
                                browser_download_dir,
                                data_br,
                                started_at,
                                12.0,
                                True,
                            )
                            if downloaded:
                                cielo_log("export_reports_drawer_download_detected_after_cta", attempt=cta_attempt, downloaded=downloaded)
                                return downloaded
                        state_text = str((reports_state or {}).get("text", "")) if isinstance(reports_state, dict) else ""
                        state_href = str((reports_state or {}).get("href", "")) if isinstance(reports_state, dict) else ""
                        if (
                            ("/vendas/resumo" in state_href or "/vendas/detalhado" in state_href)
                            and ("seu relatorio ja esta em processamento" in state_text or "acessar relatorios" in state_text)
                        ):
                            second_cta = await click_cielo_reports_cta(session_id)
                            cielo_log("export_reports_cta_second_click", result=second_cta)
                            if bool(second_cta.get("clicked")):
                                native_second_cta_clicked = await dispatch_cielo_native_click(session_id, second_cta)
                                cielo_log("export_reports_cta_second_native_click", clicked=native_second_cta_clicked, result=second_cta)
                                await asyncio.sleep(6.0)
                        if ("/vendas/resumo" in state_href or "/vendas/detalhado" in state_href) and not any(
                            marker in state_text
                            for marker in (
                                "meus relatorios",
                                "seus relatorios",
                                "relatorios solicitados",
                                "central de relatorios",
                                "historico de relatorios",
                                "relatorios gerados",
                                "arquivos gerados",
                                "baixar relatorio",
                                "download do relatorio",
                                "relatorio pronto",
                            )
                        ):
                            reports_tab = await click_cielo_sales_reports_tab(session_id)
                            cielo_log("export_reports_tab_click_after_cta", result=reports_tab)
                            if bool(reports_tab.get("clicked")):
                                native_tab_clicked = await dispatch_cielo_native_click(session_id, reports_tab)
                                cielo_log("export_reports_tab_native_click_after_cta", clicked=native_tab_clicked, result=reports_tab)
                                await asyncio.sleep(8.0)
                                await save_cielo_page_snapshot(session_id, "after_reports_tab_native")
                                try:
                                    tab_state = await eval_js(
                                        session_id,
                                        """
                                        (() => ({
                                          href: location.href,
                                          text: (document.body?.innerText || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase().slice(0, 700)
                                        }))()
                                        """,
                                        timeout=10.0,
                                    )
                                except Exception as exc:
                                    tab_state = {"error": str(exc)}
                                cielo_log("export_reports_after_tab_click", state=tab_state)
                                tab_href = str((tab_state or {}).get("href", "")) if isinstance(tab_state, dict) else ""
                                tab_text = str((tab_state or {}).get("text", "")) if isinstance(tab_state, dict) else ""
                                if (
                                    "/vendas/resumo" in tab_href
                                    or "/vendas/detalhado" in tab_href
                                    or not any(
                                        marker in tab_text
                                        for marker in (
                                            "meus relatorios",
                                            "seus relatorios",
                                            "relatorios solicitados",
                                            "central de relatorios",
                                            "historico de relatorios",
                                            "relatorios gerados",
                                            "arquivos gerados",
                                            "tipo de relatorio",
                                            "data da solicitacao",
                                            "relatorio inicio",
                                        )
                                    )
                                ):
                                    await navigate_cielo_reports_area("cta_or_tab_stayed_on_sales")
                            else:
                                await navigate_cielo_reports_area("reports_tab_not_clicked_after_cta")
                        break
                    await asyncio.sleep(3.0)
                if not bool(reports_cta.get("clicked")):
                    current_url = await eval_js(session_id, "location.href", timeout=10.0)
                    cielo_log("export_reports_cta_not_found", current_url=current_url)
                    reports_tab = await click_cielo_sales_reports_tab(session_id)
                    cielo_log("export_reports_tab_click", result=reports_tab)
                    if bool(reports_tab.get("clicked")):
                        native_tab_clicked = await dispatch_cielo_native_click(session_id, reports_tab)
                        cielo_log("export_reports_tab_native_click", clicked=native_tab_clicked, result=reports_tab)
                        await asyncio.sleep(8.0)
                    await navigate_cielo_reports_area("cta_not_found")

                latest_report_icon_clicked = False
                wrong_page_count = 0
                for attempt in range(1, 31):
                    _check_cancelled()
                    downloaded = await asyncio.to_thread(
                        _wait_for_cielo_downloaded_report,
                        browser_download_dir,
                        data_br,
                        started_at,
                        1.0,
                        True,
                    )
                    if downloaded:
                        cielo_log("export_reports_download_detected_before_click", attempt=attempt, downloaded=downloaded)
                        return downloaded
                    try:
                        current_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    except Exception:
                        current_url = ""
                    if latest_report_icon_clicked:
                        click_result = {"clicked": False, "skipped": True, "reason": "latest_report_icon_already_clicked"}
                    else:
                        click_result = await click_cielo_ready_report_download(session_id)
                    if attempt <= 3 or bool(click_result.get("clicked")) or attempt % 5 == 0:
                        cielo_log("export_reports_ready_download_click", attempt=attempt, current_url=current_url, result=click_result)
                    if not bool(click_result.get("clicked")) and bool(click_result.get("wrongPage")):
                        wrong_page_count += 1
                    else:
                        wrong_page_count = 0
                    if wrong_page_count >= 4:
                        cielo_log("export_reports_wrong_page_abort", attempt=attempt, current_url=current_url, result=click_result)
                        return None
                    click_body_text = _normalize_ascii_text(str(click_result.get("bodyText") or ""))
                    missing_reports_panel = not (
                        "tipo de relatorio" in click_body_text
                        or "data da solicitacao" in click_body_text
                        or "vendas cielo historico" in click_body_text
                    )
                    if (
                        not bool(click_result.get("clicked"))
                        and (bool(click_result.get("wrongPage")) or missing_reports_panel)
                        and ("/vendas/resumo" in current_url or "/vendas/detalhado" in current_url)
                        and attempt in {1, 5, 10, 15, 20}
                    ):
                        reports_tab = await click_cielo_sales_reports_tab(session_id)
                        cielo_log("export_reports_tab_click_retry", attempt=attempt, result=reports_tab)
                        if bool(reports_tab.get("clicked")):
                            native_tab_clicked = await dispatch_cielo_native_click(session_id, reports_tab)
                            cielo_log("export_reports_tab_native_click_retry", attempt=attempt, clicked=native_tab_clicked, result=reports_tab)
                            await asyncio.sleep(8.0)
                            continue
                        await navigate_cielo_reports_area("wrong_page_retry")
                    if bool(click_result.get("clicked")):
                        native_report_clicked = await dispatch_cielo_native_click(session_id, click_result)
                        cielo_log("export_reports_ready_download_native_click", attempt=attempt, clicked=native_report_clicked, result=click_result)
                        if str(click_result.get("method") or "") in {
                            "direct_download_icon",
                            "latest_report_icon",
                            "exact_report_row_right_edge",
                        }:
                            latest_report_icon_clicked = True
                        downloaded = await asyncio.to_thread(
                            _wait_for_cielo_downloaded_report,
                            browser_download_dir,
                            data_br,
                            started_at,
                            8.0,
                            True,
                        )
                        if downloaded:
                            cielo_log("export_reports_download_detected_after_click", attempt=attempt, downloaded=downloaded)
                            return downloaded
                    await asyncio.sleep(4.0)
                cielo_log("export_reports_download_timeout", files=_cielo_download_snapshot(started_at))
                return None

            async def select_cielo_email_delivery(session_id: str) -> bool:
                return bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                          const fire = e => {
                            if (!e) return false;
                            e.scrollIntoView({block: 'center'});
                            e.focus && e.focus();
                            e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                            e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                            e.click();
                            e.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                            e.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                            return true;
                          };
                          const directInput = document.querySelector('input#EMAIL, input[type=radio][id*="EMAIL" i], input[type=radio][value*="EMAIL" i]');
                          if (visible(directInput)) {
                            fire(directInput.closest('flui-radio-button-v2') || directInput.closest('label') || directInput);
                            fire(directInput);
                            return true;
                          }
                          const directLabel = [...document.querySelectorAll('label[for],label')]
                            .find(e => visible(e) && /e-?mail para|gmail\\.com/.test(norm(e.innerText || e.textContent || '')) && !/sms|whatsapp|reenviar|novo codigo|novo token/.test(norm(e.innerText || e.textContent || '')));
                          if (directLabel) {
                            const linked = directLabel.getAttribute('for') ? document.getElementById(directLabel.getAttribute('for')) : null;
                            fire(directLabel.closest('flui-radio-button-v2') || directLabel.parentElement || directLabel);
                            if (linked) fire(linked);
                            return true;
                          }
                          const isEmail = text => (/e-?mail para|gmail\\.com|receber por e-?mail/.test(text) && !/sms|whatsapp|reenviar|reenvie|novo codigo|novo token/.test(text));
                          const all = [...document.querySelectorAll('label,button,a,[role=button],[role=radio],[role=option],input,span,div')]
                            .filter(visible)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || e.textContent || '')])
                            .filter(([e, text]) => text && isEmail(text));
                          if (!all.length) return false;
                          all.sort((a, b) => {
                            const ar = a[0].getBoundingClientRect();
                            const br = b[0].getBoundingClientRect();
                            return (ar.height * ar.width) - (br.height * br.width);
                          });
                          const textNode = all[0][0];
                          const candidates = [
                            textNode.closest('label'),
                            textNode.closest('[role=radio]'),
                            textNode.closest('[role=option]'),
                            textNode.closest('[role=button]'),
                            textNode.closest('button'),
                            textNode.closest('a'),
                            textNode.closest('.mat-radio-button'),
                            textNode.closest('.flui-radio'),
                            textNode.closest('.flui-option'),
                            textNode.closest('.option'),
                            textNode.closest('.card'),
                            textNode.parentElement,
                            textNode
                          ].filter(Boolean);
                          for (const root of candidates) {
                            const input = root.querySelector && root.querySelector('input[type=radio],input[type=checkbox]');
                            if (input && !input.disabled) {
                              fire(root);
                              fire(input);
                              return true;
                            }
                          }
                          const target = candidates.find(visible);
                          if (!target) return false;
                          return fire(target);
                        })()
                        """,
                        timeout=10.0,
                    )
                )

            async def click_cielo_email_delivery_confirm(session_id: str) -> bool:
                clicked = bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                          const reject = /sms|whatsapp|e-?mail para|gmail\\.com|reenviar|voltar|cancelar|sair|primeiro acesso|esqueci/;
                          const buttons = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                            .filter(visible)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                            .filter(([e, text]) => text && /confirmar|continuar|enviar|receber|prosseguir|avancar/.test(text) && !reject.test(text));
                          if (!buttons.length) return false;
                          const target = buttons[0][0];
                          target.scrollIntoView({block: 'center'});
                          target.focus && target.focus();
                          target.click();
                          return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                )
                if clicked:
                    return True
                return await click_by_text(
                    session_id,
                    (
                        "confirmar",
                        "continuar",
                        "enviar",
                        "enviar codigo",
                        "enviar código",
                        "receber codigo",
                        "receber código",
                        "prosseguir",
                        "avancar",
                        "avançar",
                    ),
                    timeout=4.0,
                    reject_markers=cielo_resend_reject_markers,
                )

            async def click_cielo_token_confirm(session_id: str) -> bool:
                reject_markers_json = json.dumps([_normalize_ascii_text(marker) for marker in cielo_resend_reject_markers])
                try:
                    focused_token_input = bool(
                        await eval_js(
                            session_id,
                            """
                            (() => {
                              const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                              const inputs = [...document.querySelectorAll('input')]
                                .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()));
                              const filled = inputs.filter(e => String(e.value || '').trim());
                              const target = filled[filled.length - 1] || inputs[inputs.length - 1];
                              if (!target) return false;
                              target.scrollIntoView({block: 'center'});
                              target.focus();
                              return true;
                            })()
                            """,
                            timeout=10.0,
                        )
                    )
                    if focused_token_input:
                        await cdp(
                            "Input.dispatchKeyEvent",
                            {"type": "rawKeyDown", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                            session_id=session_id,
                            timeout=5.0,
                        )
                        await cdp(
                            "Input.dispatchKeyEvent",
                            {"type": "keyUp", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                            session_id=session_id,
                            timeout=5.0,
                        )
                        await asyncio.sleep(0.8)
                except Exception:
                    pass
                token_confirm_script = """
                        (() => {
                          const rejectMarkers = __REJECT_MARKERS__;
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                          const reject = /e-?mail|email|sms|whatsapp|voltar|cancelar|sair|alterar/;
                          const rejected = text => reject.test(text) || rejectMarkers.some(marker => marker && text.includes(marker));
                          const tokenInputs = [...document.querySelectorAll('input')]
                            .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button|email/.test((e.type || '').toLowerCase()));
                          const tokenY = tokenInputs.length
                            ? Math.min(...tokenInputs.map(e => e.getBoundingClientRect().top))
                            : -Infinity;
                          const candidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                            .filter(visible)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                            .filter(([e, text]) => text && /verificar|validar|confirmar|continuar|entrar|acessar|prosseguir|avancar/.test(text) && !rejected(text));
                          const scoped = candidates.find(([e]) => {
                            const y = e.getBoundingClientRect().top;
                            return y >= tokenY - 80 && y <= tokenY + 600;
                          });
                          const chosen = scoped || candidates[0] || null;
                          const target = chosen ? chosen[0] : null;
                          if (!target) return {clicked: false, method: 'primary', targetText: '', candidatesCount: candidates.length};
                          target.scrollIntoView({block: 'center'});
                          target.focus && target.focus();
                          target.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                          target.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                          target.click();
                          return {clicked: true, method: 'primary', targetText: chosen ? chosen[1] : '', candidatesCount: candidates.length};
                        })()
                        """.replace("__REJECT_MARKERS__", reject_markers_json)
                click_result = await eval_js(
                        session_id,
                        token_confirm_script,
                        timeout=10.0,
                    )
                click_result = click_result if isinstance(click_result, dict) else {"clicked": bool(click_result), "method": "primary"}
                cielo_log("auth_token_confirm_primary_result", result=click_result)
                clicked = bool(click_result.get("clicked"))
                if clicked:
                    return True
                clicked = await click_by_text(
                    session_id,
                    (
                        "verificar",
                        "verificar codigo",
                        "verificar código",
                        "validar",
                        "validar codigo",
                        "validar código",
                        "confirmar",
                        "continuar",
                        "entrar",
                        "acessar",
                    ),
                    timeout=4.0,
                    reject_markers=cielo_resend_reject_markers,
                )
                if clicked:
                    return True
                if await click_submit(session_id, reject_markers=cielo_resend_reject_markers):
                    return True
                try:
                    await cdp(
                        "Input.dispatchKeyEvent",
                        {"type": "rawKeyDown", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                        session_id=session_id,
                        timeout=5.0,
                    )
                    await cdp(
                        "Input.dispatchKeyEvent",
                        {"type": "keyUp", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                        session_id=session_id,
                        timeout=5.0,
                    )
                    return True
                except Exception:
                    return False

            async def wait_for_password(session_id: str, timeout: float = 35.0) -> bool:
                deadline = time.time() + timeout
                while time.time() < deadline:
                    has_password = await eval_js(
                        session_id,
                        "[...document.querySelectorAll('input')].some(e => e.type === 'password' && (e.offsetWidth || e.offsetHeight || e.getClientRects().length))",
                        timeout=10.0,
                    )
                    if has_password:
                        return True
                    await asyncio.sleep(1.0)
                return False

            async def authenticate(session_id: str) -> None:
                email = str(credenciais.get("email") or "").strip()
                password = str(credenciais.get("password") or "").strip()
                _emit_pix_status(on_status, "Autenticando na Cielo...")
                try:
                    auth_start_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                except Exception:
                    auth_start_url = ""
                cielo_log("auth_start", current_url=auth_start_url, login_email=email, password_length=len(password))
                await show_cielo_banner(
                    session_id,
                    "Cielo aberta pelo app.\nSe aparecer reCAPTCHA / 'não sou um robô', resolva manualmente nesta janela.",
                    "#1d4ed8",
                )
                login_filled = await fill_cielo_login_input(session_id, email)
                cielo_log("auth_login_fill", filled=login_filled)
                if not login_filled:
                    raise RuntimeError("A Cielo não recebeu o login no campo inicial.")
                login_submit_clicked = await click_submit(session_id)
                cielo_log("auth_login_submit", clicked=login_submit_clicked)
                password_visible = await wait_for_password(session_id, timeout=12.0)
                cielo_log("auth_password_wait_initial", visible=password_visible)
                if not password_visible:
                    manual_challenge_visible = await cielo_manual_challenge_present(session_id)
                    cielo_log("auth_password_wait_blocked", manual_challenge_visible=manual_challenge_visible)
                    if manual_challenge_visible:
                        await wait_for_manual_cielo_challenge(session_id, "abrir campo de senha")
                        login_submit_clicked = await click_submit(session_id)
                        cielo_log("auth_login_submit_after_manual_challenge", clicked=login_submit_clicked)
                        password_visible = await wait_for_password(session_id, timeout=35.0)
                        cielo_log("auth_password_wait_after_manual_challenge", visible=password_visible)
                        if not password_visible:
                            raise RuntimeError("A Cielo não exibiu o campo de senha depois do e-mail.")
                    else:
                        raise RuntimeError("A Cielo não exibiu o campo de senha depois do e-mail.")
                login_state = await cielo_login_input_state(session_id, email)
                cielo_log("auth_login_state_before_password", state=login_state)
                if login_state.get("present") and not login_state.get("matches"):
                    login_refilled = await fill_cielo_login_input(session_id, email)
                    cielo_log("auth_login_refill_before_password", filled=login_refilled)
                    if not login_refilled:
                        raise RuntimeError("A Cielo não recebeu o login ao preencher a senha.")
                    login_state = await cielo_login_input_state(session_id, email)
                    cielo_log("auth_login_state_after_refill", state=login_state)
                if login_state.get("present") and not login_state.get("matches"):
                    raise RuntimeError("O login exibido pela Cielo não corresponde ao login configurado; envio bloqueado.")
                password_filled = await fill_password_input(session_id, password)
                cielo_log("auth_password_fill", filled=password_filled, password_length=len(password))
                if not password_filled:
                    raise RuntimeError("A Cielo não recebeu a senha no campo de senha.")
                login_state = await cielo_login_input_state(session_id, email)
                cielo_log("auth_login_state_before_password_submit", state=login_state)
                if login_state.get("present") and not login_state.get("matches"):
                    raise RuntimeError("O login foi alterado antes do envio da senha; envio bloqueado.")
                if await cielo_manual_challenge_present(session_id) or not await cielo_submit_enabled(session_id):
                    cielo_log(
                        "auth_wait_manual_challenge_before_password_submit",
                        manual_challenge_visible=await cielo_manual_challenge_present(session_id),
                        submit_enabled=await cielo_submit_enabled(session_id),
                    )
                    await wait_for_manual_cielo_challenge(session_id, "apos preencher a senha")
                    if not await cielo_submit_enabled(session_id):
                        cielo_log("auth_password_submit_button_not_detected_after_manual_challenge")
                password_submit_clicked = await click_submit(session_id)
                if not password_submit_clicked:
                    force_submit_result = await force_cielo_login_submit(session_id)
                    cielo_log("auth_password_force_submit_initial", result=force_submit_result)
                    password_submit_clicked = bool(force_submit_result.get("clicked"))
                if not password_submit_clicked:
                    try:
                        await cdp(
                            "Input.dispatchKeyEvent",
                            {"type": "rawKeyDown", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                            session_id=session_id,
                            timeout=5.0,
                        )
                        await cdp(
                            "Input.dispatchKeyEvent",
                            {"type": "keyUp", "key": "Enter", "code": "Enter", "windowsVirtualKeyCode": 13, "nativeVirtualKeyCode": 13},
                            session_id=session_id,
                            timeout=5.0,
                        )
                        password_submit_clicked = True
                    except Exception:
                        password_submit_clicked = False
                cielo_log("auth_password_submit", clicked=password_submit_clicked)
                await hide_cielo_banner(session_id)
                password_submit_started_at = time.time()
                password_submit_retry_count = 0
                last_password_submit_retry_at = password_submit_started_at

                ignored_tokens: set[str] = set()
                ignored_token_message_ids: set[str] = set()
                token_lookup_min_ts = max(0.0, password_submit_started_at - 15.0)
                deadline = time.time() + 300.0
                login_error_seen_at: float | None = None
                email_delivery_requested_at: float | None = None
                email_delivery_confirm_attempted = False
                email_delivery_manual_notice_shown = False
                last_token_poll_started_at = 0.0
                token_fetch_miss_count = 0
                token_manual_entry_waiting = False
                current_cielo_token: str | None = None
                current_cielo_token_last_submit = 0.0
                current_cielo_token_submit_attempts = 0
                token_manual_notice_shown = False
                last_auth_state_signature = None

                async def submit_cielo_token_from_gmail(fetch_timeout: float, allow_callback: bool = True) -> bool:
                    nonlocal current_cielo_token, current_cielo_token_last_submit, current_cielo_token_submit_attempts, last_token_poll_started_at, token_manual_notice_shown, token_fetch_miss_count, token_manual_entry_waiting
                    if current_cielo_token:
                        token = current_cielo_token
                        cielo_log(
                            "auth_token_reuse",
                            submit_attempts=current_cielo_token_submit_attempts,
                            seconds_since_last_submit=round(time.time() - current_cielo_token_last_submit, 1)
                            if current_cielo_token_last_submit
                            else None,
                        )
                    else:
                        if token_manual_entry_waiting:
                            seconds_since_last_poll = time.time() - last_token_poll_started_at if last_token_poll_started_at else None
                            if seconds_since_last_poll is not None and seconds_since_last_poll < 12.0:
                                cielo_log(
                                    "auth_token_waiting_manual_entry",
                                    miss_count=token_fetch_miss_count,
                                    seconds_until_retry=round(12.0 - seconds_since_last_poll, 1),
                                )
                                return False
                            cielo_log("auth_token_retry_gmail_after_manual_wait", miss_count=token_fetch_miss_count)
                        if time.time() - last_token_poll_started_at < 3.0:
                            cielo_log("auth_token_fetch_throttled")
                            return False
                        last_token_poll_started_at = time.time()
                        effective_fetch_timeout = 12.0 if token_fetch_miss_count else min(fetch_timeout, 30.0)
                        token_debug_info: dict[str, object] = {}
                        cielo_log(
                            "auth_token_fetch_start",
                            timeout=effective_fetch_timeout,
                            allow_callback=allow_callback,
                            miss_count=token_fetch_miss_count,
                            min_ts=token_lookup_min_ts,
                        )
                        token = _fetch_cielo_token_from_gmail(
                            timeout=effective_fetch_timeout,
                            on_status=on_status,
                            ignored_tokens=ignored_tokens,
                            ignored_message_ids=ignored_token_message_ids,
                            min_internal_ts=token_lookup_min_ts,
                            debug_info=token_debug_info,
                            cancel_event=cancel_event,
                        )
                        token_source = "gmail" if token else None
                        if not token:
                            token_fetch_miss_count += 1
                            last_token_poll_started_at = time.time()
                        if not token and allow_callback and callable(token_callback):
                            token = str(token_callback("Informe o código enviado por e-mail pela Cielo") or "").strip()
                            token_source = "manual_callback" if token else token_source
                        elif not token and allow_callback and token_fetch_miss_count >= 1:
                            token_manual_entry_waiting = True
                            _emit_pix_status(
                                on_status,
                                "Codigo da Cielo nao encontrado no Gmail; preencha/valide manualmente na janela se o codigo chegou.",
                            )
                            await show_cielo_banner(
                                session_id,
                                "Ação manual necessária\nO app não encontrou um novo código da Cielo no Gmail. Se o código chegou, preencha e confirme manualmente nesta janela.",
                                "#92400e",
                            )
                            cielo_log("auth_token_manual_entry_required_after_gmail_miss", miss_count=token_fetch_miss_count)
                            return False
                        cielo_log(
                            "auth_token_fetch_result",
                            found=bool(token),
                            source=token_source,
                            value_length=len(token or ""),
                            gmail=token_debug_info,
                        )
                        if token:
                            token_fetch_miss_count = 0
                            token_manual_entry_waiting = False
                            current_cielo_token = token
                            current_cielo_token_submit_attempts = 0
                    if not current_cielo_token:
                        cielo_log("auth_token_missing")
                        return False
                    if current_cielo_token_submit_attempts >= 1:
                        if not token_manual_notice_shown:
                            token_manual_notice_shown = True
                            _emit_pix_status(
                                on_status,
                                "Codigo da Cielo preenchido; confirme manualmente na janela para evitar bloqueio por excesso de tentativas.",
                            )
                            await show_cielo_banner(
                                session_id,
                                "Ação manual necessária\nO código da Cielo foi preenchido. Clique manualmente em Verificar/Confirmar para evitar excesso de tentativas automáticas.",
                                "#92400e",
                            )
                            cielo_log("auth_token_manual_confirmation_required", submit_attempts=current_cielo_token_submit_attempts)
                        return False
                    if time.time() - current_cielo_token_last_submit < 12.0:
                        cielo_log(
                            "auth_token_submit_waiting_cooldown",
                            seconds_since_last_submit=round(time.time() - current_cielo_token_last_submit, 1),
                        )
                        return False
                    token = current_cielo_token
                    _emit_pix_status(on_status, "Preenchendo codigo da Cielo...")
                    filled_token = await fill_cielo_token(session_id, token)
                    cielo_log("auth_token_fill_primary", filled=filled_token, value_length=len(token or ""))
                    if not filled_token:
                        inputs_count = int(
                            await eval_js(
                                session_id,
                                "[...document.querySelectorAll('input')].filter(e => e.type !== 'hidden' && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length)).length",
                                timeout=10.0,
                            )
                            or 0
                        )
                        target_index = max(0, inputs_count - 1)
                        filled_token = await fill_visible_input(session_id, target_index, token)
                        cielo_log("auth_token_fill_fallback", filled=filled_token, inputs_count=inputs_count, target_index=target_index)
                    if not filled_token:
                        cielo_log("auth_token_fill_failed")
                        return False
                    clicked_confirm = await click_cielo_token_confirm(session_id)
                    cielo_log("auth_token_confirm_click", clicked=clicked_confirm)
                    current_cielo_token_last_submit = time.time()
                    current_cielo_token_submit_attempts += 1
                    await asyncio.sleep(8.0)
                    return True

                while time.time() < deadline:
                    _check_cancelled()
                    await asyncio.sleep(2.0)
                    text = await visible_text(session_id)
                    text_norm = _normalize_ascii_text(text)
                    current_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    token_input_visible = await cielo_token_input_present(session_id)
                    resend_code_visible = any(
                        marker in text_norm
                        for marker in (
                            "reenviar codigo",
                            "reenviar token",
                            "reenvie o codigo",
                            "reenvie o token",
                            "novo codigo",
                            "novo token",
                            "enviar novamente",
                        )
                    )
                    token_challenge_visible = (
                        token_input_visible
                        or await cielo_token_challenge_present(session_id, text_norm)
                        or resend_code_visible
                    )
                    email_delivery_visible = any(
                        marker in text_norm
                        for marker in (
                            "e-mail para",
                            "email para",
                            "gmail.com",
                            "receber por e-mail",
                            "receber por email",
                            "enviar por e-mail",
                            "enviar por email",
                        )
                    )
                    manual_challenge_visible_now = await cielo_manual_challenge_present(session_id)
                    if manual_challenge_visible_now and not token_challenge_visible and not email_delivery_visible:
                        cielo_log("auth_manual_challenge_during_login")
                        await wait_for_manual_cielo_challenge(session_id, "validar login")
                        await asyncio.sleep(1.0)
                        current_url_after_challenge = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                        text_after_challenge_norm = _normalize_ascii_text(await visible_text(session_id))
                        if cielo_public_site_url(current_url_after_challenge):
                            cielo_log("auth_public_site_redirect_after_manual_challenge", current_url=current_url_after_challenge)
                            raise RuntimeError(
                                "A Cielo redirecionou para o site publico depois do reCAPTCHA, sem concluir o login."
                            )
                        if await cielo_token_challenge_present(session_id, text_after_challenge_norm) or any(
                            marker in text_after_challenge_norm
                            for marker in (
                                "e-mail para",
                                "email para",
                                "gmail.com",
                                "receber por e-mail",
                                "receber por email",
                                "enviar por e-mail",
                                "enviar por email",
                            )
                        ):
                            cielo_log("auth_manual_challenge_next_step_visible", current_url=current_url_after_challenge)
                            password_submit_started_at = time.time()
                            continue
                        if "acessos/login" not in current_url_after_challenge:
                            cielo_log("auth_manual_challenge_non_login_after_wait", current_url=current_url_after_challenge)
                            password_submit_started_at = time.time()
                            continue
                        challenge_submit_clicked = await click_submit(session_id)
                        cielo_log("auth_manual_challenge_submit", clicked=challenge_submit_clicked)
                        password_submit_started_at = time.time()
                        continue
                    login_error_visible = any(
                        marker in text_norm
                        for marker in (
                            "dados de acesso estao incorretos",
                            "usuario ou senha",
                            "senha incorreta",
                            "acesso incorreto",
                            "credenciais invalidas",
                        )
                    )
                    submit_enabled_now = await cielo_submit_enabled(session_id)
                    auth_state_signature = (
                        current_url,
                        token_input_visible,
                        token_challenge_visible,
                        email_delivery_visible,
                        resend_code_visible,
                        login_error_visible,
                        manual_challenge_visible_now,
                        submit_enabled_now,
                    )
                    if auth_state_signature != last_auth_state_signature:
                        last_auth_state_signature = auth_state_signature
                        cielo_log(
                            "auth_state",
                            current_url=current_url,
                            token_input_visible=token_input_visible,
                            token_challenge_visible=token_challenge_visible,
                            email_delivery_visible=email_delivery_visible,
                            resend_code_visible=resend_code_visible,
                            login_error_visible=login_error_visible,
                            manual_challenge_visible=manual_challenge_visible_now,
                            submit_enabled=submit_enabled_now,
                        )
                    if email_delivery_visible and not token_challenge_visible:
                        login_error_seen_at = None
                        if email_delivery_requested_at is None:
                            _emit_pix_status(on_status, "Selecionando envio do token da Cielo por e-mail...")
                            selected_email_delivery = await select_cielo_email_delivery(session_id)
                            if not selected_email_delivery:
                                selected_email_delivery = await click_by_text(
                                    session_id,
                                    ("e-mail para", "email para", "gmail.com", "receber por e-mail", "receber por email"),
                                    timeout=8.0,
                                    reject_markers=cielo_resend_reject_markers,
                                )
                            cielo_log("auth_email_delivery_select", selected=selected_email_delivery)
                            email_delivery_requested_at = time.time()
                            await asyncio.sleep(1.5)
                        if not email_delivery_confirm_attempted:
                            email_delivery_confirm_attempted = True
                            confirmed_email_delivery = await click_cielo_email_delivery_confirm(session_id)
                            if not confirmed_email_delivery:
                                confirmed_email_delivery = await click_submit(session_id, reject_markers=cielo_resend_reject_markers)
                            cielo_log("auth_email_delivery_confirm", clicked=confirmed_email_delivery)
                            await asyncio.sleep(4.0)
                            continue
                        if not email_delivery_manual_notice_shown:
                            email_delivery_manual_notice_shown = True
                            _emit_pix_status(
                                on_status,
                                "A Cielo ainda esta na confirmacao do e-mail; confirme manualmente na janela se o botao estiver disponivel.",
                            )
                            await show_cielo_banner(
                                session_id,
                                "Ação manual necessária\nSe a Cielo pedir confirmação depois de escolher o e-mail, clique no botão confirmar/continuar nesta janela.\nO app aguardará a tela do código.",
                                "#92400e",
                            )
                            cielo_log("auth_email_delivery_manual_notice")
                        await asyncio.sleep(2.0)
                        continue
                    if token_challenge_visible:
                        login_error_seen_at = None
                    elif login_error_visible and "acessos/login" in current_url:
                        if login_error_seen_at is None:
                            login_error_seen_at = time.time()
                            cielo_log("auth_login_error_visible", current_url=current_url)
                            _emit_pix_status(
                                on_status,
                                "A Cielo exibiu uma mensagem de credenciais, mas pode avancar apos o reCAPTCHA; aguardando...",
                            )
                        elif time.time() - login_error_seen_at > 75.0:
                            cielo_log("auth_login_error_timeout", current_url=current_url, elapsed=round(time.time() - login_error_seen_at, 1))
                            raise RuntimeError(
                                "A Cielo manteve a mensagem de dados de acesso incorretos e nao avancou apos a verificacao manual."
                            )
                    elif "acessos/login" not in current_url:
                        login_error_seen_at = None
                    token_error_visible = token_challenge_visible and any(
                        marker in text_norm
                        for marker in (
                            "codigo incorreto",
                            "codigo invalido",
                            "codigo expirado",
                            "codigo nao confere",
                            "token incorreto",
                            "token invalido",
                            "token expirado",
                            "tentativas excedidas",
                        )
                    )
                    if token_error_visible and (current_cielo_token or current_cielo_token_submit_attempts > 0):
                        if current_cielo_token:
                            ignored_tokens.add(current_cielo_token)
                        cielo_log(
                            "auth_token_rejected_by_cielo",
                            had_token=bool(current_cielo_token),
                            submit_attempts=current_cielo_token_submit_attempts,
                        )
                        current_cielo_token = None
                        current_cielo_token_last_submit = 0.0
                        current_cielo_token_submit_attempts = 0
                        token_manual_entry_waiting = False
                        token_fetch_miss_count = 0
                        last_token_poll_started_at = 0.0
                        _emit_pix_status(
                            on_status,
                            "A Cielo rejeitou o codigo; buscando o e-mail de token mais recente novamente...",
                        )
                        await asyncio.sleep(2.0)
                        continue
                    if "acessos/login" in current_url and not token_challenge_visible:
                        password_visible = bool(
                            await eval_js(
                                session_id,
                                "[...document.querySelectorAll('input')].some(e => e.type === 'password' && (e.offsetWidth || e.offsetHeight || e.getClientRects().length))",
                                timeout=10.0,
                            )
                        )
                        if password_visible and time.time() - password_submit_started_at > 90.0 and not login_error_visible:
                            cielo_log(
                                "auth_password_submit_timeout",
                                current_url=current_url,
                                elapsed=round(time.time() - password_submit_started_at, 1),
                            )
                            raise RuntimeError(
                                "A Cielo não avançou após a senha. Verifique as credenciais no credenciais.txt."
                            )
                        if (
                            password_visible
                            and not login_error_visible
                            and not manual_challenge_visible_now
                            and password_submit_retry_count < 1
                            and time.time() - last_password_submit_retry_at >= 8.0
                        ):
                            password_submit_retry_count += 1
                            last_password_submit_retry_at = time.time()
                            retry_result = await force_cielo_login_submit(session_id)
                            cielo_log(
                                "auth_password_submit_retry",
                                attempt=password_submit_retry_count,
                                result=retry_result,
                                elapsed=round(time.time() - password_submit_started_at, 1),
                            )
                            await asyncio.sleep(3.0)
                            continue
                    if "acessos/login" not in current_url and not token_challenge_visible:
                        if cielo_public_site_url(current_url):
                            cielo_log("auth_public_site_redirect", current_url=current_url, elapsed=round(time.time() - password_submit_started_at, 1))
                            raise RuntimeError(
                                "A Cielo redirecionou para o site publico, nao para a area autenticada. O app nao abriu Minhas Vendas para evitar falsa autenticacao."
                            )
                        if not cielo_authenticated_portal_url(current_url):
                            cielo_log(
                                "auth_non_login_unknown_url",
                                current_url=current_url,
                                elapsed=round(time.time() - password_submit_started_at, 1),
                            )
                            await asyncio.sleep(2.0)
                            continue
                        cielo_log("auth_success", current_url=current_url, elapsed=round(time.time() - password_submit_started_at, 1))
                        return
                    if (
                        not resend_code_visible
                        and any(marker in text_norm for marker in ("email", "e-mail"))
                        and any(marker in text_norm for marker in ("codigo", "token", "verificacao", "autenticacao"))
                    ):
                        fallback_delivery_clicked = await click_by_text(
                            session_id,
                            ("e-mail", "email", "enviar codigo", "receber codigo"),
                            timeout=4.0,
                            reject_markers=cielo_resend_reject_markers,
                        )
                        fallback_submit_clicked = await click_submit(session_id, reject_markers=cielo_resend_reject_markers)
                        cielo_log(
                            "auth_email_delivery_fallback_click",
                            delivery_clicked=fallback_delivery_clicked,
                            submit_clicked=fallback_submit_clicked,
                        )
                    if token_challenge_visible:
                        await submit_cielo_token_from_gmail(fetch_timeout=45.0)
                cielo_log("auth_timeout")
                raise RuntimeError("A Cielo não confirmou a autenticação dentro do tempo limite.")

            last_cielo_export_state: dict[str, object] = {}

            def _cielo_download_snapshot(started_at: float) -> list[dict[str, object]]:
                items: list[dict[str, object]] = []
                try:
                    for path in sorted(Path(browser_download_dir).glob("*"), key=lambda item: item.stat().st_mtime, reverse=True):
                        stat = path.stat()
                        items.append(
                            {
                                "name": path.name,
                                "suffix": path.suffix.lower(),
                                "effective_suffix": _effective_local_report_suffix(path),
                                "size": stat.st_size,
                                "mtime": datetime.fromtimestamp(stat.st_mtime).isoformat(timespec="seconds"),
                                "new": stat.st_mtime >= started_at - 1,
                            }
                        )
                except Exception as exc:
                    items.append({"error": str(exc), "error_type": type(exc).__name__})
                return items[:20]

            def _cielo_export_state_is_terminal_no_result() -> bool:
                date_selection_trusted = bool(last_cielo_export_state.get("dateSelectionTrusted"))
                return bool(
                    date_selection_trusted
                    and last_cielo_export_state.get("noResultsVisible")
                    and _normalize_ascii_text(str(last_cielo_export_state.get("targetText") or "")) == "exportar"
                )

            async def select_cielo_historical_sale_date(session_id: str) -> dict:
                script = r"""
                (async (dataBr, dataIso) => {
                  const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
                  const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                  const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                  const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value')?.set;
                  const [dayText, monthText, yearText] = dataBr.split('/');
                  const day = String(Number(dayText || '0'));
                  const monthIndex = Math.max(0, Number(monthText || '1') - 1);
                  const monthPt = ['janeiro','fevereiro','marco','abril','maio','junho','julho','agosto','setembro','outubro','novembro','dezembro'][monthIndex];
                  const monthPtAccent = ['janeiro','fevereiro','março','abril','maio','junho','julho','agosto','setembro','outubro','novembro','dezembro'][monthIndex];
                  const monthEn = ['january','february','march','april','may','june','july','august','september','october','november','december'][monthIndex];
                  const result = {
                    selected: false,
                    trusted: false,
                    method: null,
                    monthNavClicks: 0,
                    dateBr: dataBr,
                    dateIso: dataIso,
                    inputValuesBefore: [],
                    inputValuesAfter: [],
                    exportStateAfter: null,
                    visibleButtonsAfterCalendar: [],
                    visibleCalendarLikeNodes: [],
                    exactRangeForced: false,
                    exactRangeValue: null,
                  };
                  const exactRangeValue = `${dataBr} At\u00e9 ${dataBr}`;
                  const exactRangeNorm = norm(exactRangeValue);

                  const inputSnapshot = () => [...document.querySelectorAll('input')]
                    .filter(visible)
                    .map(e => ({
                      type: e.type || '',
                      name: e.name || e.id || e.placeholder || e.getAttribute('aria-label') || '',
                      value: e.value || '',
                      text: (e.closest('label,div,section,form')?.innerText || '').slice(0, 120),
                    }))
                    .slice(0, 20);

                  const exportState = () => {
                    const all = [...document.querySelectorAll('body *')].filter(e => !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length)));
                    const titlePattern = /consolidado de vendas|detalhado de vendas|detalhamento de vendas|vendas detalhadas|historico de vendas|histórico de vendas|detalhes da venda|detalhe da venda|consolidado/;
                    const title = all.find(e => {
                      const text = norm(e.innerText || e.textContent || '');
                      return text.length <= 180 && titlePattern.test(text);
                    });
                    const titleY = title ? title.getBoundingClientRect().top : -Infinity;
                    const candidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                      .filter(e => visible(e) || !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length)))
                      .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                      .filter(([e, text]) => /exportar|baixar|download|excel|xlsx|csv/.test(text));
                    const target = candidates.find(([e]) => {
                      const y = e.getBoundingClientRect().top;
                      return title && y >= titleY - 40 && y <= titleY + 700;
                    }) || candidates[0];
                    return {
                      available: !!(target && !target[0].disabled && target[0].getAttribute('aria-disabled') !== 'true'),
                      targetText: target ? target[1] : '',
                      targetDisabled: target ? !!target[0].disabled : null,
                    };
                  };

                  const dispatchClick = el => {
                    if (!el || !visible(el)) return false;
                    el.scrollIntoView({block: 'center', inline: 'center'});
                    el.focus && el.focus();
                    el.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                    el.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                    el.click();
                    return true;
                  };

                  const setInputValue = (input, value) => {
                    input.scrollIntoView({block: 'center', inline: 'center'});
                    input.focus();
                    if (setter) setter.call(input, '');
                    else input.value = '';
                    input.dispatchEvent(new Event('input', {bubbles: true, composed: true}));
                    if (setter) setter.call(input, value);
                    else input.value = value;
                    input.dispatchEvent(new InputEvent('input', {bubbles: true, composed: true, inputType: 'insertText', data: value}));
                    input.dispatchEvent(new Event('change', {bubbles: true, composed: true}));
                    input.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true}));
                  };

                  const plausibleDateInputs = () => [...document.querySelectorAll('input')]
                    .filter(e => visible(e) && !/hidden|checkbox|radio|submit|button/.test((e.type || '').toLowerCase()))
                    .filter(e => {
                      const hint = norm([
                        e.type,
                        e.name,
                        e.id,
                        e.placeholder,
                        e.getAttribute('aria-label'),
                        e.value,
                        e.closest('label,div,section,form')?.innerText || '',
                      ].join(' '));
                      return /data|periodo|historico|histórico|venda|calendar|date/.test(hint) || /\d{2}\/\d{2}\/\d{4}/.test(e.value || '');
                    });

                  const tryFlatpickr = () => {
                    for (const input of [...document.querySelectorAll('input')].filter(visible)) {
                      const fp = input._flatpickr || input.__flatpickr;
                      if (!fp || typeof fp.setDate !== 'function') continue;
                      const mode = fp.config && fp.config.mode || '';
                      fp.setDate(mode === 'range' ? [dataIso, dataIso] : dataIso, true, 'Y-m-d');
                      if (typeof fp.close === 'function') fp.close();
                      result.selected = true;
                      result.trusted = true;
                      result.method = 'flatpickr';
                      result.flatpickrMode = mode;
                      return true;
                    }
                    return false;
                  };

                  const dateMatches = text => {
                    const t = norm(text);
                    return t.includes(dataBr)
                      || t.includes(dataIso)
                      || (t.includes(day) && t.includes(yearText) && (t.includes(monthPt) || t.includes(monthEn)))
                      || t.includes(`${day} de ${monthPt} de ${yearText}`)
                      || t.includes(`${day} de ${monthPtAccent} de ${yearText}`);
                  };

                  const likelyCalendarNode = el => {
                    const host = el.closest('[role=dialog], [class*="calendar"], [class*="Calendar"], [class*="datepicker"], [class*="DatePicker"], [class*="picker"], [class*="Picker"], [class*="popover"], [class*="Popover"], [class*="modal"], [class*="Modal"]');
                    return !!host || /calendar|datepicker|picker|calendario|calendário/.test(norm(el.outerHTML || ''));
                  };

                  const findCalendarDateNode = () => {
                    const nodes = [...document.querySelectorAll('button,a,[role=button],[role=gridcell],td,div,span')]
                      .filter(e => visible(e) && e.getAttribute('aria-disabled') !== 'true' && !e.disabled);
                    let target = nodes.find(e => dateMatches([
                      e.getAttribute('aria-label'),
                      e.getAttribute('title'),
                      e.getAttribute('data-date'),
                      e.getAttribute('data-day'),
                      e.getAttribute('data-value'),
                      e.textContent,
                    ].join(' ')));
                    if (target) return target.closest('button,a,[role=button],[role=gridcell],td') || target;
                    const dayNodes = nodes.filter(e => norm(e.innerText || e.textContent || '') === day && likelyCalendarNode(e));
                    return dayNodes.find(e => !/fora|disabled|inativo|indisponivel|indisponível/.test(norm(e.className || e.getAttribute('aria-label') || ''))) || null;
                  };

                  const visibleButtonSnapshot = () => [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],label,span,div')]
                    .filter(visible)
                    .map(e => {
                      const rect = e.getBoundingClientRect();
                      return {
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        type: e.getAttribute('type') || '',
                        cls: String(e.className || '').slice(0, 160),
                        text: norm(e.innerText || e.textContent || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || '').slice(0, 160),
                        aria: norm(e.getAttribute('aria-label') || '').slice(0, 160),
                        title: norm(e.getAttribute('title') || '').slice(0, 160),
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .filter(item => item.text || item.aria || item.title || /calendar|date|picker|calend|day|month|year|mes|ano|dia/.test(norm(item.cls)))
                    .slice(0, 120);

                  const calendarLikeSnapshot = () => [...document.querySelectorAll('[role=dialog], [role=grid], [role=gridcell], [class*="calendar"], [class*="Calendar"], [class*="datepicker"], [class*="DatePicker"], [class*="picker"], [class*="Picker"], [class*="day"], [class*="Day"], [class*="month"], [class*="Month"]')]
                    .filter(e => !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length)))
                    .map(e => {
                      const rect = e.getBoundingClientRect();
                      return {
                        tag: e.tagName,
                        role: e.getAttribute('role') || '',
                        cls: String(e.className || '').slice(0, 220),
                        text: norm(e.innerText || e.textContent || e.getAttribute('aria-label') || '').slice(0, 300),
                        aria: norm(e.getAttribute('aria-label') || '').slice(0, 180),
                        title: norm(e.getAttribute('title') || '').slice(0, 180),
                        x: Math.round(rect.x),
                        y: Math.round(rect.y),
                        w: Math.round(rect.width),
                        h: Math.round(rect.height),
                      };
                    })
                    .slice(0, 120);

                  const findPreviousMonthButton = () => {
                    const nodes = [...document.querySelectorAll('button,a,[role=button],span,div')]
                      .filter(e => visible(e) && e.getAttribute('aria-disabled') !== 'true' && !e.disabled);
                    return nodes.find(e => {
                      const text = norm([
                        e.innerText,
                        e.textContent,
                        e.getAttribute('aria-label'),
                        e.getAttribute('title'),
                        e.className,
                      ].join(' '));
                      return /mes anterior|anterior|previous|prev|chevron_left|arrow_left|voltar/.test(text)
                        && !/proximo|próximo|next|right/.test(text);
                    }) || null;
                  };

                  const tryCalendarClick = async () => {
                    for (const input of plausibleDateInputs()) {
                      dispatchClick(input);
                      await delay(250);
                      const directAfterInput = findCalendarDateNode();
                      if (directAfterInput) break;
                    }
                    for (let attempt = 0; attempt < 14; attempt++) {
                      const target = findCalendarDateNode();
                      if (target) {
                        dispatchClick(target);
                        await delay(350);
                        const secondTarget = findCalendarDateNode();
                        if (secondTarget) {
                          dispatchClick(secondTarget);
                          await delay(250);
                        }
                        const apply = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                          .filter(visible)
                          .find(e => /^(aplicar|ok|confirmar|selecionar|concluir)$/.test(norm(e.innerText || e.value || e.getAttribute('aria-label') || '')));
                        if (apply) {
                          dispatchClick(apply);
                          await delay(250);
                        }
                        result.selected = true;
                        result.trusted = true;
                        result.method = 'calendar_click';
                        return true;
                      }
                      const prev = findPreviousMonthButton();
                      if (!prev) break;
                      dispatchClick(prev);
                      result.monthNavClicks += 1;
                      await delay(300);
                    }
                    return false;
                  };

                  const tryInputFallback = () => {
                    const inputs = plausibleDateInputs();
                    const values = [exactRangeValue, dataBr];
                    for (const input of inputs) {
                      const value = (input.type || '').toLowerCase() === 'date' ? dataIso : values.find(v => !input.maxLength || v.length <= input.maxLength) || dataBr;
                      setInputValue(input, value);
                      input.blur();
                      result.selected = true;
                      result.trusted = false;
                      result.method = 'input_fallback';
                      return true;
                    }
                    return false;
                  };

                  const forceExactRangeIfNeeded = () => {
                    const dataNorm = norm(dataBr);
                    for (const input of plausibleDateInputs()) {
                      const valueNorm = norm(input.value || '');
                      if (valueNorm.includes(exactRangeNorm)) return false;
                      if (!valueNorm.includes(dataNorm) && !/\d{2}\/\d{2}\/\d{4}.*\d{2}\/\d{2}\/\d{4}/.test(input.value || '')) continue;
                      setInputValue(input, exactRangeValue);
                      input.dispatchEvent(new KeyboardEvent('keydown', {bubbles: true, cancelable: true, key: 'Enter', code: 'Enter'}));
                      input.dispatchEvent(new KeyboardEvent('keyup', {bubbles: true, cancelable: true, key: 'Enter', code: 'Enter'}));
                      input.blur();
                      result.selected = true;
                      result.exactRangeForced = true;
                      result.exactRangeValue = exactRangeValue;
                      result.method = result.method ? `${result.method}_exact_range` : 'input_exact_range';
                      return true;
                    }
                    return false;
                  };

                  const exactRangeConfirmed = () => {
                    const allVisibleDateValues = plausibleDateInputs()
                      .map(input => input.value || '')
                      .filter(Boolean);
                    const sameDateOccurrences = allVisibleDateValues
                      .flatMap(value => [...value.matchAll(/\b[0-9]{2}[/][0-9]{2}[/][0-9]{4}\b/g)].map(match => match[0]))
                      .filter(value => value === dataBr)
                      .length;
                    if (sameDateOccurrences >= 2) return true;
                    for (const input of plausibleDateInputs()) {
                      const raw = input.value || '';
                      const valueNorm = norm(raw);
                      if (valueNorm.includes(exactRangeNorm)) return true;
                      const dates = [...raw.matchAll(/\b[0-9]{2}[/][0-9]{2}[/][0-9]{4}\b/g)].map(match => match[0]);
                      for (let index = 0; index < dates.length - 1; index += 1) {
                        if (dates[index] === dataBr && dates[index + 1] === dataBr) return true;
                      }
                    }
                    return false;
                  };

                  result.inputValuesBefore = inputSnapshot();
                  if (!tryFlatpickr()) {
                    if (!await tryCalendarClick()) {
                      tryInputFallback();
                    }
                  }
                  await delay(250);
                  forceExactRangeIfNeeded();
                  await delay(350);
                  result.inputValuesAfter = inputSnapshot();
                  result.exactRangeConfirmed = exactRangeConfirmed();
                  if (result.selected && !result.exactRangeConfirmed) {
                    result.trusted = false;
                    result.dateValidationFailed = true;
                  }
                  result.exportStateAfter = exportState();
                  result.visibleButtonsAfterCalendar = visibleButtonSnapshot();
                  result.visibleCalendarLikeNodes = calendarLikeSnapshot();
                  return result;
                })(__DATA_BR__, __DATA_ISO__)
                """.replace("__DATA_BR__", json.dumps(data_br)).replace("__DATA_ISO__", json.dumps(data_iso))
                result = await eval_js(session_id, script, timeout=20.0)
                return result if isinstance(result, dict) else {"selected": bool(result), "trusted": False, "method": "unknown"}

            async def dismiss_cielo_overlays(session_id: str, label: str = "") -> bool:
                try:
                    result = await eval_js(
                        session_id,
                        """
                        (() => {
                          const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').replace(/\\s+/g, ' ').trim().toLowerCase();
                          const visible = e => {
                            if (!e || e.closest('#pdfreader-cielo-manual-banner')) return false;
                            const rect = e.getBoundingClientRect();
                            const style = getComputedStyle(e);
                            return rect.width > 0 && rect.height > 0 && style.visibility !== 'hidden' && style.display !== 'none';
                          };
                          const clickable = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit],i,svg,[class*="close"],[class*="fechar"]')]
                            .filter(visible)
                            .map(e => ({e, text: norm(e.innerText || e.value || e.getAttribute('aria-label') || e.getAttribute('title') || e.getAttribute('name') || e.className || '')}));
                          const preferred = clickable.find(item => /nao exibir novamente|não exibir novamente/.test(item.text))
                            || clickable.find(item => /fechar|close|dismiss|pular|agora nao|agora não/.test(item.text));
                          if (!preferred) return {clicked: false};
                          preferred.e.scrollIntoView({block: 'center'});
                          preferred.e.dispatchEvent(new MouseEvent('mousedown', {bubbles: true, cancelable: true, view: window}));
                          preferred.e.dispatchEvent(new MouseEvent('mouseup', {bubbles: true, cancelable: true, view: window}));
                          preferred.e.click();
                          return {clicked: true, text: preferred.text.slice(0, 120)};
                        })()
                        """,
                        timeout=10.0,
                    )
                    clicked = bool(isinstance(result, dict) and result.get("clicked"))
                    if clicked:
                        cielo_log("cielo_overlay_dismissed", label=label, result=result)
                        await asyncio.sleep(1.0)
                    return clicked
                except Exception as exc:
                    cielo_log("cielo_overlay_dismiss_failed", label=label, error=str(exc)[:300], error_type=type(exc).__name__)
                    return False

            async def try_export_current_area(session_id: str) -> str | None:
                nonlocal last_cielo_export_state
                same_day = data_br == datetime.now().strftime("%d/%m/%Y")
                try:
                    export_start_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                except Exception:
                    export_start_url = ""
                last_cielo_export_state = {"current_url": export_start_url, "same_day": same_day}
                cielo_log("export_area_start", current_url=export_start_url, same_day=same_day, data_br=data_br)
                date_set_result = (
                    {"selected": True, "trusted": True, "method": "same_day_detail_tab"}
                    if same_day
                    else {"selected": False, "trusted": False, "method": "detail_tab_before_historical_filter"}
                )
                cielo_log("export_date_filter_select", result=date_set_result)
                if same_day:
                    cielo_log("export_same_day_filter_skipped", action="click_detail_tab_then_export")
                else:
                    cielo_log("export_historical_filter_deferred", action="click_detail_tab_before_filter")
                await asyncio.sleep(1.0)
                try:
                    after_filter_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                except Exception:
                    after_filter_url = ""
                cielo_log("export_before_detail_tab", current_url=after_filter_url)
                detail_result = await click_cielo_sales_detail_tab(session_id)
                cielo_log("export_detail_tab_click", result=detail_result)
                detail_clicked = bool(detail_result.get("clicked")) if isinstance(detail_result, dict) else bool(detail_result)
                detail_target_text = detail_result.get("targetText") if isinstance(detail_result, dict) else None
                detail_direct_navigation = False
                last_cielo_export_state["detailClicked"] = detail_clicked
                if isinstance(detail_result, dict):
                    last_cielo_export_state["detailTargetText"] = detail_target_text
                if detail_clicked:
                    await asyncio.sleep(4.0)
                    try:
                        after_detail_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    except Exception:
                        after_detail_url = ""
                    cielo_log("export_detail_tab_after_wait", current_url=after_detail_url)
                    if after_detail_url:
                        after_filter_url = after_detail_url
                if not detail_clicked:
                    detail_url = (
                        "https://minhaconta2.cielo.com.br/site/vendas/detalhado/cielo"
                        if same_day
                        else "https://minhaconta2.cielo.com.br/site/vendas/detalhado/cielo#historic"
                    )
                    cielo_log("export_detail_tab_not_clicked", action="navigate_direct_detail", current_url=after_filter_url, detail_url=detail_url)
                    try:
                        await cdp("Page.navigate", {"url": detail_url}, session_id=session_id, timeout=15.0)
                        await asyncio.sleep(6.0)
                        after_direct_detail_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    except Exception as exc:
                        after_direct_detail_url = ""
                        cielo_log("export_detail_direct_navigation_error", error=str(exc)[:300], error_type=type(exc).__name__)
                    cielo_log("export_detail_direct_navigation_after_wait", current_url=after_direct_detail_url)
                    if after_direct_detail_url:
                        detail_direct_navigation = True
                        after_filter_url = after_direct_detail_url
                if not same_day and "/vendas/detalhado" not in str(after_filter_url or ""):
                    detail_url = "https://minhaconta2.cielo.com.br/site/vendas/detalhado/cielo#historic"
                    cielo_log("export_detail_not_reached", current_url=after_filter_url, action="navigate_direct", detail_clicked=detail_clicked)
                    try:
                        await cdp("Page.navigate", {"url": detail_url}, session_id=session_id, timeout=15.0)
                        await asyncio.sleep(8.0)
                        after_direct_detail_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                    except Exception as exc:
                        after_direct_detail_url = ""
                        cielo_log("export_detail_direct_navigation_error", error=str(exc)[:300], error_type=type(exc).__name__)
                    cielo_log("export_detail_direct_navigation_after_wait", current_url=after_direct_detail_url)
                    if "/vendas/detalhado" in after_direct_detail_url:
                        detail_direct_navigation = True
                        after_filter_url = after_direct_detail_url
                    else:
                        last_cielo_export_state = {
                            "current_url": after_direct_detail_url or after_filter_url,
                            "same_day": same_day,
                            "detailClicked": detail_clicked,
                            "detailTargetText": detail_target_text,
                            "detailRequiredFailed": True,
                            "dateSelectionMethod": date_set_result.get("method") if isinstance(date_set_result, dict) else None,
                            "dateSelectionTrusted": bool(
                                same_day
                                or (
                                    isinstance(date_set_result, dict)
                                    and date_set_result.get("trusted")
                                    and date_set_result.get("selected")
                                )
                            ),
                        }
                        cielo_log("export_detail_required_failed", state=last_cielo_export_state)
                        return None
                if not same_day:
                    try:
                        more_filters_detail = await click_by_text(session_id, ("filtrar mais", "mais filtros"), timeout=5.0)
                        cielo_log("export_detail_filter_more_clicked", clicked=more_filters_detail)
                        await asyncio.sleep(0.8)
                        sale_date_detail = await click_by_text(session_id, ("data da venda", "data de venda"), timeout=5.0)
                        cielo_log("export_detail_filter_sale_date_clicked", clicked=sale_date_detail)
                        await asyncio.sleep(0.8)
                        historic_detail = await click_by_text(session_id, ("historico",), timeout=5.0)
                        cielo_log("export_detail_filter_historic_clicked", clicked=historic_detail)
                        await asyncio.sleep(0.8)
                        date_set_result = await select_cielo_historical_sale_date(session_id)
                        cielo_log("export_detail_date_filter_select", result=date_set_result)
                        if not (
                            isinstance(date_set_result, dict)
                            and date_set_result.get("selected")
                            and date_set_result.get("trusted")
                            and date_set_result.get("exactRangeConfirmed")
                        ):
                            last_cielo_export_state = {
                                "current_url": after_filter_url,
                                "same_day": same_day,
                                "dateSelectionFailed": True,
                                "dateSelectionMethod": date_set_result.get("method") if isinstance(date_set_result, dict) else None,
                                "dateSelectionTrusted": bool(date_set_result.get("trusted")) if isinstance(date_set_result, dict) else False,
                                "dateSelectionExactRangeConfirmed": bool(date_set_result.get("exactRangeConfirmed")) if isinstance(date_set_result, dict) else False,
                                "dateSelectionInputValuesAfter": date_set_result.get("inputValuesAfter") if isinstance(date_set_result, dict) else None,
                            }
                            cielo_log("export_detail_date_filter_failed", state=last_cielo_export_state)
                            return None
                        detail_filter_apply = await click_cielo_filter_apply(session_id)
                        cielo_log("export_detail_filter_apply_clicked", result=detail_filter_apply)
                        await asyncio.sleep(5.0)
                        after_filter_url = str(await eval_js(session_id, "location.href", timeout=10.0) or after_filter_url)
                        cielo_log("export_detail_filter_after_wait", current_url=after_filter_url)
                    except Exception as exc:
                        cielo_log("export_detail_filter_error", error=str(exc)[:300], error_type=type(exc).__name__)
                started_at = time.time() - 1.0
                export_state = await eval_js(
                        session_id,
                        """
                        (() => {
                          const visibleAny = e => !!(e && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\\u0300-\\u036f]/g, '').toLowerCase();
                          const bodyText = norm(document.body && document.body.innerText || '');
                          const all = [...document.querySelectorAll('body *')].filter(visibleAny);
                          const titlePattern = /consolidado de vendas|detalhado de vendas|detalhamento de vendas|vendas detalhadas|historico de vendas|histórico de vendas|detalhes da venda|detalhe da venda|consolidado/;
                          const title = all.find(e => {
                            const text = norm(e.innerText || e.textContent || '');
                            return text.length <= 180 && titlePattern.test(text);
                          });
                          const titleY = title ? title.getBoundingClientRect().top : -Infinity;
                          const exportCandidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                            .filter(visibleAny)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                            .filter(([e, text]) => /exportar|baixar|download|excel|xlsx|csv/.test(text));
                          const target = exportCandidates.find(([e]) => {
                            const y = e.getBoundingClientRect().top;
                            return title && y >= titleY - 40 && y <= titleY + 700;
                          }) || exportCandidates[0];
                          return {
                            available: !!(target && !target[0].disabled && target[0].getAttribute('aria-disabled') !== 'true'),
                            candidatesCount: exportCandidates.length,
                            hasConsolidadoTitle: !!title,
                            titleText: title ? norm(title.innerText || title.textContent || '').slice(0, 180) : '',
                            targetText: target ? target[1] : '',
                            targetDisabled: target ? !!target[0].disabled : null,
                            targetAriaDisabled: target ? target[0].getAttribute('aria-disabled') : null,
                            noResultsVisible: /nenhum resultado|sem resultado|nao encontramos|não encontramos|nenhuma venda/.test(bodyText)
                          };
                        })()
                        """,
                        timeout=10.0,
                    )
                export_state = export_state if isinstance(export_state, dict) else {}
                last_cielo_export_state = dict(export_state)
                last_cielo_export_state["current_url"] = after_filter_url
                last_cielo_export_state["same_day"] = same_day
                last_cielo_export_state["detailClicked"] = detail_clicked
                last_cielo_export_state["detailTargetText"] = detail_target_text
                last_cielo_export_state["detailDirectNavigation"] = detail_direct_navigation
                last_cielo_export_state["detailRequiredFailed"] = (
                    not same_day and "/vendas/detalhado" not in str(after_filter_url or "")
                )
                last_cielo_export_state["dateSelectionMethod"] = date_set_result.get("method") if isinstance(date_set_result, dict) else None
                last_cielo_export_state["dateSelectionTrusted"] = bool(
                    same_day
                    or (
                        isinstance(date_set_result, dict)
                        and date_set_result.get("trusted")
                        and date_set_result.get("selected")
                    )
                )
                export_available = bool(export_state.get("available"))
                cielo_log("export_button_state", state=export_state)
                if not export_available:
                    cielo_log(
                        "export_unavailable_after_filter",
                        reason="export_button_disabled_or_missing",
                        terminal_no_result=_cielo_export_state_is_terminal_no_result(),
                    )
                    return None
                clicked = bool(
                    await eval_js(
                        session_id,
                        """
                        (() => {
                          const visible = e => !!(e && !e.disabled && (e.offsetWidth || e.offsetHeight || e.getClientRects().length));
                          const norm = s => (s || '').normalize('NFD').replace(/[\u0300-\u036f]/g, '').toLowerCase();
                          const all = [...document.querySelectorAll('body *')].filter(visible);
                          const titlePattern = /consolidado de vendas|detalhado de vendas|detalhamento de vendas|vendas detalhadas|historico de vendas|histórico de vendas|detalhes da venda|detalhe da venda|consolidado/;
                          const title = all.find(e => {
                            const text = norm(e.innerText || e.textContent || '');
                            return text.length <= 180 && titlePattern.test(text);
                          });
                          const titleY = title ? title.getBoundingClientRect().top : -Infinity;
                          const exportCandidates = [...document.querySelectorAll('button,a,[role=button],input[type=button],input[type=submit]')]
                            .filter(visible)
                            .map(e => [e, norm(e.innerText || e.value || e.getAttribute('aria-label') || '')])
                            .filter(([e, text]) => /exportar|baixar|download|excel|xlsx|csv/.test(text));
                          const scoped = exportCandidates.find(([e]) => {
                            const y = e.getBoundingClientRect().top;
                            return title && y >= titleY - 40 && y <= titleY + 700;
                          });
                          const target = scoped || exportCandidates[0];
                          if (!target) return false;
                          target[0].scrollIntoView({block: 'center'});
                          target[0].click();
                          return true;
                        })()
                        """,
                        timeout=10.0,
                    )
                )
                cielo_log("export_button_click_primary", clicked=clicked)
                if not clicked:
                    clicked = await click_by_text(session_id, ("exportar", "baixar", "download", "excel", "xlsx", "csv"), timeout=10.0)
                    cielo_log("export_button_click_text_fallback", clicked=clicked)
                if not clicked:
                    clicked = await click_submit(session_id)
                    cielo_log("export_button_click_submit_fallback", clicked=clicked)
                last_cielo_export_state["exportClicked"] = bool(clicked)
                await asyncio.sleep(1.5)
                format_result = await click_cielo_export_format(session_id)
                cielo_log("export_format_click", result=format_result)
                last_cielo_export_state["formatClicked"] = bool(format_result.get("clicked")) if isinstance(format_result, dict) else bool(format_result)
                await asyncio.sleep(1.0)
                confirm_result = await click_cielo_export_confirm(session_id, require_overlay=True)
                cielo_log("export_confirm_click_after_format", result=confirm_result)
                last_cielo_export_state["confirmClicked"] = bool(confirm_result.get("clicked")) if isinstance(confirm_result, dict) else bool(confirm_result)
                await asyncio.sleep(1.5)
                for confirm_attempt in range(1, 4):
                    followup_result = await click_cielo_export_confirm(session_id, require_overlay=True)
                    cielo_log("export_confirm_click_followup", attempt=confirm_attempt, result=followup_result)
                    if not bool(followup_result.get("clicked")):
                        break
                    last_cielo_export_state["confirmClicked"] = True
                    last_cielo_export_state["confirmFollowupClicks"] = confirm_attempt
                    await asyncio.sleep(1.5)
                downloaded = await asyncio.to_thread(_wait_for_cielo_downloaded_report, browser_download_dir, data_br, started_at, 5.0, True)
                cielo_log("export_download_wait_direct_result", downloaded=downloaded, files=_cielo_download_snapshot(started_at))
                if not downloaded:
                    downloaded = await download_cielo_generated_report_from_reports_area(session_id, started_at)
                cielo_log("export_download_wait_result", downloaded=downloaded, files=_cielo_download_snapshot(started_at))
                if not downloaded:
                    last_cielo_export_state["downloadTimedOut"] = True
                return downloaded

            try:
                targets = (await cdp("Target.getTargets")).get("targetInfos") or []
                target = next((t for t in targets if t.get("type") == "page"), targets[0] if targets else None)
                if not target:
                    raise RuntimeError("Não foi possível abrir uma aba da Cielo.")
                cielo_log("target_selected", target_id=target.get("targetId"), target_url=target.get("url"), target_title=target.get("title"))
                session_id = (await cdp("Target.attachToTarget", {"targetId": target["targetId"], "flatten": True})).get("sessionId")
                if not session_id:
                    raise RuntimeError("Não foi possível anexar a aba da Cielo.")
                cielo_log("target_attached", session_id_present=bool(session_id))
                await cdp("Page.enable", session_id=session_id)
                await cdp("Runtime.enable", session_id=session_id)
                try:
                    await cdp("Page.bringToFront", session_id=session_id, timeout=5.0)
                except Exception:
                    pass
                try:
                    await cdp("Browser.setDownloadBehavior", {"behavior": "allow", "downloadPath": browser_download_dir, "eventsEnabled": True})
                    await cdp("Page.setDownloadBehavior", {"behavior": "allow", "downloadPath": browser_download_dir}, session_id=session_id)
                except Exception:
                    pass

                await asyncio.sleep(4.0)
                await authenticate(session_id)
                await hide_cielo_banner(session_id)
                await dismiss_cielo_overlays(session_id, "after_auth")
                _emit_pix_status(on_status, "Abrindo Minhas Vendas na Cielo...")
                cielo_sales_summary_url = "https://minhaconta2.cielo.com.br/site/vendas/resumo/cielo"
                cielo_log("navigate_sales_summary", url=cielo_sales_summary_url)
                await cdp("Page.navigate", {"url": cielo_sales_summary_url}, session_id=session_id, timeout=10.0)
                await asyncio.sleep(8.0)
                await dismiss_cielo_overlays(session_id, "after_sales_navigate")
                current_url_after_sales = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                cielo_log("sales_summary_after_navigate", current_url=current_url_after_sales)
                if "acessos/login" in current_url_after_sales:
                    cielo_log("sales_summary_redirected_to_login", current_url=current_url_after_sales, action="stop_without_reauth")
                    return {
                        "cartoes": None,
                        "avisos": [
                            "A Cielo autenticou, mas voltou para a tela de login ao abrir Minhas Vendas. O app interrompeu o fallback para evitar reentradas repetidas no login."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }
                _emit_pix_status(on_status, "Exportando Detalhado de Vendas da Cielo...")

                found = await try_export_current_area(session_id)
                if found:
                    persisted = _persist_cielo_auto_report(found, data_br)
                    cielo_log("export_found_initial_area", downloaded=found, persisted=persisted)
                    return {"cartoes": persisted, "avisos": [], "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None}
                if not bool(last_cielo_export_state.get("dateSelectionTrusted")):
                    cielo_log("export_stop_after_untrusted_date_selection", state=last_cielo_export_state)
                    return {
                        "cartoes": None,
                        "avisos": [
                            "A Cielo foi acessada, mas o app não conseguiu confirmar a seleção da data no calendário histórico."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }
                if bool(last_cielo_export_state.get("detailRequiredFailed")):
                    cielo_log("export_stop_after_detail_required_failed", state=last_cielo_export_state)
                    return {
                        "cartoes": None,
                        "avisos": [
                                "A Cielo foi acessada, mas o app não conseguiu abrir a tela detalhada do dia antes de exportar. O resumo consolidado foi ignorado."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }
                if _cielo_export_state_is_terminal_no_result():
                    cielo_log("export_stop_after_no_results_initial_area", state=last_cielo_export_state)
                    return {
                        "cartoes": None,
                        "avisos": [
                            "A Cielo foi acessada e o Consolidado de Vendas não retornou vendas exportáveis para a data filtrada."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }
                if bool(last_cielo_export_state.get("downloadTimedOut")):
                    cielo_log("export_stop_after_download_timeout_initial_area", state=last_cielo_export_state)
                    return {
                        "cartoes": None,
                        "avisos": [
                            "A Cielo habilitou o Exportar e o app clicou no fluxo de exportacao, mas nenhum arquivo de relatorio apareceu nos downloads."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }
                if bool(last_cielo_export_state.get("hasConsolidadoTitle")):
                    cielo_log("export_stop_after_initial_consolidado_unavailable", state=last_cielo_export_state)
                    return {
                        "cartoes": None,
                        "avisos": [
                            "A Cielo foi acessada, mas o botao Exportar do Consolidado de Vendas continuou bloqueado apos o filtro da data."
                        ],
                        "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                    }

                cielo_log("export_not_found_after_primary_flow", state=last_cielo_export_state)
                return {
                    "cartoes": None,
                    "avisos": ["A Cielo foi acessada, mas o app não conseguiu exportar automaticamente o relatório detalhado de cartões."],
                    "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                }

                candidate_urls = [
                    "https://minhaconta2.cielo.com.br/site/vendas/resumo/cielo",
                    "https://minhaconta2.cielo.com.br/site/vendas",
                    "https://minhaconta2.cielo.com.br/site/extrato",
                    "https://minhaconta2.cielo.com.br/site/relatorios",
                    "https://minhaconta2.cielo.com.br/site/relatorios/vendas",
                ]
                for url in candidate_urls:
                    _check_cancelled()
                    try:
                        cielo_log("candidate_navigate_start", url=url)
                        await cdp("Page.navigate", {"url": url}, session_id=session_id, timeout=10.0)
                        await asyncio.sleep(6.0)
                        text_norm = _normalize_ascii_text(await visible_text(session_id))
                        candidate_current_url = str(await eval_js(session_id, "location.href", timeout=10.0) or "")
                        cielo_log(
                            "candidate_navigate_result",
                            requested_url=url,
                            current_url=candidate_current_url,
                            has_sales_terms=any(marker in text_norm for marker in ("venda", "relatorio", "extrato", "transacao")),
                        )
                        if "acessos/login" in candidate_current_url:
                            cielo_log("candidate_redirected_to_login", requested_url=url, current_url=candidate_current_url, action="reauthenticate")
                            await authenticate(session_id)
                        if not any(marker in text_norm for marker in ("venda", "relatorio", "extrato", "transacao")):
                            continue
                        found = await try_export_current_area(session_id)
                        if found:
                            persisted = _persist_cielo_auto_report(found, data_br)
                            cielo_log("export_found_candidate_area", requested_url=url, downloaded=found, persisted=persisted)
                            return {"cartoes": persisted, "avisos": [], "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None}
                        if _cielo_export_state_is_terminal_no_result():
                            cielo_log("export_stop_after_no_results_candidate_area", requested_url=url, state=last_cielo_export_state)
                            return {
                                "cartoes": None,
                                "avisos": [
                                    "A Cielo foi acessada e o Consolidado de Vendas não retornou vendas exportáveis para a data filtrada."
                                ],
                                "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                            }
                    except Exception as exc:
                        cielo_log("candidate_navigate_error", requested_url=url, error=str(exc), error_type=type(exc).__name__)
                        continue

                cielo_log("fallback_click_menu_start")
                await click_by_text(session_id, ("vendas", "relatorios", "relatórios", "extrato", "transacoes", "transações"), timeout=8.0)
                await asyncio.sleep(5.0)
                found = await try_export_current_area(session_id)
                if found:
                    persisted = _persist_cielo_auto_report(found, data_br)
                    cielo_log("export_found_fallback_menu", downloaded=found, persisted=persisted)
                    return {"cartoes": persisted, "avisos": [], "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None}
                cielo_log("export_not_found")
                return {
                    "cartoes": None,
                    "avisos": ["A Cielo foi acessada, mas o app não conseguiu localizar/exportar automaticamente o relatório de cartões."],
                    "debug_log": str(cielo_debug_log_path) if cielo_debug_log_path else None,
                }
            finally:
                recv_task.cancel()
                try:
                    await recv_task
                except BaseException:
                    pass

    _emit_pix_status(on_status, "Abrindo portal da Cielo...")
    cielo_log("browser_launch", command=os.path.basename(str(navegador)), port=port)
    proc = _launch_browser_process(chrome_args)
    try:
        result = asyncio.run(asyncio.wait_for(_run(), timeout=900.0))
        if isinstance(result, dict) and cielo_debug_log_path:
            result.setdefault("debug_log", str(cielo_debug_log_path))
        cielo_log("run_success", result={k: v for k, v in (result or {}).items() if k != "cartoes"})
        return result
    except Exception as exc:
        cielo_log("run_error", error=str(exc), error_type=type(exc).__name__)
        if str(exc).strip() == "__cancelled__":
            raise
        raise RuntimeError(str(exc)) from exc
    finally:
        cielo_log("browser_cleanup_start")
        try:
            proc.terminate()
            proc.wait(timeout=5)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass
        shutil.rmtree(profile_dir, ignore_errors=True)
        shutil.rmtree(browser_download_dir, ignore_errors=True)
        cielo_log("browser_cleanup_done")


def _build_pix_report_from_caixa_pdf(caminho_pdf: str, data_br: str) -> dict:
    text = _read_pdf_text(caminho_pdf)
    itens = []
    itens_todos = []
    for raw in text.splitlines():
        line = " ".join(str(raw or "").split())
        match = re.match(
            r"^(\d{2}/\d{2}/\d{4})\s+(\d{2}:\d{2}:\d{2})\s+(RECEBIDO|ENVIADO)\s+([A-ZÇÃÕÁÉÍÓÚ]+)(?:\s+(.*?))?\s+R\$\s*([-\d\.,]+)$",
            line,
            re.IGNORECASE,
        )
        if not match:
            continue
        data_venda, hora_venda, tipo, situacao, nome, valor_str = match.groups()
        if data_venda != data_br:
            continue
        item = {
            "data_venda": f"{data_venda} às {hora_venda}",
            "ordem": datetime.strptime(f"{data_venda} {hora_venda}", "%d/%m/%Y %H:%M:%S").strftime("%Y-%m-%d %H:%M:%S"),
            "tipo_pix": str(tipo).upper(),
            "situacao": str(situacao).upper(),
            "nome": str(nome or "").strip(),
            "valor_bruto": round(parse_number(valor_str), 2),
        }
        itens_todos.append(item)
        if item["tipo_pix"] == "RECEBIDO" and item["situacao"] == "EFETIVADO":
            itens.append(
                {
                    "data_venda": item["data_venda"],
                    "ordem": item["ordem"],
                    "tipo_pix": item["tipo_pix"],
                    "situacao": item["situacao"],
                    "nome": item["nome"],
                    "valor_bruto": item["valor_bruto"],
                }
            )

    itens.sort(key=lambda item: item.get("ordem", ""))
    total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
    periodo = f"{data_br} - {data_br}"
    return {
        "arquivo": os.path.basename(caminho_pdf),
        "caminho": caminho_pdf,
        "periodo": periodo,
        "quantidade_autorizados": len(itens),
        "total_autorizado": total,
        "itens_autorizados": itens,
        "quantidade_relatorio": len(itens),
        "total_relatorio": total,
        "consistente": True,
        "origem": "caixa_pix_pdf",
        "mensagem": None if itens else "Nenhuma transação PIX recebida encontrada no relatório local para este dia.",
        "itens_todos": itens_todos,
        "tab_title": "PIX",
        "menu_text": "Abrir PIX CAIXA",
        "summary_label": "PIX",
        "total_label": "Total PIX CAIXA",
        "section_label": "Transações PIX recebidas na CAIXA",
        "empty_message": "Nenhuma transação PIX recebida encontrada para este dia.",
        "table_headers": ("Data da venda", "Valor bruto"),
        "table_mode": "data_valor",
        "categoria": "pix_caixa",
    }


def _build_pix_report_from_caixa_csv(caminho_csv: str, data_br: str) -> dict:
    text = _read_text_file(caminho_csv)
    itens = []
    itens_todos = []
    reader = csv.DictReader(text.splitlines(), delimiter=";")
    for row in reader:
        normalized_row = {_normalize_ascii_text(key): str(value or "").strip() for key, value in row.items()}
        data_raw = normalized_row.get("data da venda", "")
        valor_raw = normalized_row.get("valor bruto", "")
        situacao_raw = str(normalized_row.get("status", "")).upper()
        codigo_raw = normalized_row.get("cod. de autorizacao", "")
        if not data_raw or not valor_raw:
            continue
        match = re.match(
            r"^(\d{2}/\d{2}/\d{4})\s+(?:as|às)\s+(\d{2}:\d{2})(?::(\d{2}))?$",
            _normalize_ascii_text(data_raw),
        )
        if not match:
            continue
        data_venda = match.group(1)
        if data_venda != data_br:
            continue
        hora = f"{match.group(2)}:{match.group(3) or '00'}"
        item = {
            "data_venda": f"{data_venda} às {hora[:5]}",
            "ordem": datetime.strptime(f"{data_venda} {hora}", "%d/%m/%Y %H:%M:%S").strftime("%Y-%m-%d %H:%M:%S"),
            "tipo_pix": "RECEBIDO",
            "situacao": situacao_raw,
            "nome": str(codigo_raw or "").strip(),
            "valor_bruto": round(parse_number(valor_raw), 2),
        }
        itens_todos.append(item)
        if _normalize_ascii_text(item["situacao"]) in {
            _normalize_ascii_text("APROVADA"),
            _normalize_ascii_text("AUTORIZADA"),
            _normalize_ascii_text("EFETIVADO"),
        }:
            itens.append(
                {
                    "data_venda": item["data_venda"],
                    "ordem": item["ordem"],
                    "tipo_pix": item["tipo_pix"],
                    "situacao": item["situacao"],
                    "nome": item["nome"],
                    "valor_bruto": item["valor_bruto"],
                }
            )

    itens.sort(key=lambda item: item.get("ordem", ""))
    total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
    periodo = f"{data_br} - {data_br}"
    return {
        "arquivo": os.path.basename(caminho_csv),
        "caminho": caminho_csv,
        "periodo": periodo,
        "quantidade_autorizados": len(itens),
        "total_autorizado": total,
        "itens_autorizados": itens,
        "quantidade_relatorio": len(itens),
        "total_relatorio": total,
        "consistente": True,
        "origem": "caixa_pix_csv",
        "mensagem": None if itens else "Nenhuma transação PIX recebida encontrada no relatório local para este dia.",
        "itens_todos": itens_todos,
        "tab_title": "PIX",
        "menu_text": "Abrir PIX CAIXA",
        "summary_label": "PIX",
        "total_label": "Total PIX CAIXA",
        "section_label": "Transações PIX recebidas na CAIXA",
        "empty_message": "Nenhuma transação PIX recebida encontrada para este dia.",
        "table_headers": ("Data da venda", "Valor bruto"),
        "table_mode": "data_valor",
        "categoria": "pix_caixa",
    }


def _build_pix_report_from_caixa_xlsx(caminho_xlsx: str, data_br: str) -> dict:
    itens = []
    itens_todos = []
    for row in _collect_card_rows_from_caixa_xlsx(caminho_xlsx):
        normalized_row = {_normalize_ascii_text(key): str(value or "").strip() for key, value in row.items()}
        data_raw = normalized_row.get("data da venda", "")
        valor_raw = normalized_row.get("valor bruto", "")
        situacao_raw = str(normalized_row.get("status", "")).upper()
        codigo_raw = normalized_row.get("cod. de autorizacao", "")
        if not data_raw or not valor_raw:
            continue
        match = re.match(
            r"^(\d{2}/\d{2}/\d{4})\s+(?:as|às)\s+(\d{2}:\d{2})(?::(\d{2}))?$",
            _normalize_ascii_text(data_raw),
        )
        if not match:
            continue
        data_venda = match.group(1)
        if data_venda != data_br:
            continue
        hora = f"{match.group(2)}:{match.group(3) or '00'}"
        item = {
            "data_venda": f"{data_venda} às {hora[:5]}",
            "ordem": datetime.strptime(f"{data_venda} {hora}", "%d/%m/%Y %H:%M:%S").strftime("%Y-%m-%d %H:%M:%S"),
            "tipo_pix": "RECEBIDO",
            "situacao": situacao_raw,
            "nome": str(codigo_raw or "").strip(),
            "valor_bruto": round(parse_number(valor_raw), 2),
        }
        itens_todos.append(item)
        if _normalize_ascii_text(item["situacao"]) in {
            _normalize_ascii_text("APROVADA"),
            _normalize_ascii_text("AUTORIZADA"),
            _normalize_ascii_text("EFETIVADO"),
        }:
            itens.append(
                {
                    "data_venda": item["data_venda"],
                    "ordem": item["ordem"],
                    "tipo_pix": item["tipo_pix"],
                    "situacao": item["situacao"],
                    "nome": item["nome"],
                    "valor_bruto": item["valor_bruto"],
                }
            )

    itens.sort(key=lambda item: item.get("ordem", ""))
    total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
    periodo = f"{data_br} - {data_br}"
    return {
        "arquivo": os.path.basename(caminho_xlsx),
        "caminho": caminho_xlsx,
        "periodo": periodo,
        "quantidade_autorizados": len(itens),
        "total_autorizado": total,
        "itens_autorizados": itens,
        "quantidade_relatorio": len(itens),
        "total_relatorio": total,
        "consistente": True,
        "origem": "caixa_pix_xlsx",
        "mensagem": None if itens else "Nenhuma transação PIX recebida encontrada no relatório local para este dia.",
        "itens_todos": itens_todos,
        "tab_title": "PIX",
        "menu_text": "Abrir PIX CAIXA",
        "summary_label": "PIX",
        "total_label": "Total PIX CAIXA",
        "section_label": "Transações PIX recebidas na CAIXA",
        "empty_message": "Nenhuma transação PIX recebida encontrada para este dia.",
        "table_headers": ("Data da venda", "Valor bruto"),
        "table_mode": "data_valor",
        "categoria": "pix_caixa",
    }


def _convert_pix_xlsx_to_csv(caminho_xlsx: str) -> str | None:
    try:
        rows = _collect_card_rows_from_caixa_xlsx(caminho_xlsx)
    except Exception:
        return None
    if not rows:
        return None
    csv_path = str(Path(caminho_xlsx).with_suffix(".csv"))
    ordered_headers = [
        "Data da venda",
        "Cód. de autorização",
        "Valor bruto",
        "Terminal",
        "Número do estabelecimento",
        "Status",
    ]
    try:
        with open(csv_path, "w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=ordered_headers, delimiter=";")
            writer.writeheader()
            for row in rows:
                writer.writerow({header: str(row.get(header, "") or "").strip() for header in ordered_headers})
        return csv_path
    except Exception:
        return None


def _build_card_reports_from_caixa_pdf(caminho_pdf: str, data_br: str) -> dict[str, dict]:
    text = _read_pdf_text(caminho_pdf)
    buckets = {
        "cartao_credito_caixa": [],
        "cartao_debito_caixa": [],
    }

    for raw in text.splitlines():
        line = " ".join(str(raw or "").split())
        if "Aprovada" not in line and "Cancelada" not in line:
            continue
        tokens = line.split(" ")
        if len(tokens) < 17 or not re.match(r"^\d{2}/\d{2}/\d{4}$", tokens[0]):
            continue

        data_venda = tokens[0]
        if data_venda != data_br or tokens[-1] != "Aprovada":
            continue

        meio = " ".join(tokens[5:-9])
        meio_normalizado = _normalize_ascii_text(meio)
        if "debito" in meio_normalizado:
            key = "cartao_debito_caixa"
        elif "credito" in meio_normalizado or "parcelado" in meio_normalizado:
            key = "cartao_credito_caixa"
        else:
            continue

        buckets[key].append(
            {
                "numero": tokens[4],
                "numero_exibicao": tokens[4].lstrip("0") or tokens[4],
                "data_venda": f"{data_venda} às {tokens[2]}",
                "valor_bruto": round(parse_number(tokens[-6]), 2),
            }
        )

    reports: dict[str, dict] = {}
    periodo = f"{data_br} - {data_br}"
    meta_by_key = {
        "cartao_credito_caixa": {
            "tab_title": "Cartão de Crédito CAIXA",
            "menu_text": "Abrir cartão de crédito CAIXA",
            "summary_label": "Cartão de crédito CAIXA",
            "total_label": "Total cartão de crédito CAIXA",
            "section_label": "Transações em cartão de crédito na CAIXA",
            "empty_message": "Nenhuma transação em cartão de crédito da CAIXA encontrada para este dia.",
        },
        "cartao_debito_caixa": {
            "tab_title": "Cartão de Débito CAIXA",
            "menu_text": "Abrir cartão de débito CAIXA",
            "summary_label": "Cartão de débito CAIXA",
            "total_label": "Total cartão de débito CAIXA",
            "section_label": "Transações em cartão de débito na CAIXA",
            "empty_message": "Nenhuma transação em cartão de débito da CAIXA encontrada para este dia.",
        },
    }

    for key, itens in buckets.items():
        itens.sort(key=lambda item: (item.get("data_venda", ""), item.get("numero", "")))
        total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
        meta = meta_by_key[key]
        reports[key] = {
            "arquivo": os.path.basename(caminho_pdf),
            "caminho": caminho_pdf,
            "periodo": periodo,
            "quantidade_autorizados": len(itens),
            "total_autorizado": total,
            "itens_autorizados": itens,
            "quantidade_relatorio": len(itens),
            "total_relatorio": total,
            "consistente": True,
            "origem": "caixa_cartoes_pdf",
            "mensagem": None if itens else meta["empty_message"],
            "categoria": key,
            "tab_title": meta["tab_title"],
            "menu_text": meta["menu_text"],
            "summary_label": meta["summary_label"],
            "total_label": meta["total_label"],
            "section_label": meta["section_label"],
            "empty_message": meta["empty_message"],
            "table_headers": ("Comprovante", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }

    return reports


def _collect_card_rows_from_caixa_xlsx(caminho_xlsx: str) -> list[dict[str, str]]:
    import pandas as pd

    def _rows_from_tabular_text(text: str) -> list[dict[str, str]]:
        parsed_rows: list[list[str]] = []
        if "<table" in str(text or "").lower():
            try:
                from bs4 import BeautifulSoup

                soup = BeautifulSoup(text, "html.parser")
                for tr in soup.select("tr"):
                    cells = [
                        " ".join(cell.get_text(" ", strip=True).split())
                        for cell in tr.find_all(["th", "td"])
                    ]
                    if any(cells):
                        parsed_rows.append(cells)
            except Exception:
                parsed_rows = []
        if not parsed_rows:
            for delimiter in (";", "\t", ","):
                candidate_rows = []
                for line in str(text or "").splitlines():
                    if not line.strip():
                        continue
                    candidate_rows.append([cell.strip().strip('"') for cell in line.split(delimiter)])
                if any(
                    "data da venda" in [_normalize_ascii_text(cell) for cell in row]
                    and "valor bruto" in [_normalize_ascii_text(cell) for cell in row]
                    for row in candidate_rows
                ):
                    parsed_rows = candidate_rows
                    break
        headers: list[str] = []
        header_idx = -1
        for idx, row in enumerate(parsed_rows):
            normalized = [_normalize_ascii_text(cell) for cell in row]
            if "data da venda" in normalized and "valor bruto" in normalized and "status" in normalized:
                headers = [str(cell or "").strip() for cell in row]
                header_idx = idx
                break
        if header_idx < 0 or not headers:
            return []
        out: list[dict[str, str]] = []
        for row in parsed_rows[header_idx + 1 :]:
            if not any(str(value or "").strip() for value in row):
                continue
            row_map = {
                headers[idx]: str(row[idx] or "").strip()
                for idx in range(min(len(headers), len(row)))
                if str(headers[idx] or "").strip()
            }
            if any(str(value or "").strip() for value in row_map.values()):
                out.append(row_map)
        return out

    rows_out: list[dict[str, str]] = []
    try:
        xls = pd.ExcelFile(caminho_xlsx)
        for sheet_name in xls.sheet_names:
            df = pd.read_excel(xls, sheet_name=sheet_name, dtype=str).fillna("")
            for _, row in df.iterrows():
                rows_out.append({str(key or ""): str(value or "").strip() for key, value in row.items()})
        if rows_out:
            return rows_out
    except Exception:
        pass

    try:
        fallback_sheets = _read_xlsx_rows_fallback(caminho_xlsx)
    except Exception:
        try:
            return _rows_from_tabular_text(_read_text_file(caminho_xlsx))
        except Exception:
            return rows_out

    for _sheet_name, rows in fallback_sheets:
        if not rows:
            continue
        headers: list[str] = []
        header_idx = -1
        for idx, row in enumerate(rows):
            normalized = [_normalize_ascii_text(cell) for cell in row]
            if "data da venda" in normalized and "valor bruto" in normalized and "status" in normalized:
                headers = [str(cell or "").strip() for cell in row]
                header_idx = idx
                break
        if header_idx < 0 or not headers:
            continue
        for row in rows[header_idx + 1 :]:
            if not any(str(value or "").strip() for value in row):
                continue
            row_map = {
                headers[idx]: str(row[idx] or "").strip()
                for idx in range(min(len(headers), len(row)))
                if str(headers[idx] or "").strip()
            }
            if any(str(value or "").strip() for value in row_map.values()):
                rows_out.append(row_map)
    return rows_out


def _build_card_reports_from_caixa_xlsx(caminho_xlsx: str, data_br: str) -> dict[str, dict]:
    import pandas as pd

    sheet_rows = _collect_card_rows_from_caixa_xlsx(caminho_xlsx)
    buckets = {
        "cartao_credito_caixa": [],
        "cartao_debito_caixa": [],
    }
    seen_authorized_rows: set[tuple[str, str, str, str, float]] = set()

    for row in sheet_rows:
        normalized_row = {_normalize_ascii_text(key): str(value or "").strip() for key, value in row.items()}
        data_raw = normalized_row.get("data da venda", "")
        valor_raw = normalized_row.get("valor bruto", "")
        status_raw = normalized_row.get("status", "")
        produto_raw = normalized_row.get("produto", "")
        numero_raw = normalized_row.get("cod. de autorizacao", "") or normalized_row.get("comprovante de venda", "")
        if not data_raw or not valor_raw:
            continue
        match = re.match(r"^(\d{2}/\d{2}/\d{4})\s+(?:as|a?s)\s+(\d{2}:\d{2})(?::(\d{2}))?$", _normalize_ascii_text(data_raw))
        if not match:
            match = re.match(r"^(\d{2}/\d{2}/\d{4})\s+(\d{2}:\d{2})(?::(\d{2}))?$", _normalize_ascii_text(data_raw))
        if not match:
            continue
        data_venda = match.group(1)
        if data_venda != data_br:
            continue
        if _normalize_ascii_text(status_raw) not in {
            _normalize_ascii_text("Aprovada"),
            _normalize_ascii_text("Autorizada"),
        }:
            continue
        produto_norm = _normalize_ascii_text(produto_raw)
        if "debito" in produto_norm:
            key = "cartao_debito_caixa"
        elif "credito" in produto_norm or "parcelado" in produto_norm:
            key = "cartao_credito_caixa"
        else:
            continue
        hora = f"{match.group(2)}:{match.group(3) or '00'}"
        numero = str(numero_raw or "").strip()
        valor = round(parse_number(valor_raw), 2)
        numero_norm = _normalize_ascii_text(numero)
        if numero_norm:
            dedupe_key = (data_venda, hora[:5], numero_norm, key, valor)
            if dedupe_key in seen_authorized_rows:
                continue
            seen_authorized_rows.add(dedupe_key)
        buckets[key].append(
            {
                    "numero": numero,
                    "numero_exibicao": numero.lstrip("0") or numero or "-",
                    "data_venda": f"{data_venda} às {hora[:5]}",
                    "valor_bruto": valor,
            }
        )

    reports: dict[str, dict] = {}
    periodo = f"{data_br} - {data_br}"
    meta_by_key = {
        "cartao_credito_caixa": {
            "tab_title": "Cartão de Crédito CAIXA",
            "menu_text": "Abrir cartão de crédito CAIXA",
            "summary_label": "Cartão de crédito CAIXA",
            "total_label": "Total cartão de crédito CAIXA",
            "section_label": "Transações em cartão de crédito na CAIXA",
            "empty_message": "Nenhuma transação em cartão de crédito da CAIXA encontrada para este dia.",
        },
        "cartao_debito_caixa": {
            "tab_title": "Cartão de Débito CAIXA",
            "menu_text": "Abrir cartão de débito CAIXA",
            "summary_label": "Cartão de débito CAIXA",
            "total_label": "Total cartão de débito CAIXA",
            "section_label": "Transações em cartão de débito na CAIXA",
            "empty_message": "Nenhuma transação em cartão de débito da CAIXA encontrada para este dia.",
        },
    }
    for key, itens in buckets.items():
        itens.sort(key=lambda item: (item.get("data_venda", ""), item.get("numero", "")))
        total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
        meta = meta_by_key[key]
        reports[key] = {
            "arquivo": os.path.basename(caminho_xlsx),
            "caminho": caminho_xlsx,
            "periodo": periodo,
            "quantidade_autorizados": len(itens),
            "total_autorizado": total,
            "itens_autorizados": itens,
            "quantidade_relatorio": len(itens),
            "total_relatorio": total,
            "consistente": True,
            "origem": "caixa_cartoes_xlsx",
            "mensagem": None if itens else meta["empty_message"],
            "categoria": key,
            "tab_title": meta["tab_title"],
            "menu_text": meta["menu_text"],
            "summary_label": meta["summary_label"],
            "total_label": meta["total_label"],
            "section_label": meta["section_label"],
            "empty_message": meta["empty_message"],
            "table_headers": ("Comprovante", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }
    return reports


def _build_card_reports_from_caixa(caminho: str, data_br: str) -> dict[str, dict]:
    suffix = _effective_local_report_suffix(caminho)
    if suffix in {".xlsx", ".xls", ".csv"}:
        return _build_card_reports_from_caixa_xlsx(caminho, data_br)
    return _build_card_reports_from_caixa_pdf(caminho, data_br)


_AZULZINHA_UNIFIED_REQUIRED_HEADERS = ("data da venda", "modalidade", "produto", "valor bruto")


def _find_azulzinha_unified_header_row(rows: list[list[str]]) -> tuple[int, dict[str, int]] | None:
    for idx, row in enumerate(rows):
        normalized = [_normalize_ascii_text(cell) for cell in row]
        if all(header in normalized for header in _AZULZINHA_UNIFIED_REQUIRED_HEADERS):
            column_index: dict[str, int] = {}
            for pos, cell in enumerate(row):
                key = _normalize_ascii_text(cell)
                if key and key not in column_index:
                    column_index[key] = pos
            return idx, column_index
    return None


def _write_azulzinha_unified_report_files(
    caminho_xlsx: str,
    data_br: str,
    company_norm: str,
    output_dir: str | Path,
) -> dict[str, str | None]:
    """Reads the unified 'Relatório Histórico de vendas' export from the new Azulzinha/Caixa
    Vendas screen (one file covering PIX + cartão, all establishments) and rewrites it as the
    two legacy-shaped local files (card XLSX + PIX CSV) the rest of the pipeline already knows
    how to parse and reconcile."""
    output_dir = Path(output_dir)
    try:
        sheets = _read_xlsx_rows_fallback(caminho_xlsx)
    except Exception:
        return {"cartoes": None, "pix": None}

    pix_rows: list[dict[str, object]] = []
    credito_rows: list[dict[str, object]] = []
    debito_rows: list[dict[str, object]] = []

    for _sheet_name, rows in sheets:
        located = _find_azulzinha_unified_header_row(rows)
        if not located:
            continue
        header_idx, column_index = located

        def _cell(row: list[str], key: str) -> str:
            idx = column_index.get(key)
            if idx is None or idx >= len(row):
                return ""
            return str(row[idx] or "").strip()

        for row in rows[header_idx + 1 :]:
            if not any(str(value or "").strip() for value in row):
                continue
            normalized_row = {key: _cell(row, key) for key in column_index}
            parsed = _parse_cielo_card_datetime(normalized_row, data_br)
            if not parsed:
                continue
            data_venda_fmt, _ordem = parsed
            valor_raw = normalized_row.get("valor bruto", "")
            if not valor_raw:
                continue
            status_raw = _cell(row, "status")
            produto_raw = _cell(row, "produto")
            produto_norm = _normalize_ascii_text(produto_raw)
            modalidade_norm = _normalize_ascii_text(_cell(row, "modalidade"))
            numero = _cell(row, "cod. de autorizacao") or _cell(row, "comprovante de venda")

            if modalidade_norm == "via qrcode" or produto_norm == "pix":
                if _normalize_ascii_text(status_raw) not in {
                    _normalize_ascii_text("APROVADA"),
                    _normalize_ascii_text("AUTORIZADA"),
                    _normalize_ascii_text("EFETIVADO"),
                }:
                    continue
                pix_rows.append(
                    {
                        "Data da venda": data_venda_fmt,
                        "Cód. de autorização": numero,
                        "Valor bruto": valor_raw,
                        "Status": status_raw or "Autorizada",
                    }
                )
                continue

            if _normalize_ascii_text(status_raw) not in {
                _normalize_ascii_text("Aprovada"),
                _normalize_ascii_text("Autorizada"),
            }:
                continue
            card_row = {
                "Data da venda": data_venda_fmt,
                "Cód. de autorização": numero,
                "Comprovante da venda": _cell(row, "comprovante de venda"),
                "Produto": produto_raw,
                "Parcelado": _cell(row, "parcelas"),
                "Bandeira": _cell(row, "bandeira"),
                "Canal": _cell(row, "canal"),
                "Terminal": _cell(row, "numero do terminal"),
                "Valor bruto": valor_raw,
                "Status": status_raw,
                "Número do estabelecimento": _cell(row, "numero do estabelecimento"),
                "Final do cartão": _cell(row, "numero do cartao"),
                "Cód. Ref. Cartão": _cell(row, "cod. ref. cartao"),
            }
            if "debito" in produto_norm:
                debito_rows.append(card_row)
            elif "credito" in produto_norm or "parcelado" in produto_norm:
                credito_rows.append(card_row)

    result: dict[str, str | None] = {"cartoes": None, "pix": None}
    safe_date = data_br.replace("/", "-")
    output_dir.mkdir(parents=True, exist_ok=True)

    card_rows_all = credito_rows + debito_rows
    if card_rows_all:
        import pandas as pd

        columns = [
            "Data da venda", "Cód. de autorização", "Comprovante da venda", "Produto",
            "Parcelado", "Bandeira", "Canal", "Terminal", "Valor bruto", "Status",
            "Número do estabelecimento", "Final do cartão", "Cód. Ref. Cartão",
        ]
        cartoes_path = output_dir / f"Historico_Simplificado_de_vendas_{safe_date}_{company_norm}_auto.xlsx"
        pd.DataFrame(card_rows_all, columns=columns).to_excel(cartoes_path, index=False)
        result["cartoes"] = str(cartoes_path)

    if pix_rows:
        pix_path = output_dir / f"Relatorio_de_Vendas_Pix_{safe_date}_{company_norm}_auto.csv"
        with open(pix_path, "w", encoding="utf-8-sig", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=["Data da venda", "Cód. de autorização", "Valor bruto", "Status"],
                delimiter=";",
            )
            writer.writeheader()
            for row in pix_rows:
                writer.writerow(row)
        result["pix"] = str(pix_path)

    return result


_CIELO_DATE_FIELDS = (
    "data da venda",
    "data venda",
    "data da transacao",
    "data transacao",
    "data autorizacao",
    "data",
)
_CIELO_TIME_FIELDS = (
    "hora da venda",
    "hora venda",
    "hora da transacao",
    "hora transacao",
    "hora",
)
_CIELO_VALUE_FIELDS = (
    "valor bruto",
    "valor da venda",
    "valor venda",
    "valor transacao",
    "valor da transacao",
    "valor autorizado",
    "valor",
)
_CIELO_STATUS_FIELDS = (
    "status",
    "situacao",
    "situacao da venda",
    "status da venda",
    "status transacao",
    "status da transacao",
)
_CIELO_PRODUCT_FIELDS = (
    "produto",
    "modalidade",
    "tipo",
    "tipo de venda",
    "tipo venda",
    "forma de pagamento",
    "meio de pagamento",
    "meio pagamento",
)
_CIELO_NUMBER_FIELDS = (
    "codigo de autorizacao",
    "cod de autorizacao",
    "cod. de autorizacao",
    "autorizacao",
    "nsu",
    "nsu host",
    "comprovante",
    "comprovante de venda",
    "numero do pedido",
    "pedido",
    "tid",
)


def _pick_normalized_row_value(normalized_row: dict[str, str], field_names: tuple[str, ...]) -> str:
    normalized_names = [_normalize_ascii_text(name) for name in field_names]
    for name in normalized_names:
        value = str(normalized_row.get(name) or "").strip()
        if value:
            return value
    for key, value in normalized_row.items():
        if not str(value or "").strip():
            continue
        if any(name and (key == name or name in key) for name in normalized_names):
            return str(value or "").strip()
    return ""


def _cielo_header_score(cells: list[str]) -> int:
    normalized = [_normalize_ascii_text(cell) for cell in cells]
    joined = " ".join(normalized)
    score = 0
    if any("data" in cell for cell in normalized):
        score += 2
    if any("valor" in cell for cell in normalized):
        score += 2
    if any(marker in joined for marker in ("status", "situacao", "produto", "modalidade", "forma de pagamento", "meio de pagamento")):
        score += 1
    if any(marker in joined for marker in ("autorizacao", "comprovante", "nsu", "tid", "pedido")):
        score += 4
    if any("hora" in cell for cell in normalized):
        score += 1
    if "quantidade de vendas" in joined and not any(marker in joined for marker in ("status", "situacao", "autorizacao", "comprovante", "nsu", "tid", "pedido", "hora")):
        score -= 4
    return score


def _dict_rows_from_tabular_rows(rows: list[list[str]]) -> list[dict[str, str]]:
    header_idx = -1
    headers: list[str] = []
    best_score = -1
    for idx, row in enumerate(rows):
        row_values = [str(cell or "").strip() for cell in row]
        score = _cielo_header_score(row_values)
        if score >= 3 and score > best_score:
            header_idx = idx
            headers = row_values
            best_score = score
    if header_idx < 0 or not headers:
        return []

    output: list[dict[str, str]] = []
    for row in rows[header_idx + 1 :]:
        if not any(str(value or "").strip() for value in row):
            continue
        row_map = {
            headers[idx]: str(row[idx] or "").strip()
            for idx in range(min(len(headers), len(row)))
            if str(headers[idx] or "").strip()
        }
        if any(str(value or "").strip() for value in row_map.values()):
            output.append(row_map)
    return output


def _collect_card_rows_from_cielo_csv(caminho_csv: str) -> list[dict[str, str]]:
    text = _read_text_file(caminho_csv)
    lines = [line for line in text.splitlines() if str(line or "").strip()]
    if lines and _normalize_ascii_text(lines[0]).startswith("sep="):
        lines = lines[1:]
    delimiters = [";", ",", "\t", "|"]
    try:
        dialect = csv.Sniffer().sniff("\n".join(lines[:8]), delimiters=";,\t|")
        delimiters.insert(0, dialect.delimiter)
    except Exception:
        pass

    seen_delimiters: set[str] = set()
    for delimiter in delimiters:
        if delimiter in seen_delimiters:
            continue
        seen_delimiters.add(delimiter)
        try:
            rows = [
                [str(cell or "").strip() for cell in row]
                for row in csv.reader(lines, delimiter=delimiter)
            ]
        except Exception:
            continue
        dict_rows = _dict_rows_from_tabular_rows(rows)
        if dict_rows:
            return dict_rows
    return []


def _collect_card_rows_from_cielo_xlsx(caminho_xlsx: str) -> list[dict[str, str]]:
    import pandas as pd

    rows_out: list[dict[str, str]] = []
    try:
        xls = pd.ExcelFile(caminho_xlsx)
        for sheet_name in xls.sheet_names:
            df_raw = pd.read_excel(xls, sheet_name=sheet_name, dtype=str, header=None).fillna("")
            rows = [
                [str(value or "").strip() for value in row]
                for row in df_raw.values.tolist()
            ]
            rows_out.extend(_dict_rows_from_tabular_rows(rows))
        if rows_out:
            return rows_out
    except Exception:
        pass

    for _sheet_name, rows in _read_xlsx_rows_fallback(caminho_xlsx):
        rows_out.extend(_dict_rows_from_tabular_rows(rows))
    return rows_out


def _parse_cielo_card_datetime(normalized_row: dict[str, str], data_br: str) -> tuple[str, str] | None:
    data_raw = _pick_normalized_row_value(normalized_row, _CIELO_DATE_FIELDS)
    hora_raw = _pick_normalized_row_value(normalized_row, _CIELO_TIME_FIELDS)
    if not data_raw:
        return None

    cleaned = corrigir_texto(str(data_raw or "")).strip()
    if hora_raw and not re.search(r"\d{1,2}:\d{2}", cleaned):
        cleaned = f"{cleaned} {hora_raw}"
    cleaned = re.sub(r"\b(?:as|às|a?s)\b", " ", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()

    dt_obj: datetime | None = None
    serial_candidate = str(data_raw or "").strip()
    if re.fullmatch(r"\d+(?:[\.,]\d+)?", serial_candidate):
        try:
            serial_value = float(serial_candidate.replace(",", "."))
            if 30000 <= serial_value <= 80000:
                dt_obj = datetime(1899, 12, 30) + timedelta(days=serial_value)
                time_match = re.search(r"(\d{1,2}):(\d{2})(?::(\d{2}))?", str(hora_raw or ""))
                if time_match:
                    dt_obj = dt_obj.replace(
                        hour=int(time_match.group(1)),
                        minute=int(time_match.group(2)),
                        second=int(time_match.group(3) or "0"),
                    )
        except Exception:
            dt_obj = None
    for fmt in (
        "%d/%m/%Y %H:%M:%S",
        "%d/%m/%Y %H:%M",
        "%d/%m/%Y",
        "%Y-%m-%d %H:%M:%S",
        "%Y-%m-%d %H:%M",
        "%Y-%m-%d",
    ):
        try:
            dt_obj = datetime.strptime(cleaned[: len(datetime.now().strftime(fmt))], fmt)
            break
        except Exception:
            pass
    if dt_obj is None:
        match_br = re.search(r"(\d{2}/\d{2}/\d{4})(?:\D+(\d{1,2}:\d{2})(?::(\d{2}))?)?", cleaned)
        match_iso = re.search(r"(\d{4}-\d{2}-\d{2})(?:\D+(\d{1,2}:\d{2})(?::(\d{2}))?)?", cleaned)
        try:
            if match_br:
                hora = match_br.group(2) or "00:00"
                segundo = match_br.group(3) or "00"
                dt_obj = datetime.strptime(f"{match_br.group(1)} {hora}:{segundo}", "%d/%m/%Y %H:%M:%S")
            elif match_iso:
                hora = match_iso.group(2) or "00:00"
                segundo = match_iso.group(3) or "00"
                dt_obj = datetime.strptime(f"{match_iso.group(1)} {hora}:{segundo}", "%Y-%m-%d %H:%M:%S")
        except Exception:
            dt_obj = None
    if dt_obj is None:
        return None

    data_venda = dt_obj.strftime("%d/%m/%Y")
    if data_venda != data_br:
        return None
    return f"{data_venda} às {dt_obj.strftime('%H:%M')}", dt_obj.strftime("%Y-%m-%d %H:%M:%S")


def _cielo_status_is_approved(status_raw: str) -> bool:
    status_norm = _normalize_ascii_text(status_raw)
    if any(marker in status_norm for marker in ("cancel", "estorn", "negad", "recus", "falh", "desfeit", "devol", "chargeback")):
        return False
    if not status_norm:
        return True
    return any(marker in status_norm for marker in ("aprov", "autor", "captur", "confirm", "conclu", "finaliz", "liquid", "pago"))


def _cielo_card_key_from_row(normalized_row: dict[str, str]) -> str | None:
    product_raw = _pick_normalized_row_value(normalized_row, _CIELO_PRODUCT_FIELDS)
    row_text = _normalize_ascii_text(" ".join([product_raw, *normalized_row.values()]))
    if "debito" in row_text or "debit" in row_text:
        return "cartao_debito_caixa"
    if "credito" in row_text or "credit" in row_text or "parcelado" in row_text:
        return "cartao_credito_caixa"
    return None


def _build_card_reports_from_cielo(caminho: str, data_br: str) -> dict[str, dict]:
    suffix = _effective_local_report_suffix(caminho)
    if suffix == ".csv":
        rows = _collect_card_rows_from_cielo_csv(caminho)
        origem = "cielo_cartoes_csv"
    elif suffix == ".xlsx":
        rows = _collect_card_rows_from_cielo_xlsx(caminho)
        origem = "cielo_cartoes_xlsx"
    else:
        rows = []
        origem = "cielo_cartoes"

    buckets = {
        "cartao_credito_caixa": [],
        "cartao_debito_caixa": [],
    }
    all_items: dict[str, list[dict]] = {
        "cartao_credito_caixa": [],
        "cartao_debito_caixa": [],
    }

    for row in rows:
        normalized_row = {_normalize_ascii_text(key): str(value or "").strip() for key, value in row.items()}
        parsed_dt = _parse_cielo_card_datetime(normalized_row, data_br)
        if not parsed_dt:
            continue
        key = _cielo_card_key_from_row(normalized_row)
        if not key:
            continue
        valor_raw = _pick_normalized_row_value(normalized_row, _CIELO_VALUE_FIELDS)
        if not valor_raw:
            continue
        status_raw = _pick_normalized_row_value(normalized_row, _CIELO_STATUS_FIELDS)
        numero = _pick_normalized_row_value(normalized_row, _CIELO_NUMBER_FIELDS)
        data_venda, ordem = parsed_dt
        item = {
            "numero": numero,
            "numero_exibicao": str(numero or "").lstrip("0") or numero or "-",
            "data_venda": data_venda,
            "ordem": ordem,
            "valor_bruto": round(parse_number(valor_raw), 2),
            "status": status_raw,
        }
        all_items[key].append(item)
        if _cielo_status_is_approved(status_raw):
            buckets[key].append(
                {
                    "numero": item["numero"],
                    "numero_exibicao": item["numero_exibicao"],
                    "data_venda": item["data_venda"],
                    "ordem": item["ordem"],
                    "valor_bruto": item["valor_bruto"],
                }
            )

    reports: dict[str, dict] = {}
    periodo = f"{data_br} - {data_br}"
    meta_by_key = {
        "cartao_credito_caixa": {
            "tab_title": "Cartão de Crédito Cielo",
            "menu_text": "Abrir cartão de crédito Cielo",
            "summary_label": "Cartão de crédito Cielo",
            "total_label": "Total cartão de crédito Cielo",
            "section_label": "Transações em cartão de crédito na Cielo",
            "empty_message": "Nenhuma transação em cartão de crédito da Cielo encontrada para este dia.",
        },
        "cartao_debito_caixa": {
            "tab_title": "Cartão de Débito Cielo",
            "menu_text": "Abrir cartão de débito Cielo",
            "summary_label": "Cartão de débito Cielo",
            "total_label": "Total cartão de débito Cielo",
            "section_label": "Transações em cartão de débito na Cielo",
            "empty_message": "Nenhuma transação em cartão de débito da Cielo encontrada para este dia.",
        },
    }

    for key, itens in buckets.items():
        itens.sort(key=lambda item: (item.get("ordem", ""), item.get("numero", "")))
        total = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
        meta = meta_by_key[key]
        reports[key] = {
            "arquivo": os.path.basename(caminho),
            "caminho": caminho,
            "periodo": periodo,
            "quantidade_autorizados": len(itens),
            "total_autorizado": total,
            "itens_autorizados": itens,
            "quantidade_relatorio": len(itens),
            "total_relatorio": total,
            "consistente": True,
            "origem": origem,
            "mensagem": None if itens else meta["empty_message"],
            "categoria": key,
            "tab_title": meta["tab_title"],
            "menu_text": meta["menu_text"],
            "summary_label": meta["summary_label"],
            "total_label": meta["total_label"],
            "section_label": meta["section_label"],
            "empty_message": meta["empty_message"],
            "itens_todos": all_items[key],
            "table_headers": ("Comprovante", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }
    return reports


def _find_local_cielo_card_report(data_br: str, *, company: str = "MVA") -> dict[str, object]:
    matches: list[Path] = []
    avisos: list[str] = []
    company_norm = _normalize_ascii_text(company) or "mva"
    patterns = ("*.csv", "*.xlsx", "*.crdownload")

    for directory in _candidate_local_report_dirs():
        for pattern in patterns:
            for path in directory.glob(pattern):
                try:
                    effective_suffix = _effective_local_report_suffix(path)
                    if effective_suffix not in {".csv", ".xlsx"}:
                        continue
                    normalized_path = Path(_finalize_local_report_path(path))
                    if effective_suffix == ".csv":
                        text = _read_text_file(normalized_path)
                    else:
                        text = _read_excel_text(normalized_path)
                    name_norm = _normalize_ascii_text(normalized_path.name)
                    text_norm = _normalize_ascii_text(text[:6000])
                    if "cielo" not in name_norm and "cielo" not in text_norm:
                        continue
                    detected_date = _extract_local_report_date_br(text)
                    reports = _build_card_reports_from_cielo(str(normalized_path), data_br)
                    if any((report.get("itens_autorizados") or []) for report in reports.values()):
                        if detected_date and detected_date != data_br:
                            avisos.append(
                                f'O arquivo "{normalized_path.name}" tem cabeçalho Cielo iniciando em {detected_date}, mas trouxe transações de {data_br}; ele foi usado.'
                            )
                        matches.append(normalized_path)
                    else:
                        if detected_date and detected_date != data_br:
                            avisos.append(
                                f'O arquivo "{normalized_path.name}" foi identificado como relatório Cielo, mas o conteúdo é de {detected_date} e não trouxe transações de {data_br}. Ele foi ignorado.'
                            )
                            continue
                        avisos.append(
                            f'O arquivo "{normalized_path.name}" não trouxe transações Cielo aprovadas para {data_br} e foi ignorado.'
                        )
                except Exception as exc:
                    if "cielo" in _normalize_ascii_text(path.name):
                        avisos.append(f'Não foi possível ler o relatório Cielo "{path.name}": {exc}')
                    continue

    def _score(item: Path) -> tuple[int, float]:
        name = item.stem.casefold()
        if f"_{company_norm}_auto" in name:
            company_score = 3
        elif "_auto" in name:
            company_score = 1
        else:
            company_score = 0
        return (company_score, item.stat().st_mtime)

    return {
        "cartoes": str(max(matches, key=_score)) if matches else None,
        "avisos": list(dict.fromkeys(avisos)),
    }


MVA_CIELO_AUTO_MIN_PENDING_CARD_COUNT = 15


def _payment_report_total(report: dict | None) -> float:
    return round(float((report or {}).get("total_autorizado", 0.0) or 0.0), 2)


def _mva_cielo_needed_card_keys(relatorio_fechamento: dict) -> list[str]:
    relatorios_pagamento = relatorio_fechamento.get("relatorios_pagamento") or {}
    needed: list[str] = []
    for external_key, internal_key in (
        ("cartao_credito_caixa", "cartao_credito"),
        ("cartao_debito_caixa", "cartao_debito"),
    ):
        report_fechamento = relatorios_pagamento.get(internal_key) or {}
        report_externo = relatorios_pagamento.get(external_key) or {}
        total_fechamento = round(float(report_fechamento.get("total_autorizado", 0.0) or 0.0), 2)
        total_externo = round(float(report_externo.get("total_autorizado", 0.0) or 0.0), 2)
        if total_fechamento > 0.009 and total_externo + 0.01 < total_fechamento:
            needed.append(external_key)
    return needed


def _mva_cielo_pending_card_count(relatorio_fechamento: dict, needed_keys: list[str] | None = None) -> int:
    relatorios_pagamento = relatorio_fechamento.get("relatorios_pagamento") or {}
    needed = set(needed_keys or _mva_cielo_needed_card_keys(relatorio_fechamento))
    pending_count = 0
    for external_key, internal_key in (
        ("cartao_credito_caixa", "cartao_credito"),
        ("cartao_debito_caixa", "cartao_debito"),
    ):
        if external_key not in needed:
            continue
        report_fechamento = relatorios_pagamento.get(internal_key) or {}
        report_externo = relatorios_pagamento.get(external_key) or {}
        total_fechamento = round(float(report_fechamento.get("total_autorizado", 0.0) or 0.0), 2)
        total_externo = round(float(report_externo.get("total_autorizado", 0.0) or 0.0), 2)
        if total_fechamento <= 0.009 or total_externo + 0.01 >= total_fechamento:
            continue

        itens_fechamento = list(report_fechamento.get("itens_autorizados") or [])
        itens_externos = list(report_externo.get("itens_autorizados") or [])
        if itens_fechamento:
            try:
                _matched, _externos_sem_fechamento, fechamento_sem_externo = _multiset_match_by_value(
                    itens_externos,
                    itens_fechamento,
                    campo_esquerda="valor_bruto",
                    campo_direita="valor_bruto",
                )
                pending_count += len(fechamento_sem_externo)
                continue
            except Exception:
                pass

        quantidade_fechamento = int(report_fechamento.get("quantidade_autorizados") or len(itens_fechamento) or 0)
        quantidade_externo = int(report_externo.get("quantidade_autorizados") or len(itens_externos) or 0)
        pending_count += max(1, quantidade_fechamento - quantidade_externo)
    return pending_count


def _mva_caixa_reports_refresh_needs(relatorio_fechamento: dict) -> dict[str, object]:
    relatorios_pagamento = relatorio_fechamento.get("relatorios_pagamento") or {}
    reasons: list[str] = []
    need_cartoes = False

    for external_key, internal_key, label in (
        ("cartao_credito_caixa", "cartao_credito", "cartao_credito"),
        ("cartao_debito_caixa", "cartao_debito", "cartao_debito"),
    ):
        internal_total = _payment_report_total(relatorios_pagamento.get(internal_key))
        external_total = _payment_report_total(relatorios_pagamento.get(external_key))
        if internal_total > 0.009 and external_total + 0.01 < internal_total:
            need_cartoes = True
            reasons.append(f"{label}: fechamento={internal_total:.2f}, caixa/cielo={external_total:.2f}")

    pix_fechamento_total = _payment_report_total(relatorios_pagamento.get("pix_fechamento"))
    pix_caixa_total = _payment_report_total(relatorios_pagamento.get("pix_caixa"))
    need_pix = pix_fechamento_total > 0.009 and pix_caixa_total + 0.01 < pix_fechamento_total
    if need_pix:
        reasons.append(f"pix: fechamento={pix_fechamento_total:.2f}, caixa={pix_caixa_total:.2f}")

    return {
        "need_cartoes": need_cartoes,
        "need_pix": need_pix,
        "reasons": reasons,
    }


def _refresh_mva_caixa_reports_if_needed(
    relatorio_fechamento: dict,
    data_br: str,
    *,
    avisos_usuario: list[str] | None = None,
    auto_download_missing: bool = False,
    force_refresh_payments: bool = False,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
    company: str = "MVA",
) -> tuple[dict, list[str], bool]:
    avisos = list(avisos_usuario or relatorio_fechamento.get("avisos_usuario") or [])
    if _normalize_ascii_text(company) != "mva" or not data_br:
        return relatorio_fechamento, avisos, False
    if not auto_download_missing or force_refresh_payments:
        return relatorio_fechamento, avisos, False

    refresh_needs = _mva_caixa_reports_refresh_needs(relatorio_fechamento)
    need_pix = bool(refresh_needs.get("need_pix"))
    need_cartoes = bool(refresh_needs.get("need_cartoes"))
    if not (need_pix or need_cartoes):
        return relatorio_fechamento, avisos, False

    tipos = []
    if need_pix:
        tipos.append("PIX")
    if need_cartoes:
        tipos.append("cartoes")
    try:
        _emit_pix_status(
            on_status,
            f"Relatorios {'/'.join(tipos)} da Caixa/Azulzinha vieram abaixo do fechamento; baixando novamente...",
        )
        baixados = baixar_relatorios_caixa_eh_azulzinha(
            data_br,
            on_status=on_status,
            cancel_event=cancel_event,
            token_callback=token_callback,
            need_pix=need_pix,
            need_cartoes=need_cartoes,
            company=company,
        )
        avisos.extend(list(baixados.get("avisos") or []))
        relatorio_fechamento, _relatorio_pix, avisos_integracao = _integrate_local_payment_reports(
            relatorio_fechamento,
            data_br,
            avisos_usuario=avisos,
            company=company,
        )
        avisos.extend(list(avisos_integracao or []))
        avisos = list(dict.fromkeys(avisos))
        if avisos:
            relatorio_fechamento["avisos_usuario"] = avisos
        return relatorio_fechamento, avisos, True
    except Exception as exc:
        if str(exc).strip() == "__cancelled__":
            raise
        avisos.append(f"Nao foi possivel revalidar os relatorios da Caixa/Azulzinha: {exc}")
        relatorio_fechamento["avisos_usuario"] = list(dict.fromkeys(avisos))
        return relatorio_fechamento, avisos, False


def _merge_card_machine_report(existing: dict | None, extra: dict) -> dict:
    if not existing or not (existing.get("itens_autorizados") or []):
        return dict(extra)
    if not extra or not (extra.get("itens_autorizados") or []):
        return dict(existing)

    merged = dict(existing)
    existing_items = [dict(item) for item in existing.get("itens_autorizados") or []]
    extra_items = [dict(item) for item in extra.get("itens_autorizados") or []]
    items = existing_items + extra_items
    items.sort(key=lambda item: (item.get("ordem", "") or item.get("data_venda", ""), item.get("numero", "")))
    total = round(sum(float(item.get("valor_bruto", 0.0) or 0.0) for item in items), 2)

    categoria = str(extra.get("categoria") or existing.get("categoria") or "")
    is_credit = categoria == "cartao_credito_caixa"
    label = "Cartão de crédito" if is_credit else "Cartão de débito"
    label_title = "Cartão de Crédito" if is_credit else "Cartão de Débito"
    empty = f"Nenhuma transação em {label} da CAIXA/Cielo encontrada para este dia."

    merged.update(
        {
            "arquivo": " + ".join([str(existing.get("arquivo") or "").strip(), str(extra.get("arquivo") or "").strip()]).strip(" + "),
            "caminho": " + ".join([str(existing.get("caminho") or "").strip(), str(extra.get("caminho") or "").strip()]).strip(" + "),
            "quantidade_autorizados": len(items),
            "total_autorizado": total,
            "itens_autorizados": items,
            "quantidade_relatorio": len(items),
            "total_relatorio": total,
            "consistente": True,
            "origem": "caixa_cielo_cartoes",
            "mensagem": None if items else empty,
            "tab_title": f"{label_title} CAIXA/Cielo",
            "menu_text": f"Abrir {label} CAIXA/Cielo",
            "summary_label": f"{label} CAIXA/Cielo",
            "total_label": f"Total {label} CAIXA/Cielo",
            "section_label": f"Transações em {label} na CAIXA/Cielo",
            "empty_message": empty,
            "table_headers": ("Comprovante", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }
    )
    merged["itens_todos"] = [dict(item) for item in existing.get("itens_todos") or existing_items] + [
        dict(item) for item in extra.get("itens_todos") or extra_items
    ]
    return merged


def _select_cielo_items_for_closing_gap(
    existing: dict | None,
    extra: dict | None,
    closing: dict | None,
) -> list[dict]:
    extra_items = [dict(item) for item in (extra or {}).get("itens_autorizados") or []]
    if not extra_items:
        return []

    closing_items = [dict(item) for item in (closing or {}).get("itens_autorizados") or []]
    existing_items = [dict(item) for item in (existing or {}).get("itens_autorizados") or []]
    if closing_items:
        _matched_existing, _existing_without_closing, closing_missing = _multiset_match_by_value(
            existing_items,
            closing_items,
            campo_esquerda="valor_bruto",
            campo_direita="valor_bruto",
        )
        matched_extra, _extra_without_closing, _closing_still_missing = _multiset_match_by_value(
            extra_items,
            closing_missing,
            campo_esquerda="valor_bruto",
            campo_direita="valor_bruto",
        )
        return [dict(extra_item) for extra_item, _closing_item in matched_extra]

    closing_total = _payment_report_total(closing)
    if closing_total <= 0.009:
        return []
    existing_total = round(sum(float(item.get("valor_bruto", 0.0) or 0.0) for item in existing_items), 2)
    remaining = round(closing_total - existing_total, 2)
    if remaining <= 0.009:
        return []

    selected: list[dict] = []
    selected_total = 0.0
    for item in sorted(extra_items, key=lambda value: float(value.get("valor_bruto", 0.0) or 0.0), reverse=True):
        value = round(float(item.get("valor_bruto", 0.0) or 0.0), 2)
        if value <= 0.0:
            continue
        if selected_total + value <= remaining + 0.01:
            selected.append(dict(item))
            selected_total = round(selected_total + value, 2)
        if remaining - selected_total <= 0.009:
            break
    return selected


def _cielo_report_with_selected_items(report: dict, items: list[dict]) -> dict:
    selected = [dict(item) for item in items]
    total = round(sum(float(item.get("valor_bruto", 0.0) or 0.0) for item in selected), 2)
    filtered = dict(report)
    filtered["itens_autorizados"] = selected
    filtered["quantidade_autorizados"] = len(selected)
    filtered["total_autorizado"] = total
    filtered["quantidade_relatorio"] = len(selected)
    filtered["total_relatorio"] = total
    if "itens_todos" in filtered:
        filtered["itens_todos"] = selected
    return filtered


def _merge_cielo_reports_into_payment_reports(relatorios_pagamento: dict, cielo_reports: dict[str, dict]) -> bool:
    merged_any = False
    internal_keys = {
        "cartao_credito_caixa": "cartao_credito",
        "cartao_debito_caixa": "cartao_debito",
    }
    for key, report in cielo_reports.items():
        if key not in {"cartao_credito_caixa", "cartao_debito_caixa"}:
            continue
        if not (report.get("itens_autorizados") or []):
            continue
        selected_items = _select_cielo_items_for_closing_gap(
            relatorios_pagamento.get(key),
            report,
            relatorios_pagamento.get(internal_keys.get(key, "")),
        )
        if not selected_items:
            continue
        selected_report = _cielo_report_with_selected_items(report, selected_items)
        relatorios_pagamento[key] = _merge_card_machine_report(relatorios_pagamento.get(key), selected_report)
        merged_any = True
    return merged_any


def _integrate_cielo_card_reports_if_needed(
    relatorio_fechamento: dict,
    data_br: str,
    *,
    avisos_usuario: list[str] | None = None,
    auto_download_missing: bool = False,
    force_refresh_payments: bool = False,
    allow_cielo_fallback: bool = True,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
    company: str = "MVA",
) -> tuple[dict, list[str]]:
    avisos = list(avisos_usuario or [])
    if _normalize_ascii_text(company) != "mva" or not data_br:
        return relatorio_fechamento, avisos
    if not allow_cielo_fallback:
        return relatorio_fechamento, avisos

    cielo_decision_log_path: Path | None = None

    def cielo_decision_log(event: str, **details) -> None:
        nonlocal cielo_decision_log_path
        if not CIELO_DEBUG_LOGS_ENABLED:
            return
        if cielo_decision_log_path is None:
            cielo_decision_log_path = _new_cielo_debug_log_path(data_br, company)
        _write_cielo_debug_log(cielo_decision_log_path, event, **details)

    needed_keys = _mva_cielo_needed_card_keys(relatorio_fechamento)
    if not needed_keys and not force_refresh_payments:
        return relatorio_fechamento, avisos
    cielo_decision_log(
        "integration_start",
        needed_keys=needed_keys,
        auto_download_missing=auto_download_missing,
        force_refresh_payments=force_refresh_payments,
    )

    scope_windows = _report_scope_windows(relatorio_fechamento)
    relatorios_pagamento = dict(relatorio_fechamento.get("relatorios_pagamento") or {})

    def _read_and_merge(path_like: str | None, source_label: str) -> bool:
        if not path_like:
            return False
        try:
            cielo_reports = _build_card_reports_from_cielo(str(path_like), data_br)
            cielo_reports = {
                key: _filter_payment_report_to_scope(report, scope_windows)
                for key, report in cielo_reports.items()
            }
            return _merge_cielo_reports_into_payment_reports(relatorios_pagamento, cielo_reports)
        except Exception as exc:
            avisos.append(f"Não foi possível processar o relatório de cartões da Cielo ({source_label}): {exc}")
            return False

    local_cielo = _find_local_cielo_card_report(data_br, company=company)
    avisos.extend(local_cielo.get("avisos") or [])
    cielo_decision_log(
        "integration_local_search",
        found=bool(local_cielo.get("cartoes")),
        warnings_count=len(local_cielo.get("avisos") or []),
    )
    local_merged = _read_and_merge(local_cielo.get("cartoes"), "arquivo local")
    cielo_decision_log("integration_local_merge", merged=local_merged)

    relatorio_fechamento["relatorios_pagamento"] = relatorios_pagamento
    needed_keys = _mva_cielo_needed_card_keys(relatorio_fechamento)
    if not needed_keys:
        cielo_decision_log("integration_local_report_covers_closing", merged=local_merged)
        return relatorio_fechamento, list(dict.fromkeys(avisos))

    pending_card_count = _mva_cielo_pending_card_count(relatorio_fechamento, needed_keys)
    same_day_report = str(data_br or "").strip() == datetime.now().strftime("%d/%m/%Y")
    should_auto_download_cielo = force_refresh_payments or (
        pending_card_count >= MVA_CIELO_AUTO_MIN_PENDING_CARD_COUNT
    )
    cielo_decision_log(
        "integration_decision",
        needed_keys=needed_keys,
        pending_card_count=pending_card_count,
        threshold=MVA_CIELO_AUTO_MIN_PENDING_CARD_COUNT,
        auto_download_missing=auto_download_missing,
        force_refresh_payments=force_refresh_payments,
        same_day_report=same_day_report,
        should_auto_download_cielo=should_auto_download_cielo,
    )
    if (needed_keys or force_refresh_payments) and auto_download_missing and should_auto_download_cielo:
        try:
            baixado = baixar_relatorio_cielo_mva(
                data_br,
                on_status=on_status,
                cancel_event=cancel_event,
                token_callback=token_callback,
            )
            cielo_decision_log(
                "integration_download_result",
                has_card_report=bool(baixado.get("cartoes")),
                warnings_count=len(baixado.get("avisos") or []),
                download_debug_log=baixado.get("debug_log"),
            )
            avisos.extend(list(baixado.get("avisos") or []))
            if _read_and_merge(baixado.get("cartoes"), "download automático"):
                relatorio_fechamento["relatorios_pagamento"] = relatorios_pagamento
        except Exception as exc:
            if str(exc).strip() == "__cancelled__":
                raise
            cielo_decision_log("integration_download_error", error=str(exc), error_type=type(exc).__name__)
            avisos.append(f"Não foi possível baixar automaticamente o relatório de cartões da Cielo: {exc}")
    elif needed_keys and auto_download_missing and pending_card_count < MVA_CIELO_AUTO_MIN_PENDING_CARD_COUNT:
        cielo_decision_log(
            "integration_auto_download_skipped",
            reason="pending_card_count_below_threshold",
            pending_card_count=pending_card_count,
            threshold=MVA_CIELO_AUTO_MIN_PENDING_CARD_COUNT,
        )

    relatorio_fechamento["relatorios_pagamento"] = relatorios_pagamento
    avisos = list(dict.fromkeys(avisos))
    if avisos:
        relatorio_fechamento["avisos_usuario"] = avisos
    return relatorio_fechamento, avisos


def _build_generic_aux_report(
    *,
    categoria: str,
    tab_title: str,
    menu_text: str,
    summary_label: str,
    total_label: str,
    section_label: str,
    headers: tuple[str, ...],
    rows: list[tuple[str, ...]],
    periodo: str | None,
    quantidade: int,
    total: float,
    empty_message: str,
) -> dict:
    return {
        "arquivo": "",
        "caminho": "",
        "periodo": periodo,
        "quantidade_autorizados": quantidade,
        "total_autorizado": round(float(total or 0.0), 2),
        "itens_autorizados": [],
        "quantidade_relatorio": quantidade,
        "total_relatorio": round(float(total or 0.0), 2),
        "consistente": True,
        "origem": "eh_auxiliar",
        "mensagem": None if rows else empty_message,
        "categoria": categoria,
        "tab_title": tab_title,
        "menu_text": menu_text,
        "summary_label": summary_label,
        "total_label": total_label,
        "section_label": section_label,
        "empty_message": empty_message,
        "table_headers": headers,
        "table_rows": rows,
        "table_widths": [100, 220, 200, 120][: len(headers)],
        "table_mode": "custom",
    }


def _multiset_match_by_value(
    esquerda: list[dict],
    direita: list[dict],
    *,
    campo_esquerda: str = "valor",
    campo_direita: str = "valor",
) -> tuple[list[tuple[dict, dict]], list[dict], list[dict]]:
    buckets: dict[int, list[dict]] = {}
    for item in direita:
        key = int(round(float(item.get(campo_direita, 0.0)) * 100))
        buckets.setdefault(key, []).append(item)

    matched: list[tuple[dict, dict]] = []
    left_only: list[dict] = []
    for item in esquerda:
        key = int(round(float(item.get(campo_esquerda, 0.0)) * 100))
        if buckets.get(key):
            matched.append((item, buckets[key].pop(0)))
        else:
            left_only.append(item)

    right_only: list[dict] = []
    for values in buckets.values():
        right_only.extend(values)
    return matched, left_only, right_only


def _consume_matches_against_nf(
    itens_externos: list[dict],
    itens_nf: list[dict],
    *,
    campo_externo: str,
) -> tuple[list[tuple[dict, dict]], list[dict], list[dict]]:
    buckets: dict[int, list[dict]] = {}
    for item in itens_nf:
        key = int(round(float(item.get("valor", 0.0)) * 100))
        buckets.setdefault(key, []).append(item)

    matched: list[tuple[dict, dict]] = []
    remaining: list[dict] = []
    for item in itens_externos:
        key = int(round(float(item.get(campo_externo, 0.0)) * 100))
        if buckets.get(key):
            matched.append((item, buckets[key].pop(0)))
        else:
            remaining.append(item)
    remaining_nf: list[dict] = []
    for values in buckets.values():
        remaining_nf.extend(values)
    return matched, remaining, remaining_nf


def _build_eh_nf_filtered_report(relatorio_caixa: dict) -> dict | None:
    itens_nf = [
        item
        for item in (relatorio_caixa.get("itens_excluidos") or [])
        if "NOTA FISCAL ELETRONICA" in _normalize_caixa_client(item.get("documento", ""))
    ]
    if not itens_nf:
        return None

    rows = [
        (
            _display_eh_order_number(item.get("pedido", "")),
            str(item.get("cliente", "")),
            str(item.get("motivo", "")),
            f"R$ {format_number_br(item.get('valor', 0.0))}",
        )
        for item in itens_nf
    ]
    report = _build_generic_aux_report(
        categoria="nf_pedidos_eh",
        tab_title="NF-e Filtradas",
        menu_text="Abrir NF-e filtradas",
        summary_label="NF-e filtradas",
        total_label="Total NF-e filtradas",
        section_label="Pedidos NF-e filtrados",
        headers=("Pedido", "Cliente", "Motivo", "Valor"),
        rows=rows,
        periodo=relatorio_caixa.get("periodo"),
        quantidade=len(itens_nf),
        total=sum(float(item.get("valor", 0.0)) for item in itens_nf),
        empty_message="Nenhuma NF-e filtrada encontrada.",
    )
    report["table_widths"] = [90, 250, 220, 110]
    return report


def _build_eh_alerts_report(
    periodo: str | None,
    rows: list[tuple[str, ...]],
    *,
    pix_fechamento_rows: list[tuple[str, str]] | None = None,
    pix_maquina_rows: list[tuple[str, str]] | None = None,
    cartao_fechamento_rows: list[tuple[str, str]] | None = None,
    cartao_maquina_rows: list[tuple[str, str]] | None = None,
    cancelados_rows: list[tuple[str, str]] | None = None,
    allow_empty: bool = False,
) -> dict | None:
    pix_fechamento_rows = list(pix_fechamento_rows or [])
    pix_maquina_rows = list(pix_maquina_rows or [])
    cartao_fechamento_rows = list(cartao_fechamento_rows or [])
    cartao_maquina_rows = list(cartao_maquina_rows or [])
    cancelados_rows = list(cancelados_rows or [])
    tipos_alerta_exibidos = {"Cupom cancelado"}

    observacao_rows = [
        row
        for row in rows
        if row and row[0] not in {"CF sem Transação Bancária", "Transação Bancária sem CF/NF"}
    ]
    observacao_rows = [row for row in observacao_rows if row and row[0] not in tipos_alerta_exibidos]
    bank_pending_rows = (
        len(pix_fechamento_rows)
        + len(pix_maquina_rows)
        + len(cartao_fechamento_rows)
        + len(cartao_maquina_rows)
    )
    display_rows = bank_pending_rows + len(cancelados_rows) + len(observacao_rows)
    if display_rows <= 0 and not allow_empty:
        return None

    table_rows: list[tuple[str, ...]] = []
    if cancelados_rows:
        table_rows.append(("Cupons Cancelados", "", ""))
        table_rows.extend(cancelados_rows)
    for section_title, section_rows in (
        ("PIX - CF sem Transação Bancária", pix_fechamento_rows),
        ("PIX - Transação Bancária sem CF/NF", pix_maquina_rows),
        ("Cartões - CF sem Transação Bancária", cartao_fechamento_rows),
        ("Cartões - Transação Bancária sem CF/NF", cartao_maquina_rows),
        ("Observações", observacao_rows),
    ):
        if not section_rows:
            continue
        table_rows.append((section_title, "", ""))
        table_rows.extend(section_rows)

    total = 0.0
    for collection in (pix_fechamento_rows, pix_maquina_rows, cartao_fechamento_rows, cartao_maquina_rows):
        for row in collection:
            if not row:
                continue
            valor = row[-1]
            total += parse_number(valor)
    report = _build_generic_aux_report(
        categoria="alertas_eh",
        tab_title="Conciliação Bancária",
        menu_text="Abrir conciliação bancária",
        summary_label="Pendências",
        total_label="Total pendências",
        section_label="Pendências e sobras da conciliação bancária",
        headers=("Tipo", "Detalhe", "Valor"),
        rows=table_rows,
        periodo=periodo,
        quantidade=bank_pending_rows,
        total=total,
        empty_message="Nenhum alerta encontrado.",
    )
    report["table_widths"] = [170, 360, 110]
    report["pix_fechamento_rows"] = pix_fechamento_rows
    report["pix_maquina_rows"] = pix_maquina_rows
    report["cartao_fechamento_rows"] = cartao_fechamento_rows
    report["cartao_maquina_rows"] = cartao_maquina_rows
    report["cancelados_rows"] = cancelados_rows
    report["observacao_rows"] = observacao_rows
    return report


def _is_cancelled_coupon_alert_row(row: tuple[str, ...] | list[str] | None) -> bool:
    return bool(row) and str(row[0] or "").strip() == "Cupom cancelado"


def _count_visible_alert_rows(report: dict | None) -> int:
    report = report or {}
    return sum(
        len(report.get(key) or [])
        for key in (
            "pix_fechamento_rows",
            "cartao_fechamento_rows",
            "pix_maquina_rows",
            "cartao_maquina_rows",
        )
    )


def _build_eh_card_mismatch_report(
    periodo: str | None,
    itens_fechamento: list[dict],
    itens_maquina: list[dict],
) -> dict | None:
    if not itens_fechamento and not itens_maquina:
        return None

    def _tipo_curto(titulo: str) -> str:
        titulo = corrigir_texto(titulo)
        titulo_norm = _normalize_caixa_client(titulo)
        if "CREDITO" in titulo_norm:
            return "Crédito"
        if "DEBITO" in titulo_norm:
            return "Débito"
        return str(titulo or "").strip()

    itens_fechamento = sorted(
        itens_fechamento,
        key=lambda item: (_tipo_curto(item.get("titulo", "")), str(item.get("numero_exibicao") or "")),
    )
    itens_maquina = sorted(
        itens_maquina,
        key=lambda item: (_tipo_curto(item.get("titulo", "")), str(item.get("data_venda") or "")),
    )

    rows: list[tuple[str, ...]] = []
    fechamento_rows: list[tuple[str, str]] = []
    maquina_rows: list[tuple[str, str]] = []
    total = 0.0
    total += sum(float(item.get("valor", 0.0)) for item in itens_fechamento)
    total += sum(float(item.get("valor", 0.0)) for item in itens_maquina)

    for item in itens_fechamento:
        fechamento_rows.append(
            (
                f"{_tipo_curto(item.get('titulo', ''))}: CF {item.get('numero_exibicao') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )

    for item in itens_maquina:
        maquina_rows.append(
            (
                f"{_tipo_curto(item.get('titulo', ''))}: {item.get('data_venda') or item.get('numero_exibicao') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )

    max_len = max(len(itens_fechamento), len(itens_maquina))
    for idx in range(max_len):
        fechamento_item = itens_fechamento[idx] if idx < len(itens_fechamento) else None
        maquina_item = itens_maquina[idx] if idx < len(itens_maquina) else None

        fechamento_desc = ""
        fechamento_valor = ""
        if fechamento_item:
            fechamento_desc = (
                f"{_tipo_curto(fechamento_item.get('titulo', ''))}: "
                f"CF {fechamento_item.get('numero_exibicao') or '-'}"
            )
            fechamento_valor = f"R$ {format_number_br(fechamento_item.get('valor', 0.0))}"

        maquina_desc = ""
        maquina_valor = ""
        if maquina_item:
            maquina_desc = (
                f"{_tipo_curto(maquina_item.get('titulo', ''))}: "
                f"{maquina_item.get('data_venda') or maquina_item.get('numero_exibicao') or '-'}"
            )
            maquina_valor = f"R$ {format_number_br(maquina_item.get('valor', 0.0))}"

        rows.append((fechamento_desc, fechamento_valor, maquina_desc, maquina_valor))

    report = _build_generic_aux_report(
        categoria="cartoes_conciliacao_eh",
        tab_title="Conciliação Cartões",
        menu_text="Abrir conciliação cartões",
        summary_label="Pendências cartões",
        total_label="Total pendências cartões",
        section_label="Valores de cartões sem correspondência",
        headers=("Fechamento EH", "Valor EH", "Máquina", "Valor Banco"),
        rows=rows,
        periodo=periodo,
        quantidade=len(rows),
        total=total,
        empty_message="Nenhuma pendência de cartão encontrada.",
    )
    report["table_widths"] = [250, 110, 250, 110]
    report["fechamento_rows"] = fechamento_rows
    report["maquina_rows"] = maquina_rows
    report["fechamento_headers"] = ("Fechamento EH", "Valor EH")
    report["maquina_headers"] = ("Máquina", "Valor Banco")
    report["fechamento_section_label"] = "CF sem Transação Bancária"
    report["maquina_section_label"] = "Transação Bancária sem CF/NF"
    report["fechamento_empty_message"] = "Nenhum CF sem transação bancária encontrado."
    report["maquina_empty_message"] = "Nenhuma transação bancária sem CF/NF encontrada."
    report["fechamento_widths"] = [250, 110]
    report["maquina_widths"] = [250, 110]
    return report


def _analisar_html_fechamento_caixa_eh(html_text: str, arquivo: str = "Fechamento de caixa - Zweb") -> dict:
    from bs4 import BeautifulSoup

    periodo = _extract_zweb_period(html_text)
    nfces_map = {}
    totalizadores = {}
    relatorios_pagamento_brutos = {}
    total_abertura = 0.0
    total_sangria = 0.0
    total_geral = 0.0
    fechamento_janelas: list[dict] = []

    soup = BeautifulSoup(html_text, "html.parser")
    money_pattern = re.compile(r"R\$\s*([-\d\.,]+)", re.IGNORECASE)
    date_pattern = re.compile(r"(\d{2}/\d{2}/\d{2})")

    for section in soup.find_all("div", class_="mt-4"):
        title_node = section.find("div", class_="fw-bolder fs-6")
        if not title_node:
            continue
        titulo = _clean_zweb_html_value(title_node.get_text(" ", strip=True))
        section_text = section.get_text(" ", strip=True)
        abertura_match = re.search(r"Abertura:\s*(\d{2}/\d{2}/\d{4}\s+\d{2}:\d{2}:\d{2})", section_text)
        fechamento_match = re.search(r"Fechamento:\s*(\d{2}/\d{2}/\d{4}\s+\d{2}:\d{2}:\d{2})", section_text)
        fechamento_janela = _build_scope_window(
            abertura_match.group(1) if abertura_match else "",
            fechamento_match.group(1) if fechamento_match else "",
        )
        if fechamento_janela:
            fechamento_janelas.append(fechamento_janela)
        scope_abertura = str((fechamento_janela or {}).get("abertura") or "").strip()
        scope_fechamento = str((fechamento_janela or {}).get("fechamento") or "").strip()
        meta_pagamento = _build_zweb_payment_report_meta(titulo)
        bucket_pagamento = None
        if meta_pagamento:
            bucket_pagamento = relatorios_pagamento_brutos.setdefault(
                meta_pagamento["key"],
                {
                    **meta_pagamento,
                    "itens": [],
                    "total_secao": 0.0,
                },
            )

        table = section.find_next_sibling("table")
        if table is None:
            continue
        footer = table.find_next_sibling("div", class_="totalizer-footer")
        if bucket_pagamento is not None and footer is not None:
            footer_money = money_pattern.search(footer.get_text(" ", strip=True))
            if footer_money:
                bucket_pagamento["total_secao"] = round(
                    float(bucket_pagamento.get("total_secao", 0.0)) + parse_number(footer_money.group(1)),
                    2,
                )

        for row in table.find_all("tr"):
            cells = row.find_all("td")
            if len(cells) < 3:
                continue
            numero_text = cells[0].get_text(" ", strip=True)
            data_text = cells[1].get_text(" ", strip=True)
            valores_linha = [
                round(parse_number(valor_str), 2)
                for valor_str in money_pattern.findall(cells[2].get_text(" ", strip=True))
            ]
            numero_match = re.search(r"(\d{6,})", numero_text)
            data_match = date_pattern.search(data_text)
            if not numero_match or not data_match or not valores_linha:
                continue

            numero = numero_match.group(1)
            data_venda = data_match.group(1)
            numero_normalizado = _normalize_fiscal_number(numero)
            valor = round(sum(valores_linha), 2)
            data_exibicao = _display_zweb_short_date(data_venda)
            existente = nfces_map.get(numero_normalizado)
            if existente:
                existente["valor"] = round(existente["valor"] + valor, 2)
                if titulo not in existente["descricao"]:
                    existente["descricao"] = f"{existente['descricao']} + {titulo}"
            else:
                nfces_map[numero_normalizado] = {
                    "numero": numero_normalizado,
                    "numero_exibicao": _display_fiscal_number(numero_normalizado),
                    "descricao": titulo,
                    "data_venda": data_exibicao,
                    "scope_abertura": scope_abertura,
                    "scope_fechamento": scope_fechamento,
                    "valor": valor,
                }
            if bucket_pagamento is not None:
                for valor_parcela in valores_linha:
                    bucket_pagamento["itens"].append(
                        {
                            "numero": numero_normalizado,
                            "numero_exibicao": _display_fiscal_number(numero_normalizado),
                            "data_venda": data_exibicao,
                            "scope_abertura": scope_abertura,
                            "scope_fechamento": scope_fechamento,
                            "valor_bruto": valor_parcela,
                        }
                    )

    totalizer_table = soup.find("table", class_=lambda value: value and "totalizers-table" in value)
    if totalizer_table:
        for row in totalizer_table.find_all("tr"):
            cells = row.find_all("td")
            if len(cells) < 2:
                continue
            label = _clean_zweb_html_value(cells[0].get_text(" ", strip=True))
            valor_match = money_pattern.search(cells[1].get_text(" ", strip=True))
            if not label or not valor_match:
                continue
            valor_str = valor_match.group(1)
            valor = round(parse_number(valor_str), 2)
            totalizadores[label] = valor
            label_normalizado = _normalize_caixa_client(label)
            if "ABERTURA" in label_normalizado:
                total_abertura = valor
            elif "SANGRIA" in label_normalizado:
                total_sangria = valor
            elif "TOTAL GERAL" in label_normalizado:
                total_geral = valor

    itens_nfce = sorted(nfces_map.values(), key=lambda item: item["numero"])
    total_nfce = round(sum(item["valor"] for item in itens_nfce), 2)
    if not total_geral:
        total_geral = round(total_nfce + total_abertura - total_sangria, 2)

    relatorios_pagamento = {}
    for key, bucket in relatorios_pagamento_brutos.items():
        itens = sorted(
            bucket.get("itens", []),
            key=lambda item: (item.get("data_venda") or "", item.get("numero") or ""),
        )
        total_itens = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
        total_reportado = round(float(totalizadores.get(bucket["forma_pagamento"], bucket.get("total_secao", 0.0))), 2)
        relatorios_pagamento[key] = {
            "arquivo": arquivo,
            "caminho": "",
            "periodo": periodo,
            "quantidade_autorizados": len(itens),
            "total_autorizado": total_reportado,
            "itens_autorizados": itens,
            "quantidade_relatorio": len(itens),
            "total_relatorio": total_reportado,
            "consistente": abs(total_itens - total_reportado) < 0.01,
            "origem": "zweb_fechamento_caixa",
            "mensagem": None if itens else bucket.get("empty_message"),
            "categoria": key,
            "tab_title": bucket.get("tab_title"),
            "menu_text": bucket.get("menu_text"),
            "summary_label": bucket.get("summary_label"),
            "total_label": bucket.get("total_label"),
            "section_label": bucket.get("section_label"),
            "empty_message": bucket.get("empty_message"),
            "table_headers": ("NFC-e", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }

    fechamento_janelas = _normalize_scope_windows(fechamento_janelas)
    return {
        "arquivo": arquivo,
        "arquivo_tipo": "fechamento_caixa_zweb",
        "arquivo_resumo_titulo": "Arquivo Fechamento",
        "total_resumo_titulo": "Total Fechamento de caixa",
        "subtitle": (
            "Compara o total de caixa dos pedidos com o Fechamento de caixa do Zweb "
            "e aponta as NFC-e faltantes."
        ),
        "resumo_modelo": "EH",
        "periodo": periodo,
        "quantidade_nfce": len(itens_nfce),
        "total_nfce": total_nfce,
        "total_geral": total_geral,
        "total_abertura": total_abertura,
        "total_sangria": total_sangria,
        "totalizadores": totalizadores,
        "relatorios_pagamento": relatorios_pagamento,
        "fechamento_janelas": fechamento_janelas,
        "fechamento_parcial": _is_partial_scope_windows(fechamento_janelas),
        "nfces": itens_nfce,
        "nfces_faltantes_sequencia": _find_missing_fiscal_numbers([item["numero"] for item in itens_nfce]),
        "fiscal_status_map": {},
    }


def _is_mva_clipp_fechamento_text(texto: str) -> bool:
    texto_normalizado = _normalize_caixa_client(texto)
    return (
        "FECHAMENTO DE CAIXA" in texto_normalizado
        and "DOCUMENTOS GERADOS" in texto_normalizado
        and "PAGAMENTO INSTANTANEO" in texto_normalizado
        and "MVA COMERCIO" in texto_normalizado
    )


def analisar_pdf_fechamento_caixa_mva_clipp(
    caminho_pdf: str,
    *,
    company: str = "MVA",
    avisos_usuario: list[str] | None = None,
    auto_download_missing: bool = False,
    force_refresh_payments: bool = False,
    allow_cielo_fallback: bool = True,
    scope_mode: str | None = None,
    filter_opening_date_br: str | None = None,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
) -> dict:
    texto = _read_pdf_text(caminho_pdf)
    if not _is_mva_clipp_fechamento_text(texto):
        avisos = list(avisos_usuario or [])
        avisos.append(
            "O PDF informado como Fechamento de Caixa da MVA não corresponde ao layout esperado do fechamento Clipp. "
            "Ele será tratado apenas como relatório local, e a busca automática dos pagamentos na Azulzinha/Caixa não será acionada por este arquivo."
        )
        return {
            "arquivo": os.path.basename(caminho_pdf),
            "arquivo_tipo": "mva_desconhecido",
            "resumo_modelo": "MVA",
            "periodo": None,
            "quantidade_nfce": 0,
            "total_nfce": 0.0,
            "relatorios_pagamento": {},
            "fechamento_janelas": [],
            "fechamento_parcial": False,
            "nfces": [],
            "nfces_faltantes_sequencia": [],
            "fiscal_status_map": {},
            "avisos_usuario": list(dict.fromkeys(avisos)),
        }

    linhas_brutas = [corrigir_texto(linha.strip()) for linha in texto.splitlines()]
    linhas: list[str] = []
    for linha in linhas_brutas:
        if not linha:
            continue
        linha_normalizada = _normalize_caixa_client(linha)
        if linha.lower().startswith("file:///"):
            continue
        if linha_normalizada == "(PIX)":
            continue
        if re.fullmatch(r"\d{2}/\d{2}/\d{2},\s+\d{2}:\d{2}\s+clipp_exportado\.htm", linha, re.IGNORECASE):
            continue
        linhas.append(linha)

    periodo = None
    match_periodo = re.search(
        r"PER[IÍ]ODO ANALISADO,\s*DE\s*(\d{2}/\d{2}/\d{4})\s*AT[ÉE]\s*(\d{2}/\d{2}/\d{4})",
        _normalize_caixa_client(texto),
    )
    if match_periodo:
        periodo = f"{match_periodo.group(1)} - {match_periodo.group(2)}"
    data_base = _extract_period_range(periodo or "")[0] or ""
    fechamento_janelas = _normalize_scope_windows(
        [
            {
                "abertura": match.group(1),
                "fechamento": match.group(2),
            }
            for match in re.finditer(
                r"\b\d+\s*-\s*Abertura\s*:\s*(\d{2}/\d{2}/\d{4}\s+\d{2}:\d{2}:\d{2})\s*-\s*Fechamento\s*:\s*(\d{2}/\d{2}/\d{4}\s+\d{2}:\d{2}:\d{2})",
                corrigir_texto(texto),
                re.IGNORECASE,
            )
        ]
    )

    payment_aliases = [
        ("Pagamento Instantâneo (PIX)", ("PAGAMENTO INSTANTANEO (PIX)", "PAGAMENTO INSTANTANEO")),
        ("Cartão de Crédito", ("CARTAO DE CREDITO",)),
        ("Cartão de Débito", ("CARTAO DE DEBITO",)),
        ("Dinheiro", ("DINHEIRO",)),
    ]

    totais_pagamento: dict[str, float] = {}
    nfces_map: dict[str, dict] = {}
    payment_buckets: dict[str, dict] = {}

    for linha in linhas:
        linha_normalizada = _normalize_caixa_client(linha)
        total_match = re.match(
            r"^(DINHEIRO|CARTAO DE CREDITO|CARTAO DE DEBITO|PAGAMENTO INSTANTANEO(?: \(PIX\))?)\s*:?\s*([-\d\.,]+)$",
            linha_normalizada,
        )
        if total_match:
            label_ascii = total_match.group(1)
            valor = round(parse_number(total_match.group(2)), 2)
            canonical_label = next(
                (
                    display
                    for display, aliases in payment_aliases
                    if any(alias == label_ascii for alias in aliases)
                ),
                None,
            )
            if canonical_label:
                totais_pagamento[canonical_label] = valor
            continue

        doc_match = re.match(r"^(?P<numero>\d{6,})\s+NFCE\s+(?P<hora>\d{2}:\d{2}:\d{2})\s+(?P<resto>.+)$", linha_normalizada)
        if not doc_match:
            continue

        numero = _normalize_fiscal_number(doc_match.group("numero"))
        hora = doc_match.group("hora")
        resto_original = linha[doc_match.end("hora"):].strip()
        valor_match = re.search(r"([-\d\.,]+)\s*$", resto_original)
        if not valor_match:
            continue
        valor = round(parse_number(valor_match.group(1)), 2)
        corpo_original = resto_original[: valor_match.start()].strip()
        corpo_normalizado = _normalize_caixa_client(corpo_original)

        forma_pagamento = ""
        idx_forma = -1
        for display_label, aliases in payment_aliases:
            for alias in aliases:
                current_idx = corpo_normalizado.rfind(alias)
                if current_idx > idx_forma:
                    idx_forma = current_idx
                    forma_pagamento = display_label

        cliente = corpo_original
        if idx_forma >= 0 and forma_pagamento:
            forma_ascii = _normalize_caixa_client(forma_pagamento)
            idx_original = _normalize_caixa_client(corpo_original).rfind(forma_ascii)
            if idx_original >= 0:
                cliente = corpo_original[:idx_original].strip()
            else:
                cliente = corpo_original

        data_venda = f"{data_base} {hora}".strip() if data_base else hora
        existente = nfces_map.get(numero)
        if existente is None:
            nfces_map[numero] = {
                "numero": numero,
                "numero_exibicao": _display_fiscal_number(numero),
                "descricao": forma_pagamento or "NFC-e",
                "data_venda": data_venda,
                "cliente": cliente,
                "valor": valor,
            }
        else:
            existente["valor"] = round(float(existente.get("valor", 0.0)) + valor, 2)
            if forma_pagamento and forma_pagamento not in str(existente.get("descricao") or ""):
                existente["descricao"] = f"{existente['descricao']} + {forma_pagamento}"

        if not forma_pagamento:
            continue
        meta_pagamento = _build_zweb_payment_report_meta(forma_pagamento)
        if not meta_pagamento:
            continue
        bucket = payment_buckets.setdefault(
            meta_pagamento["key"],
            {
                **meta_pagamento,
                "itens": [],
            },
        )
        bucket["itens"].append(
            {
                "numero": numero,
                "numero_exibicao": _display_fiscal_number(numero),
                "data_venda": data_venda,
                "valor_bruto": valor,
            }
        )

    itens_nfce = sorted(nfces_map.values(), key=lambda item: item["numero"])
    total_nfce = round(sum(float(item.get("valor", 0.0)) for item in itens_nfce), 2)

    relatorios_pagamento = {}
    for key, bucket in payment_buckets.items():
        itens = sorted(
            bucket.get("itens", []),
            key=lambda item: (str(item.get("data_venda") or ""), str(item.get("numero") or "")),
        )
        total_itens = round(sum(float(item.get("valor_bruto", 0.0)) for item in itens), 2)
        total_reportado = round(float(totais_pagamento.get(bucket["forma_pagamento"], total_itens)), 2)
        relatorios_pagamento[key] = {
            "arquivo": os.path.basename(caminho_pdf),
            "caminho": caminho_pdf,
            "periodo": periodo,
            "quantidade_autorizados": len(itens),
            "total_autorizado": total_reportado,
            "itens_autorizados": itens,
            "quantidade_relatorio": len(itens),
            "total_relatorio": total_reportado,
            "consistente": abs(total_itens - total_reportado) < 0.01,
            "origem": "clipp_fechamento_caixa_mva",
            "mensagem": None if itens else bucket.get("empty_message"),
            "categoria": key,
            "tab_title": bucket.get("tab_title"),
            "menu_text": bucket.get("menu_text"),
            "summary_label": bucket.get("summary_label"),
            "total_label": bucket.get("total_label"),
            "section_label": bucket.get("section_label"),
            "empty_message": bucket.get("empty_message"),
            "table_headers": ("NFC-e", "Data", "Valor"),
            "table_mode": "numero_data_valor",
        }

    report = {
        "arquivo": os.path.basename(caminho_pdf),
        "arquivo_tipo": "fechamento_caixa_clipp_mva",
        "arquivo_resumo_titulo": "Arquivo Fechamento",
        "total_resumo_titulo": "Total Fechamento de caixa",
        "subtitle": "Compara os DAVs finalizados com o fechamento do Clipp e cruza as formas de pagamento com os relatórios da Caixa.",
        "resumo_modelo": "MVA",
        "periodo": periodo,
        "quantidade_nfce": len(itens_nfce),
        "total_nfce": total_nfce,
        "total_geral": total_nfce,
        "totalizadores": totais_pagamento,
        "relatorios_pagamento": relatorios_pagamento,
        "fechamento_janelas": fechamento_janelas,
        "fechamento_parcial": _is_partial_scope_windows(fechamento_janelas),
        "nfces": itens_nfce,
        "nfces_faltantes_sequencia": _find_missing_fiscal_numbers([item["numero"] for item in itens_nfce]),
        "fiscal_status_map": {},
    }
    data_br = _extract_period_range(periodo or "")[0]
    opening_filter_date = str(filter_opening_date_br or "").strip()
    if opening_filter_date:
        opening_windows = [
            window
            for window in fechamento_janelas
            if str(window.get("abertura") or "").strip().startswith(opening_filter_date)
        ]
        if opening_windows:
            report = _filter_fechamento_report_to_scope(report, opening_windows)
            report["periodo"] = f"{opening_filter_date} - {opening_filter_date}"
            report["fechamento_data_abertura_filtrada"] = opening_filter_date
            for payment_report in (report.get("relatorios_pagamento") or {}).values():
                if isinstance(payment_report, dict):
                    payment_report["periodo"] = report["periodo"]
            data_br = opening_filter_date
    requested_scope_windows = _scope_windows_for_mode(fechamento_janelas, scope_mode)
    if opening_filter_date:
        requested_scope_windows = _scope_windows_for_mode(report.get("fechamento_janelas"), scope_mode)
    if requested_scope_windows and _normalize_ascii_text(scope_mode or "") not in {"", "daily", "diario"}:
        report = _filter_fechamento_report_to_scope(report, requested_scope_windows)
        report["escopo_relatorio"] = _scope_mode_label(scope_mode)
    avisos = list(avisos_usuario or [])
    if data_br and auto_download_missing:
        local_payment_reports = _find_eh_local_payment_reports(data_br, company=company)
        need_pix = not bool(local_payment_reports.get("pix"))
        need_cartoes = not bool(local_payment_reports.get("cartoes"))
        if force_refresh_payments or need_pix or need_cartoes:
            try:
                baixados = baixar_relatorios_caixa_eh_azulzinha(
                    data_br,
                    on_status=on_status,
                    cancel_event=cancel_event,
                    token_callback=token_callback,
                    need_pix=force_refresh_payments or need_pix,
                    need_cartoes=force_refresh_payments or need_cartoes,
                    company=company,
                )
                avisos.extend(list(baixados.get("avisos") or []))
            except Exception as exc:
                if str(exc).strip() == "__cancelled__":
                    raise
                avisos.append(f"Não foi possível baixar automaticamente os relatórios da Caixa da {company}: {exc}")
    if data_br:
        report, _relatorio_pix, _avisos = _integrate_local_payment_reports(
            report,
            data_br,
            avisos_usuario=avisos,
            company=company,
        )
        report, avisos, refreshed_caixa_payments = _refresh_mva_caixa_reports_if_needed(
            report,
            data_br,
            avisos_usuario=report.get("avisos_usuario") or avisos,
            auto_download_missing=auto_download_missing,
            force_refresh_payments=force_refresh_payments,
            on_status=on_status,
            cancel_event=cancel_event,
            token_callback=token_callback,
            company=company,
        )
        report, avisos = _integrate_cielo_card_reports_if_needed(
            report,
            data_br,
            avisos_usuario=report.get("avisos_usuario") or avisos,
            auto_download_missing=auto_download_missing,
            force_refresh_payments=force_refresh_payments,
            allow_cielo_fallback=allow_cielo_fallback,
            on_status=on_status,
            cancel_event=cancel_event,
            token_callback=token_callback,
            company=company,
        )
    return report


def gerar_relatorios_caixa_eh_manuais(
    data_br: str,
    caminho_pedidos_html: str,
    caminho_fechamento_html: str,
) -> tuple[dict, dict, dict | None]:
    texto_pedidos = _read_text_file(caminho_pedidos_html)
    texto_fechamento = _read_text_file(caminho_fechamento_html)

    relatorio = _analisar_html_pedidos_importados_eh(
        texto_pedidos,
        arquivo=os.path.basename(caminho_pedidos_html),
    )
    relatorio_fechamento = _analisar_html_fechamento_caixa_eh(
        texto_fechamento,
        arquivo=os.path.basename(caminho_fechamento_html),
    )
    relatorio_fechamento["fiscal_status_map"] = {}
    relatorio = _aplicar_filtro_canceladas_pedidos_eh(relatorio, {})
    relatorio_fechamento, relatorio_pix, _avisos = _integrate_local_payment_reports(
        relatorio_fechamento,
        data_br,
    )
    return relatorio, relatorio_fechamento, relatorio_pix




def _mva_report_type_from_text(texto: str) -> str:
    texto_normalizado = _normalize_caixa_client(texto)
    if "DAV - ORCAMENTO" in texto_normalizado:
        return "orcamentos_mva"
    if "DAV - PEDIDOS DE VENDA" in texto_normalizado:
        return "exportacao_dados_mva"
    return "mva_desconhecido"


def _mva_report_label(arquivo_tipo: str) -> str:
    if arquivo_tipo == "orcamentos_mva":
        return "Orcamentos"
    if arquivo_tipo == "exportacao_dados_mva":
        return "Exportacao de dados"
    return "MVA"


def criar_relatorio_orcamentos_mva_vazio(periodo: str | None = None) -> dict:
    return {
        "arquivo": "Orcamento ignorado",
        "caixa_modelo": "MVA",
        "arquivo_tipo": "orcamentos_mva",
        "periodo": periodo,
        "pedidos_total": 0,
        "pedidos_balcao": 0,
        "pedidos_caixa": 0,
        "pedidos_excluidos": 0,
        "pedidos_excluidos_cliente": 0,
        "pedidos_excluidos_documento": 0,
        "pedidos_editando": 0,
        "pedidos_outros_status": 0,
        "total_documento": 0.0,
        "total_excluido": 0.0,
        "total_caixa": 0.0,
        "itens_caixa": [],
        "itens_excluidos": [],
        "orcamento_ignorado": True,
    }


def _normalize_mva_description(resto_linha: str) -> str:
    descricao = re.sub(r"^\s*\d+\s+", "", (resto_linha or "").strip())
    return descricao or "-"


def _extract_mva_word_rows(page) -> list[list[dict]]:
    rows_by_top = {}
    for word in page.extract_words(use_text_flow=False):
        rows_by_top.setdefault(round(word["top"], 1), []).append(word)

    grouped_rows = []
    for top in sorted(rows_by_top):
        row = sorted(rows_by_top[top], key=lambda item: item["x0"])
        if any(re.fullmatch(r"\d{6,}", item["text"]) and item["x0"] < 60 for item in row):
            grouped_rows.append(row)
    return grouped_rows


def _extract_mva_column_bounds(page) -> dict:
    rows_by_top = {}
    for word in page.extract_words(use_text_flow=False):
        rows_by_top.setdefault(round(word["top"], 1), []).append(word)

    header_row = None
    for top in sorted(rows_by_top):
        row = sorted(rows_by_top[top], key=lambda item: item["x0"])
        normalized = [_normalize_caixa_client(item["text"]) for item in row]
        if "STATUS" in normalized:
            header_row = row
            break

    bounds = {
        "code_x1": 140.0,
        "vendor_x0": None,
        "status_x0": None,
    }
    if not header_row:
        return bounds

    for item in header_row:
        normalized = _normalize_caixa_client(item["text"])
        if normalized in {"CODIGO", "CÓDIGO"}:
            bounds["code_x1"] = item["x1"]
        elif normalized == "VENDEDOR":
            bounds["vendor_x0"] = item["x0"]
        elif normalized == "STATUS":
            bounds["status_x0"] = item["x0"]
    return bounds


def _extract_mva_description_from_row(row_words: list[dict], bounds: dict, fallback: str) -> str:
    if not row_words:
        return fallback

    left_bound = float(bounds.get("code_x1") or 140.0) + 2.0
    right_bound = None
    vendor_x0 = bounds.get("vendor_x0")
    status_x0 = bounds.get("status_x0")
    if vendor_x0 is not None:
        right_bound = float(vendor_x0) - 32.0
    elif status_x0 is not None:
        right_bound = float(status_x0) - 20.0

    descricao = " ".join(
        item["text"]
        for item in row_words
        if item["x0"] >= left_bound and (right_bound is None or item["x1"] <= right_bound)
    ).strip()
    return descricao or fallback


def _parse_period_bounds(periodo: str) -> tuple[object | None, object | None]:
    from datetime import datetime

    inicio, fim = _extract_period_range(periodo or "")
    if not inicio or not fim:
        return None, None
    return (
        datetime.strptime(inicio, "%d/%m/%Y"),
        datetime.strptime(fim, "%d/%m/%Y"),
    )




def combinar_relatorios_caixa_mva(relatorios: list[dict]) -> dict:
    from datetime import datetime

    relatorios_validos = [
        rel
        for rel in relatorios
        if rel and (rel.get("caixa_modelo") or "").upper() == "MVA"
    ]
    if not relatorios_validos:
        return {
            "arquivo": "",
            "caixa_modelo": "MVA",
            "arquivo_tipo": "mva_davs_combinado",
            "periodo": None,
            "pedidos_total": 0,
            "pedidos_balcao": 0,
            "pedidos_caixa": 0,
            "pedidos_excluidos": 0,
            "pedidos_excluidos_cliente": 0,
            "pedidos_excluidos_documento": 0,
            "pedidos_editando": 0,
            "pedidos_outros_status": 0,
            "total_documento": 0.0,
            "total_excluido": 0.0,
            "total_caixa": 0.0,
            "itens_caixa": [],
            "itens_excluidos": [],
        }

    datas_inicio = []
    datas_fim = []
    for relatorio in relatorios_validos:
        inicio, fim = _parse_period_bounds(relatorio.get("periodo", ""))
        if inicio:
            datas_inicio.append(inicio)
        if fim:
            datas_fim.append(fim)

    periodo = None
    if datas_inicio and datas_fim:
        periodo = (
            f"{min(datas_inicio).strftime('%d/%m/%Y')} - "
            f"{max(datas_fim).strftime('%d/%m/%Y')}"
        )

    itens_caixa = []
    itens_excluidos = []
    for relatorio in relatorios_validos:
        for item in relatorio.get("itens_caixa", []):
            itens_caixa.append({**item})
        for item in relatorio.get("itens_excluidos", []):
            itens_excluidos.append({**item})

    return {
        "arquivo": " + ".join(relatorio.get("arquivo") or "-" for relatorio in relatorios_validos),
        "caixa_modelo": "MVA",
        "arquivo_tipo": "mva_davs_combinado",
        "periodo": periodo,
        "pedidos_total": sum(relatorio.get("pedidos_total", 0) for relatorio in relatorios_validos),
        "pedidos_balcao": 0,
        "pedidos_caixa": sum(relatorio.get("pedidos_caixa", 0) for relatorio in relatorios_validos),
        "pedidos_excluidos": sum(relatorio.get("pedidos_excluidos", 0) for relatorio in relatorios_validos),
        "pedidos_excluidos_cliente": 0,
        "pedidos_excluidos_documento": 0,
        "pedidos_editando": sum(relatorio.get("pedidos_editando", 0) for relatorio in relatorios_validos),
        "pedidos_outros_status": sum(relatorio.get("pedidos_outros_status", 0) for relatorio in relatorios_validos),
        "total_documento": round(
            sum(float(relatorio.get("total_documento", 0.0)) for relatorio in relatorios_validos),
            2,
        ),
        "total_excluido": round(
            sum(float(relatorio.get("total_excluido", 0.0)) for relatorio in relatorios_validos),
            2,
        ),
        "total_caixa": round(
            sum(float(relatorio.get("total_caixa", 0.0)) for relatorio in relatorios_validos),
            2,
        ),
        "itens_caixa": sorted(
            itens_caixa,
            key=lambda item: (str(item.get("ordem") or ""), item.get("pedido", "")),
        ),
        "itens_excluidos": sorted(
            itens_excluidos,
            key=lambda item: (
                str(item.get("ordem") or ""),
                item.get("documento", ""),
                item.get("origem_mva", ""),
                item.get("pedido", ""),
            ),
        ),
    }


def validar_arquivo_caixa_mva(relatorio: dict, arquivo_tipo_esperado: str) -> tuple[bool, str]:
    if relatorio and relatorio.get("pdf_sem_texto"):
        return False, _pdf_sem_texto_message(relatorio.get("arquivo"))

    if not relatorio or (relatorio.get("caixa_modelo") or "").upper() != "MVA":
            return False, "O arquivo selecionado não parece ser um relatório de Caixa MVA."

    if arquivo_tipo_esperado == "exportacao_dados_mva":
        if relatorio.get("arquivo_tipo") != "exportacao_dados_mva":
            return False, "O arquivo selecionado no passo 1 não parece ser a Exportação de dados da MVA."
    elif arquivo_tipo_esperado == "orcamentos_mva":
        if relatorio.get("arquivo_tipo") != "orcamentos_mva":
            return False, "O arquivo selecionado no passo 2 não parece ser o relatório de Orçamentos da MVA."

    if relatorio.get("pedidos_total", 0) <= 0:
        return False, "O arquivo selecionado não trouxe nenhum DAV válido."
    return True, ""




def _normalize_fiscal_number(numero: str) -> str:
    digits = re.sub(r"\D", "", str(numero or ""))
    if not digits:
        return ""
    return digits.zfill(9)


def _display_fiscal_number(numero: str) -> str:
    normalized = _normalize_fiscal_number(numero)
    if not normalized:
        return ""
    return str(int(normalized))


def _extract_period_range(periodo: str) -> tuple[str | None, str | None]:
    match = re.search(r"(\d{2}/\d{2}/\d{4})\s*-\s*(\d{2}/\d{2}/\d{4})", periodo or "")
    if not match:
        return None, None
    return match.group(1), match.group(2)


def _parse_scope_datetime(value: object) -> datetime | None:
    text = corrigir_texto(str(value or "")).strip()
    if not text:
        return None

    normalized = _normalize_ascii_text(text)
    for fmt in (
        "%d/%m/%Y %H:%M:%S",
        "%d/%m/%Y %H:%M",
        "%Y-%m-%d %H:%M:%S",
        "%Y-%m-%d %H:%M",
    ):
        try:
            return datetime.strptime(normalized, fmt)
        except ValueError:
            continue

    match = re.search(
        r"(\d{2}/\d{2}/\d{4})\s*(?:as\s*)?(\d{2}:\d{2})(?::(\d{2}))?",
        normalized,
        re.IGNORECASE,
    )
    if match:
        seconds = match.group(3) or "00"
        try:
            return datetime.strptime(
                f"{match.group(1)} {match.group(2)}:{seconds}",
                "%d/%m/%Y %H:%M:%S",
            )
        except ValueError:
            return None

    return None


def _build_scope_window(abertura: object, fechamento: object) -> dict | None:
    abertura_dt = _parse_scope_datetime(abertura)
    fechamento_dt = _parse_scope_datetime(fechamento)
    if not abertura_dt or not fechamento_dt or fechamento_dt < abertura_dt:
        return None
    return {
        "abertura": abertura_dt.strftime("%d/%m/%Y %H:%M:%S"),
        "fechamento": fechamento_dt.strftime("%d/%m/%Y %H:%M:%S"),
    }


def _normalize_scope_windows(windows: object) -> list[dict]:
    normalized: list[dict] = []
    seen: set[tuple[str, str]] = set()
    for raw in list(windows or []):
        if isinstance(raw, dict):
            opening = raw.get("abertura")
            closing = raw.get("fechamento")
        elif isinstance(raw, (list, tuple)) and len(raw) >= 2:
            opening, closing = raw[0], raw[1]
        else:
            continue
        window = _build_scope_window(opening, closing)
        if not window:
            continue
        key = (window["abertura"], window["fechamento"])
        if key in seen:
            continue
        seen.add(key)
        normalized.append(window)
    normalized.sort(key=lambda item: (item["abertura"], item["fechamento"]))
    return normalized


def _scope_window_datetimes(window: dict) -> tuple[datetime | None, datetime | None]:
    return _parse_scope_datetime(window.get("abertura")), _parse_scope_datetime(window.get("fechamento"))


def _is_overnight_afternoon_window(window: dict) -> bool:
    opening_dt, closing_dt = _scope_window_datetimes(window)
    return bool(
        opening_dt
        and closing_dt
        and opening_dt.date() < closing_dt.date()
        and opening_dt.hour >= 12
    )


def _is_afternoon_scope_window(window: dict) -> bool:
    opening_dt, closing_dt = _scope_window_datetimes(window)
    return bool(
        opening_dt
        and closing_dt
        and (
            _is_overnight_afternoon_window(window)
            or (opening_dt.date() == closing_dt.date() and opening_dt.hour >= 12)
        )
    )


def _is_partial_scope_windows(windows: object) -> bool:
    normalized = _normalize_scope_windows(windows)
    if not normalized:
        return False
    if len(normalized) > 1:
        return False
    opening_dt, closing_dt = _scope_window_datetimes(normalized[0])
    if not opening_dt or not closing_dt:
        return False
    duration_hours = max(0.0, (closing_dt - opening_dt).total_seconds() / 3600.0)
    if duration_hours >= 8.5 and opening_dt.hour <= 10 and closing_dt.hour >= 16:
        return False
    return True


def _report_scope_windows(report: dict | None) -> list[dict]:
    return _normalize_scope_windows((report or {}).get("fechamento_janelas"))


def _scope_window_key(window: dict | None) -> tuple[str, str]:
    window = window or {}
    return (
        str(window.get("abertura") or "").strip(),
        str(window.get("fechamento") or "").strip(),
    )


def _scope_windows_for_mode(windows: object, mode: str | None) -> list[dict]:
    normalized = _normalize_scope_windows(windows)
    mode_norm = _normalize_ascii_text(mode or "")
    if not normalized or mode_norm in {"", "daily", "diario"}:
        return normalized
    scoped_windows = list(normalized)
    if len(scoped_windows) > 2:
        opening_dt, closing_dt = _scope_window_datetimes(scoped_windows[0])
        if opening_dt and closing_dt:
            first_duration_minutes = (closing_dt - opening_dt).total_seconds() / 60.0
            if 0 <= first_duration_minutes <= 10.0:
                scoped_windows = scoped_windows[1:]
    if mode_norm in {"morning", "manha"}:
        if len(scoped_windows) == 1 and _is_afternoon_scope_window(scoped_windows[0]):
            return []
        return scoped_windows[:1]
    if mode_norm in {"afternoon", "tarde"}:
        if len(scoped_windows) == 1 and _is_afternoon_scope_window(scoped_windows[0]):
            return scoped_windows
        return scoped_windows[1:] if len(scoped_windows) > 1 else []
    return normalized


def _detect_closing_scope_kind(report: dict | None) -> str:
    windows = _report_scope_windows(report)
    if not windows:
        return "daily"
    if len(windows) > 1:
        return "daily"
    opening_dt, closing_dt = _scope_window_datetimes(windows[0])
    if _is_afternoon_scope_window(windows[0]):
        return "afternoon"
    if opening_dt and closing_dt and closing_dt.hour < 15:
        return "morning"
    return "partial"


def describe_closing_scope(report: dict | None) -> dict:
    windows = _report_scope_windows(report)
    detected = _detect_closing_scope_kind(report)
    available_modes = ["daily"]
    if windows:
        if len(windows) == 1:
            available_modes = [detected] if detected in {"morning", "afternoon"} else ["daily"]
        else:
            available_modes = ["daily", "morning", "afternoon"]
    return {
        "detected": detected,
        "windows": windows,
        "available_modes": available_modes,
        "has_morning_only": detected == "morning",
        "has_afternoon_only": detected == "afternoon",
        "has_full_day": len(windows) > 1,
    }


def _scope_mode_label(mode: str | None) -> str:
    mode_norm = _normalize_ascii_text(mode or "")
    if mode_norm in {"morning", "manha"}:
        return "Manhã"
    if mode_norm in {"afternoon", "tarde"}:
        return "Tarde"
    return "Diário"


def _item_within_scope_windows(item: dict, windows: list[dict]) -> bool:
    if not windows:
        return True
    item_scope_key = _scope_window_key(
        {
            "abertura": (item or {}).get("scope_abertura"),
            "fechamento": (item or {}).get("scope_fechamento"),
        }
    )
    if any(item_scope_key):
        valid_scope_keys = {_scope_window_key(window) for window in windows}
        return item_scope_key in valid_scope_keys
    item_dt = _parse_scope_datetime((item or {}).get("ordem")) or _parse_scope_datetime((item or {}).get("data_venda"))
    if item_dt is None:
        return True
    for window in windows:
        opening_dt, closing_dt = _scope_window_datetimes(window)
        if opening_dt and closing_dt and opening_dt <= item_dt <= closing_dt:
            return True
    return False


def _filter_payment_report_to_scope(report: dict | None, windows: list[dict]) -> dict | None:
    if not report:
        return report
    normalized_windows = _normalize_scope_windows(windows)
    if not normalized_windows:
        return report

    filtered = dict(report)
    items = [dict(item) for item in list(report.get("itens_autorizados") or []) if _item_within_scope_windows(item, normalized_windows)]
    filtered["itens_autorizados"] = items
    filtered["quantidade_autorizados"] = len(items)
    filtered["total_autorizado"] = round(sum(float(item.get("valor_bruto", 0.0) or 0.0) for item in items), 2)

    if "itens_todos" in report:
        all_items = [dict(item) for item in list(report.get("itens_todos") or []) if _item_within_scope_windows(item, normalized_windows)]
        filtered["itens_todos"] = all_items

    if "quantidade_relatorio" in filtered:
        filtered["quantidade_relatorio"] = len(items)
    if "total_relatorio" in filtered:
        filtered["total_relatorio"] = filtered["total_autorizado"]

    if filtered.get("quantidade_autorizados", 0) <= 0 and filtered.get("empty_message"):
        filtered["mensagem"] = filtered.get("empty_message")
    filtered["escopo_horario_aplicado"] = list(normalized_windows)
    return filtered


def _filter_items_to_scope(items: list[dict] | None, windows: list[dict]) -> list[dict]:
    normalized_windows = _normalize_scope_windows(windows)
    if not normalized_windows:
        return [dict(item) for item in list(items or [])]
    return [
        dict(item)
        for item in list(items or [])
        if _item_within_scope_windows(item, normalized_windows)
    ]


def _derive_scope_numbers(items: list[dict]) -> set[str]:
    numbers: set[str] = set()
    for item in items:
        numero = _normalize_fiscal_number(item.get("numero") or item.get("pedido") or "")
        if numero:
            numbers.add(numero)
    return numbers


def _is_eh_cancelled_excluded_item(item: dict) -> bool:
    motivo = corrigir_texto(str((item or {}).get("motivo", ""))).casefold()
    documento = _normalize_caixa_client((item or {}).get("documento", ""))
    return "cupom cancelado" in motivo or "CANCELADA" in documento


def _filter_eh_caixa_report_to_scope(relatorio_caixa: dict, relatorio_fechamento: dict, windows: list[dict]) -> dict:
    filtered = dict(relatorio_caixa or {})
    scoped_nfces = list(relatorio_fechamento.get("nfces") or [])
    scoped_numbers = _derive_scope_numbers(scoped_nfces)
    scoped_ints = sorted(int(numero) for numero in scoped_numbers if numero.isdigit())
    min_num = scoped_ints[0] if scoped_ints else None
    max_num = scoped_ints[-1] if scoped_ints else None

    def _item_in_scope(item: dict) -> bool:
        numero = _normalize_fiscal_number(item.get("pedido", ""))
        if not numero or not numero.isdigit():
            return False
        if numero in scoped_numbers:
            return True
        if min_num is None or max_num is None:
            return False
        numero_int = int(numero)
        return min_num <= numero_int <= max_num

    itens_caixa = [dict(item) for item in list(relatorio_caixa.get("itens_caixa") or []) if _item_in_scope(item)]
    itens_excluidos = [dict(item) for item in list(relatorio_caixa.get("itens_excluidos") or []) if _item_in_scope(item)]

    pedidos_balcao = len(
        [
            item
            for item in itens_caixa
            if _is_eh_counter_client(item.get("cliente", ""))
        ]
    )
    pedidos_excluidos_cliente = len(
        [
            item
            for item in itens_excluidos
            if "CLIENTE DIFERENTE" in _normalize_caixa_client(item.get("motivo", ""))
        ]
    )
    pedidos_excluidos_documento = len(
        [
            item
            for item in itens_excluidos
            if "NF-E" in _normalize_caixa_client(item.get("motivo", ""))
        ]
    )
    total_caixa = round(sum(float(item.get("valor", 0.0) or 0.0) for item in itens_caixa), 2)
    total_excluido = round(sum(float(item.get("valor", 0.0) or 0.0) for item in itens_excluidos), 2)
    itens_cancelados = [item for item in itens_excluidos if _is_eh_cancelled_excluded_item(item)]
    total_cancelados = round(sum(float(item.get("valor", 0.0) or 0.0) for item in itens_cancelados), 2)

    filtered.update(
        {
            "pedidos_total": len(itens_caixa) + len(itens_excluidos),
            "pedidos_balcao": pedidos_balcao,
            "pedidos_caixa": len(itens_caixa),
            "pedidos_excluidos": len(itens_excluidos),
            "pedidos_excluidos_cliente": pedidos_excluidos_cliente,
            "pedidos_excluidos_documento": pedidos_excluidos_documento,
            "pedidos_excluidos_cancelados": len(itens_cancelados),
            "total_documento": round(total_caixa + total_excluido, 2),
            "total_excluido": total_excluido,
            "total_excluido_cancelados": total_cancelados,
            "total_caixa": total_caixa,
            "itens_caixa": sorted(
                itens_caixa,
                key=lambda item: (item.get("pedido", ""), str(item.get("cliente", "")).casefold()),
            ),
            "itens_excluidos": sorted(
                itens_excluidos,
                key=lambda item: (-float(item.get("valor", 0.0) or 0.0), str(item.get("cliente", "")).casefold(), item.get("pedido", "")),
            ),
            "escopo_horario_aplicado": list(_normalize_scope_windows(windows)),
        }
    )
    return filtered


def _filter_generic_caixa_report_to_scope(relatorio_caixa: dict, windows: list[dict]) -> dict:
    filtered = dict(relatorio_caixa or {})
    itens_caixa = _filter_items_to_scope(relatorio_caixa.get("itens_caixa") or [], windows)
    itens_excluidos = _filter_items_to_scope(relatorio_caixa.get("itens_excluidos") or [], windows)
    total_caixa = round(sum(float(item.get("valor", 0.0) or 0.0) for item in itens_caixa), 2)
    total_excluido = round(sum(float(item.get("valor", 0.0) or 0.0) for item in itens_excluidos), 2)
    pedidos_editando = len(
        [
            item
            for item in itens_excluidos
            if _normalize_caixa_client(item.get("documento", "")) == "EDITANDO"
        ]
    )
    pedidos_outros_status = max(0, len(itens_excluidos) - pedidos_editando)
    filtered.update(
        {
            "pedidos_total": len(itens_caixa) + len(itens_excluidos),
            "pedidos_caixa": len(itens_caixa),
            "pedidos_excluidos": len(itens_excluidos),
            "pedidos_editando": pedidos_editando,
            "pedidos_outros_status": pedidos_outros_status,
            "total_documento": round(total_caixa + total_excluido, 2),
            "total_excluido": total_excluido,
            "total_caixa": total_caixa,
            "itens_caixa": sorted(itens_caixa, key=lambda item: item.get("pedido", "")),
            "itens_excluidos": sorted(
                itens_excluidos,
                key=lambda item: (item.get("documento", ""), item.get("origem_mva", ""), item.get("pedido", "")),
            ),
            "escopo_horario_aplicado": list(_normalize_scope_windows(windows)),
        }
    )
    return filtered


def _filter_fechamento_report_to_scope(relatorio_fechamento: dict, windows: list[dict]) -> dict:
    normalized_windows = _normalize_scope_windows(windows)
    if not normalized_windows:
        return dict(relatorio_fechamento or {})

    filtered = dict(relatorio_fechamento or {})
    nfces = _filter_items_to_scope(relatorio_fechamento.get("nfces") or [], normalized_windows)
    relatorios_pagamento = {}
    for key, report in dict(relatorio_fechamento.get("relatorios_pagamento") or {}).items():
        relatorios_pagamento[key] = _filter_payment_report_to_scope(report, normalized_windows)

    totalizadores = {}
    for report in relatorios_pagamento.values():
        if not isinstance(report, dict):
            continue
        titulo = str(report.get("forma_pagamento") or report.get("summary_label") or "").strip()
        if titulo:
            totalizadores[titulo] = round(float(report.get("total_autorizado", 0.0) or 0.0), 2)

    filtered.update(
        {
            "quantidade_nfce": len(nfces),
            "total_nfce": round(sum(float(item.get("valor", 0.0) or 0.0) for item in nfces), 2),
            "total_geral": round(sum(float(item.get("valor", 0.0) or 0.0) for item in nfces), 2),
            "nfces": sorted(
                nfces,
                key=lambda item: (
                    str(item.get("data_venda") or ""),
                    str(item.get("numero") or ""),
                ),
            ),
            "nfces_faltantes_sequencia": _find_missing_fiscal_numbers(
                [_normalize_fiscal_number(item.get("numero", "")) for item in nfces]
            ),
            "relatorios_pagamento": relatorios_pagamento,
            "fechamento_janelas": list(normalized_windows),
            "fechamento_parcial": _is_partial_scope_windows(normalized_windows),
            "totalizadores": totalizadores or dict(relatorio_fechamento.get("totalizadores") or {}),
            "escopo_horario_aplicado": list(normalized_windows),
        }
    )
    return filtered


def _zweb_fechamento_has_sales_outside_date(relatorio_fechamento: dict, data_br: str) -> bool:
    target_date = str(data_br or "").strip()
    if not target_date:
        return False

    dates: set[str] = set()
    for item in list((relatorio_fechamento or {}).get("nfces") or []):
        data_venda = str((item or {}).get("data_venda") or "").strip()
        if data_venda:
            dates.add(data_venda)

    for report in dict((relatorio_fechamento or {}).get("relatorios_pagamento") or {}).values():
        if not isinstance(report, dict):
            continue
        for item in list(report.get("itens_autorizados") or []):
            data_venda = str((item or {}).get("data_venda") or "").strip()
            if data_venda:
                dates.add(data_venda)

    return bool(dates and any(data_venda != target_date for data_venda in dates))


def _filter_zweb_fechamento_to_sales_date(relatorio_fechamento: dict, data_br: str) -> dict:
    target_date = str(data_br or "").strip()
    if not target_date:
        return relatorio_fechamento

    filtered = dict(relatorio_fechamento or {})
    nfces = [
        dict(item)
        for item in list((relatorio_fechamento or {}).get("nfces") or [])
        if str(item.get("data_venda") or "").strip() == target_date
    ]
    relatorios_pagamento = {}
    relevant_scope_keys: set[tuple[str, str]] = set()

    for item in nfces:
        key = _scope_window_key(
            {
                "abertura": item.get("scope_abertura"),
                "fechamento": item.get("scope_fechamento"),
            }
        )
        if any(key):
            relevant_scope_keys.add(key)

    for report_key, report in dict((relatorio_fechamento or {}).get("relatorios_pagamento") or {}).items():
        if not isinstance(report, dict):
            continue
        report_copy = dict(report)
        items = [
            dict(item)
            for item in list(report.get("itens_autorizados") or [])
            if str(item.get("data_venda") or "").strip() == target_date
        ]
        for item in items:
            key = _scope_window_key(
                {
                    "abertura": item.get("scope_abertura"),
                    "fechamento": item.get("scope_fechamento"),
                }
            )
            if any(key):
                relevant_scope_keys.add(key)
        report_copy["itens_autorizados"] = items
        report_copy["quantidade_autorizados"] = len(items)
        report_copy["quantidade_relatorio"] = len(items)
        total = round(sum(float(item.get("valor_bruto", 0.0) or 0.0) for item in items), 2)
        report_copy["total_autorizado"] = total
        report_copy["total_relatorio"] = total
        if total <= 0.009 and report_copy.get("empty_message"):
            report_copy["mensagem"] = report_copy.get("empty_message")
        relatorios_pagamento[report_key] = report_copy

    original_windows = _normalize_scope_windows((relatorio_fechamento or {}).get("fechamento_janelas"))
    if relevant_scope_keys:
        fechamento_janelas = [
            window
            for window in original_windows
            if _scope_window_key(window) in relevant_scope_keys
        ]
    else:
        fechamento_janelas = []

    totalizadores = {}
    for report in relatorios_pagamento.values():
        titulo = str(report.get("forma_pagamento") or report.get("summary_label") or "").strip()
        if titulo:
            totalizadores[titulo] = round(float(report.get("total_autorizado", 0.0) or 0.0), 2)

    filtered.update(
        {
            "periodo": f"{target_date} - {target_date}",
            "quantidade_nfce": len(nfces),
            "total_nfce": round(sum(float(item.get("valor", 0.0) or 0.0) for item in nfces), 2),
            "total_geral": round(sum(float(item.get("valor", 0.0) or 0.0) for item in nfces), 2),
            "nfces": sorted(
                nfces,
                key=lambda item: (
                    str(item.get("data_venda") or ""),
                    str(item.get("numero") or ""),
                ),
            ),
            "nfces_faltantes_sequencia": _find_missing_fiscal_numbers(
                [_normalize_fiscal_number(item.get("numero", "")) for item in nfces]
            ),
            "relatorios_pagamento": relatorios_pagamento,
            "fechamento_janelas": fechamento_janelas,
            "fechamento_parcial": _is_partial_scope_windows(fechamento_janelas),
            "totalizadores": totalizadores,
            "fechamento_data_venda_filtrada": target_date,
        }
    )
    return filtered


def aplicar_escopo_relatorio_caixa(
    relatorio_caixa: dict,
    relatorio_fechamento: dict,
    relatorio_pix: dict | None = None,
    *,
    scope_mode: str | None = None,
) -> tuple[dict, dict, dict | None]:
    windows = _scope_windows_for_mode((relatorio_fechamento or {}).get("fechamento_janelas"), scope_mode)
    mode_norm = _normalize_ascii_text(scope_mode or "")
    if not windows or mode_norm in {"", "daily", "diario"}:
        caixa_copy = dict(relatorio_caixa or {})
        fechamento_copy = dict(relatorio_fechamento or {})
        pix_copy = dict(relatorio_pix) if isinstance(relatorio_pix, dict) else relatorio_pix
        for report in (caixa_copy, fechamento_copy, pix_copy):
            if isinstance(report, dict):
                report["escopo_relatorio"] = _scope_mode_label(scope_mode)
        return caixa_copy, fechamento_copy, pix_copy

    fechamento_filtrado = _filter_fechamento_report_to_scope(relatorio_fechamento, windows)
    if str((relatorio_caixa or {}).get("caixa_modelo") or "").upper() == "MVA":
        caixa_filtrado = _filter_generic_caixa_report_to_scope(relatorio_caixa, windows)
    else:
        caixa_filtrado = _filter_eh_caixa_report_to_scope(relatorio_caixa, fechamento_filtrado, windows)
    pix_filtrado = _filter_payment_report_to_scope(relatorio_pix, windows) if relatorio_pix else relatorio_pix

    escopo_label = _scope_mode_label(scope_mode)
    for report in (caixa_filtrado, fechamento_filtrado, pix_filtrado):
        if isinstance(report, dict):
            report["escopo_relatorio"] = escopo_label
            report["escopo_horario_aplicado"] = list(windows)

    return caixa_filtrado, fechamento_filtrado, pix_filtrado


def _period_to_iso_date(periodo: str) -> str | None:
    inicio, fim = _extract_period_range(periodo or "")
    if not inicio or not fim or inicio != fim:
        return None
    try:
        return datetime.strptime(inicio, "%d/%m/%Y").strftime("%Y-%m-%d")
    except ValueError:
        return None


def _iso_to_br_date(data_iso: str) -> str | None:
    try:
        return datetime.strptime(data_iso, "%Y-%m-%d").strftime("%d/%m/%Y")
    except ValueError:
        return None


def _period_from_br_dates(datas: list[str]) -> str | None:
    datas_validas = []
    for data_str in datas:
        try:
            datas_validas.append(datetime.strptime(str(data_str).strip(), "%d/%m/%Y"))
        except ValueError:
            continue

    if not datas_validas:
        return None

    inicio = min(datas_validas).strftime("%d/%m/%Y")
    fim = max(datas_validas).strftime("%d/%m/%Y")
    return f"{inicio} - {fim}"


def _runtime_user_dir() -> str:
    return _project_base_dir()


def _canonical_runtime_dir() -> Path:
    canonical = Path(r"D:\pdfReader")
    if canonical.is_dir():
        return canonical
    return Path(_runtime_user_dir())


def _runtime_file_path(filename: str, *, prefer_existing: bool = True) -> Path:
    candidates = [
        _canonical_runtime_dir() / filename,
        Path(_runtime_user_dir()) / filename,
        Path(_active_report_dir()) / filename,
    ]
    seen: set[str] = set()
    unique_candidates: list[Path] = []
    for candidate in candidates:
        key = str(candidate).casefold()
        if key in seen:
            continue
        seen.add(key)
        unique_candidates.append(candidate)
    if prefer_existing:
        for candidate in unique_candidates:
            if candidate.is_file():
                return candidate
    return unique_candidates[0]


def _zweb_browser_profile_dir() -> str:
    profile_dir = _canonical_runtime_dir() / "runtime" / "zweb_browser_profile"
    os.makedirs(profile_dir, exist_ok=True)
    return str(profile_dir)


def _load_zweb_credentials(*, account_index: int = 0) -> dict | None:
    if account_index < 0:
        return None

    for filename in ("credenciais.txt", "credencias.txt"):
        caminho = str(_runtime_file_path(filename))
        if not os.path.isfile(caminho):
            continue
        try:
            with open(caminho, "r", encoding="utf-8", errors="ignore") as arquivo:
                linhas = [linha.strip() for linha in arquivo.readlines() if linha.strip()]
        except OSError:
            continue

        account_sections = [
            marker_index
            for marker_index, linha in enumerate(linhas)
            if _normalize_caixa_client(linha) == "CONTA ZWEB:"
        ]
        if account_index >= len(account_sections):
            continue

        idx = account_sections[account_index]
        username = str(linhas[idx + 1] if len(linhas) > idx + 1 else "").strip()
        password = str(linhas[idx + 2] if len(linhas) > idx + 2 else "").strip()
        base_url = str(linhas[idx + 3] if len(linhas) > idx + 3 else "").strip().rstrip("/")
        if username and password and base_url.startswith("http"):
            return {
                "username": username,
                "password": password,
                "base_url": base_url,
                "sign_in_url": f"{base_url}/#/sign-in",
                "dashboard_url": f"{base_url}/#/dashboard",
                "finance_movimentations_url": f"{base_url}/#/finance/movimentations",
                "finance_reports_url": f"{base_url}/#/finance/reports",
                "document_reports_url": f"{base_url}/#/document/reports",
            }

    if account_index != 0:
        return None

    username = str(ZWEB_USERNAME or "").strip()
    password = str(ZWEB_PASSWORD or "").strip()
    base_url = str(ZWEB_BASE_URL or "").strip().rstrip("/")
    if username and password and base_url.startswith("http"):
        return {
            "username": username,
            "password": password,
            "base_url": base_url,
            "sign_in_url": f"{base_url}/#/sign-in",
            "dashboard_url": f"{base_url}/#/dashboard",
            "finance_movimentations_url": f"{base_url}/#/finance/movimentations",
            "finance_reports_url": f"{base_url}/#/finance/reports",
            "document_reports_url": f"{base_url}/#/document/reports",
        }
    return None


def _find_chromium_browser_path() -> str | None:
    env_candidates = [
        os.environ.get("CHROMIUM_PATH"),
        os.environ.get("CHROME_PATH"),
        os.environ.get("EDGE_PATH"),
    ]
    common_paths = [
        r"C:\Program Files\Google\Chrome\Application\chrome.exe",
        r"C:\Program Files (x86)\Google\Chrome\Application\chrome.exe",
        r"C:\Program Files\Chromium\Application\chrome.exe",
        r"C:\Program Files (x86)\Chromium\Application\chrome.exe",
        r"C:\Program Files\Microsoft\Edge\Application\msedge.exe",
        r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe",
    ]

    for caminho in [*env_candidates, *common_paths]:
        caminho = str(caminho or "").strip()
        if caminho and os.path.isfile(caminho):
            return caminho
    return None


def _pick_free_local_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _wait_for_devtools_ready(port: int, timeout: float = 60.0) -> dict:
    import urllib.request
    import urllib.error
    deadline = time.time() + timeout
    last_exc = None

    while time.time() < deadline:
        try:
            resposta = requests.get(f"http://127.0.0.1:{port}/json/version", timeout=3)
            resposta.raise_for_status()
            return resposta.json() or {}
        except Exception as exc:
            last_exc = exc
            time.sleep(1.0)

    raise RuntimeError(f"Não foi possível iniciar o Chromium para gerar o relatório PIX: {last_exc}")


def _emit_pix_status(on_status, message: str) -> None:
    if callable(on_status):
        try:
            on_status(str(message or "").strip())
        except Exception:
            pass


def _prepare_chromium_profile(profile_dir: str, download_dir: str) -> None:
    default_dir = os.path.join(profile_dir, "Default")
    os.makedirs(default_dir, exist_ok=True)

    for lock_name in (
        "SingletonCookie",
        "SingletonLock",
        "SingletonSocket",
        "DevToolsActivePort",
        "lockfile",
    ):
        lock_path = os.path.join(profile_dir, lock_name)
        try:
            if os.path.exists(lock_path):
                os.remove(lock_path)
        except OSError:
            pass
        default_lock_path = os.path.join(default_dir, lock_name)
        try:
            if os.path.exists(default_lock_path):
                os.remove(default_lock_path)
        except OSError:
            pass

    prefs_path = os.path.join(default_dir, "Preferences")
    prefs = {
        "credentials_enable_service": False,
        "autofill": {
            "enabled": False,
        },
        "download": {
            "default_directory": download_dir,
            "prompt_for_download": False,
        },
        "profile": {
            "password_manager_enabled": False,
            "default_content_setting_values": {
                "geolocation": 2,
                "notifications": 2,
            },
        },
    }

    try:
        with open(prefs_path, "w", encoding="utf-8") as arquivo:
            json.dump(prefs, arquivo)
    except OSError:
        pass


def _launch_browser_process(chrome_args: list[str]) -> subprocess.Popen:
    popen_kwargs = {
        "stdin": subprocess.DEVNULL,
        "stdout": subprocess.DEVNULL,
        "stderr": subprocess.DEVNULL,
    }
    return subprocess.Popen(chrome_args, **popen_kwargs)


async def _hide_chromium_window(cdp, target_id: str) -> None:
    if not target_id:
        return
    try:
        window_info = await cdp("Browser.getWindowForTarget", {"targetId": target_id}, timeout=5.0)
    except Exception:
        return

    window_id = window_info.get("windowId")
    if not window_id:
        return

    try:
        await cdp(
            "Browser.setWindowBounds",
            {
                "windowId": window_id,
                "bounds": {
                    "left": -32000,
                    "top": 0,
                    "width": 1400,
                    "height": 900,
                },
            },
            timeout=5.0,
        )
    except Exception:
        pass

    try:
        await cdp(
            "Browser.setWindowBounds",
            {"windowId": window_id, "bounds": {"state": "minimized"}},
            timeout=5.0,
        )
    except Exception:
        pass


async def _show_chromium_window(cdp, target_id: str) -> None:
    if not target_id:
        return
    try:
        window_info = await cdp("Browser.getWindowForTarget", {"targetId": target_id}, timeout=5.0)
    except Exception:
        return

    window_id = window_info.get("windowId")
    if not window_id:
        return

    try:
        await cdp(
            "Browser.setWindowBounds",
            {"windowId": window_id, "bounds": {"state": "normal"}},
            timeout=5.0,
        )
        await cdp(
            "Browser.setWindowBounds",
            {
                "windowId": window_id,
                "bounds": {"left": 40, "top": 40, "width": 1400, "height": 900},
            },
            timeout=5.0,
        )
    except Exception:
        pass


def gerar_relatorios_caixa_eh_zweb(
    data_br: str,
    on_status=None,
    cancel_event: threading.Event | None = None,
    token_callback=None,
    force_refresh_payments: bool = False,
    fechamento_data_inicio_br: str | None = None,
    fechamento_data_fim_br: str | None = None,
    filtrar_fechamento_por_data_venda: bool = False,
    scope_mode: str | None = None,
) -> tuple[dict, dict, dict]:
    cancel_event = cancel_event or threading.Event()

    def _check_cancelled() -> None:
        if cancel_event.is_set():
            raise RuntimeError("__cancelled__")

    credenciais = _load_zweb_credentials(account_index=1)
    if not credenciais:
        raise ValueError("As credenciais do Zweb não foram encontradas no credenciais.txt.")

    try:
        data_iso = datetime.strptime(str(data_br or "").strip(), "%d/%m/%Y").strftime("%Y-%m-%d")
    except ValueError as exc:
        raise ValueError("A data do Caixa EH e invalida.") from exc

    fechamento_data_inicio_br = str(fechamento_data_inicio_br or data_br or "").strip()
    fechamento_data_fim_br = str(fechamento_data_fim_br or fechamento_data_inicio_br or "").strip()
    try:
        datetime.strptime(fechamento_data_inicio_br, "%d/%m/%Y")
        datetime.strptime(fechamento_data_fim_br, "%d/%m/%Y")
    except ValueError as exc:
        raise ValueError("A data do Fechamento de caixa do Zweb e invalida.") from exc

    local_payment_reports = _find_eh_local_payment_reports(data_br)
    local_pix_pdf = local_payment_reports.get("pix")
    local_card_pdf = local_payment_reports.get("cartoes")
    avisos_usuario: list[str] = list(local_payment_reports.get("avisos") or [])

    if force_refresh_payments or not local_pix_pdf or not local_card_pdf:
        try:
            baixados = baixar_relatorios_caixa_eh_azulzinha(
                data_br,
                on_status=on_status,
                cancel_event=cancel_event,
                token_callback=token_callback,
                need_pix=force_refresh_payments or not bool(local_pix_pdf),
                need_cartoes=force_refresh_payments or not bool(local_card_pdf),
            )
            if baixados.get("pix"):
                local_pix_pdf = baixados.get("pix")
            if baixados.get("cartoes"):
                local_card_pdf = baixados.get("cartoes")
            avisos_usuario.extend(baixados.get("avisos") or [])
        except Exception as exc:
            if str(exc).strip() == "__cancelled__":
                raise
            avisos_usuario.append(f"Não foi possível baixar automaticamente os relatórios da Caixa: {exc}")

    navegador = _find_chromium_browser_path()
    if not navegador:
        raise RuntimeError("Nenhum navegador Chromium compativel foi encontrado para acessar o Zweb.")

    profile_root = _zweb_browser_profile_dir()
    profile_dir = ""
    port = 0
    proc = None

    async def _run() -> tuple[str, str, dict, list[dict], str | None]:
        import websockets

        _check_cancelled()
        meta = _wait_for_devtools_ready(port)
        ws_url = str(meta.get("webSocketDebuggerUrl") or "").strip()
        if not ws_url:
            raise RuntimeError("Não foi possível conectar ao Chromium para acessar o Zweb.")

        async with websockets.connect(ws_url, max_size=50_000_000) as conn:
            next_id = 0
            pending = {}

            async def recv_loop():
                while True:
                    _check_cancelled()
                    mensagem = json.loads(await conn.recv())
                    if "id" in mensagem and mensagem["id"] in pending:
                        pending.pop(mensagem["id"]).set_result(mensagem)

            recv_task = asyncio.create_task(recv_loop())

            async def cdp(method: str, params: dict | None = None, session_id: str | None = None, timeout: float = 60.0):
                nonlocal next_id
                _check_cancelled()
                next_id += 1
                future = asyncio.get_running_loop().create_future()
                pending[next_id] = future
                mensagem = {"id": next_id, "method": method}
                if params:
                    mensagem["params"] = params
                if session_id:
                    mensagem["sessionId"] = session_id
                await conn.send(json.dumps(mensagem))
                resposta = await asyncio.wait_for(future, timeout)
                if "error" in resposta:
                    raise RuntimeError(resposta["error"])
                return resposta.get("result", {})

            async def eval_js(session_id: str, expression: str):
                _check_cancelled()
                resposta = await cdp(
                    "Runtime.evaluate",
                    {
                        "expression": expression,
                        "returnByValue": True,
                        "awaitPromise": True,
                    },
                    session_id=session_id,
                )
                return resposta.get("result", {}).get("value")

            async def wait_for_condition(session_id: str, expression: str, timeout: float = 60.0, step: float = 0.4):
                deadline = time.time() + timeout
                last_value = None
                while time.time() < deadline:
                    _check_cancelled()
                    try:
                        last_value = await eval_js(session_id, expression)
                        if last_value:
                            return last_value
                    except Exception as exc:
                        last_value = str(exc)
                    await asyncio.sleep(step)
                raise TimeoutError(f"{expression} :: ultimo retorno={last_value!r}")

            async def open_route(session_id: str, url: str, ready_text: str) -> None:
                _check_cancelled()
                await cdp("Page.navigate", {"url": url}, session_id=session_id)
                await wait_for_condition(session_id, "document.readyState === 'complete'", timeout=60.0)
                await wait_for_condition(
                    session_id,
                    f"""
                    (() => {{
                        const text = document.body ? document.body.innerText : '';
                        return location.href.includes({url.split('#', 1)[-1]!r}) || text.toUpperCase().includes({ready_text.upper()!r});
                    }})()
                    """,
                    timeout=60.0,
                )

            async def ensure_logged_in(session_id: str) -> None:
                _check_cancelled()
                _emit_pix_status(on_status, "Abrindo login do Zweb...")
                await cdp("Page.navigate", {"url": credenciais["sign_in_url"]}, session_id=session_id)
                await wait_for_condition(session_id, "document.readyState === 'complete'", timeout=60.0)
                estado_login = await wait_for_condition(
                    session_id,
                    "location.href.includes('/dashboard') || location.hash.includes('/dashboard') || document.querySelectorAll('input').length >= 2",
                    timeout=60.0,
                )
                if estado_login and await eval_js(
                    session_id,
                    "location.href.includes('/dashboard') || location.hash.includes('/dashboard')",
                ):
                    return
                _emit_pix_status(on_status, "Autenticando no Zweb...")
                await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const setNativeValue = (el, value) => {{
                            if (!el) return false;
                            const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                            setter.call(el, value);
                            el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            el.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                            return true;
                        }};
                        const inputs = [...document.querySelectorAll('input')];
                        const email = inputs.find((el) => (el.name || '').toLowerCase() === 'email') || inputs[0];
                        const password = inputs.find((el) => (el.type || '').toLowerCase() === 'password') || inputs[1];
                        if (!setNativeValue(email, {credenciais["username"]!r})) return false;
                        if (!setNativeValue(password, {credenciais["password"]!r})) return false;
                        const button = document.querySelector('button[type="submit"], button.btn-primary, button');
                        button?.click();
                        return true;
                    }})()
                    """,
                )
                _emit_pix_status(on_status, "Entrando no painel do Zweb...")
                await wait_for_condition(
                    session_id,
                    "location.href.includes('/dashboard') || location.hash.includes('/dashboard')",
                    timeout=90.0,
                )

            async def click_report_button(session_id: str, titulo: str) -> None:
                _check_cancelled()
                await wait_for_condition(
                    session_id,
                    f"""
                    (() => {{
                        const normalize = (value) =>
                            (value || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .replace(/\\s+/g, ' ')
                                .trim()
                                .toUpperCase();
                        const targetTitle = {titulo.upper()!r};
                        const rows = [...document.querySelectorAll('div.row.mb-5.p-4.bg-light.align-items-center.rounded')];
                        return rows.some((el) => normalize(el.innerText || el.textContent).includes(targetTitle));
                    }})()
                    """,
                    timeout=30.0,
                )
                clicked = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const normalize = (value) =>
                            (value || '')
                                .normalize('NFD')
                                .replace(/[\\u0300-\\u036f]/g, '')
                                .replace(/\\s+/g, ' ')
                                .trim()
                                .toUpperCase();
                        const targetTitle = {titulo.upper()!r};
                        const rows = [...document.querySelectorAll('div.row.mb-5.p-4.bg-light.align-items-center.rounded')];
                        const row = rows.find((el) => normalize(el.innerText || el.textContent).includes(targetTitle));
                        const button = row?.querySelector('button.btn.btn-primary.btn-sm');
                        if (!button) return false;
                        button.scrollIntoView({{ block: 'center', inline: 'center' }});
                        button.click();
                        return true;
                    }})()
                    """,
                )
                if not clicked:
                    raise RuntimeError(f"Não foi possível localizar o relatório {titulo} no Zweb.")

            async def wait_modal(session_id: str, titulo: str) -> None:
                _check_cancelled()
                await wait_for_condition(
                    session_id,
                    f"""
                    (() => {{
                        const modal = document.querySelector('.modal.show#modal-wrapper');
                        if (!modal) return false;
                        const text = (modal.innerText || '').toUpperCase();
                        return text.includes({titulo.upper()!r});
                    }})()
                    """,
                    timeout=30.0,
                )

            async def set_modal_period(
                session_id: str,
                from_selector: str,
                to_selector: str,
                start_date_br: str,
                end_date_br: str | None = None,
            ) -> None:
                _check_cancelled()
                end_date_br = end_date_br or start_date_br
                preenchido = await eval_js(
                    session_id,
                    f"""
                    (() => {{
                        const setValue = (selector, value) => {{
                            const input = document.querySelector(selector);
                            if (!input) return false;
                            const setter = Object.getOwnPropertyDescriptor(HTMLInputElement.prototype, 'value').set;
                            setter.call(input, value);
                            input.dispatchEvent(new Event('input', {{ bubbles: true }}));
                            input.dispatchEvent(new Event('change', {{ bubbles: true }}));
                            input.dispatchEvent(new Event('blur', {{ bubbles: true }}));
                            return true;
                        }};
                        const okFrom = setValue({from_selector!r}, {start_date_br!r});
                        const okTo = setValue({to_selector!r}, {end_date_br!r});
                        return okFrom && okTo;
                    }})()
                    """,
                )
                if not preenchido:
                    raise RuntimeError("Não foi possível preencher o período do relatório no Zweb.")

            async def ensure_html_format(session_id: str) -> None:
                _check_cancelled()
                await eval_js(
                    session_id,
                    """
                    (() => {
                        const radio = [...document.querySelectorAll('input[type="radio"]')]
                            .find((el) => String(el.value || '').toUpperCase() === 'HTML');
                        if (!radio) return true;
                        if (!radio.checked) {
                            radio.click();
                            radio.dispatchEvent(new Event('change', { bubbles: true }));
                        }
                        return true;
                    })()
                    """,
                )

            async def prepare_fechamento_filters(session_id: str) -> None:
                _check_cancelled()
                prepared = await eval_js(
                    session_id,
                    r"""
                    (() => {
                        const normalize = (value) =>
                            (value || '')
                                .normalize('NFD')
                                .replace(/[\u0300-\u036f]/g, '')
                                .replace(/\s+/g, ' ')
                                .trim()
                                .toUpperCase();

                        document.querySelectorAll('.multiselect__tag-icon').forEach((el) => el.click());

                        const multiselect = document.querySelector('.z-select-multiple .multiselect') || document.querySelector('.z-select-right-icon');
                        multiselect?.click();

                        const option = [...document.querySelectorAll('.multiselect__option')]
                            .find((el) => normalize(el.innerText || el.textContent).startsWith('001'));
                        if (!option) return false;
                        option.click();

                        const labelNode = [...document.querySelectorAll('label, span, div')]
                            .find((el) => normalize(el.innerText || el.textContent).includes('AGRUPAR POR FORMA DE PAGAMENTO'));
                        const containers = [
                            labelNode,
                            labelNode?.closest('label'),
                            labelNode?.closest('div'),
                            labelNode?.parentElement,
                            labelNode?.parentElement?.parentElement,
                        ].filter(Boolean);
                        let checkbox = null;
                        for (const container of containers) {
                            checkbox = container.querySelector?.('input[type="checkbox"]') || null;
                            if (checkbox) break;
                        }
                        if (checkbox && !checkbox.checked) checkbox.click();
                        return true;
                    })()
                    """,
                )
                if not prepared:
                    raise RuntimeError("Não foi possível selecionar o Caixa 001 no Zweb.")

            async def capture_report_url(session_id: str) -> str:
                _check_cancelled()
                await eval_js(
                    session_id,
                    """
                    (() => {
                        window.__codexReportUrl = '';
                        window.__codexOriginalOpen = window.__codexOriginalOpen || window.open;
                        window.open = function(url) {
                            window.__codexReportUrl = url || '';
                            return null;
                        };
                        return true;
                    })()
                    """,
                )
                clicked = await eval_js(
                    session_id,
                    """
                    (() => {
                        const button = document.querySelector('.modal.show#modal-wrapper .modal-footer button.btn.btn-primary');
                        if (!button) return false;
                        button.click();
                        return true;
                    })()
                    """,
                )
                if not clicked:
                    raise RuntimeError("Não foi possível confirmar a geração do relatório no Zweb.")

                return await wait_for_condition(
                    session_id,
                    """
                    (() => {
                        const direct = window.__codexReportUrl || '';
                        if (direct) return direct;
                        const resources = performance.getEntriesByType('resource') || [];
                        const entry = [...resources]
                            .reverse()
                            .find((item) => /\\/uploads\\/reports\\/report\\/.*\\.html/i.test(String(item && item.name || '')));
                        return entry ? entry.name : '';
                    })()
                    """,
                    timeout=60.0,
                )

            async def fetch_report_html(session_id: str, report_key: str) -> str:
                _check_cancelled()
                if report_key == "pedidos_importados":
                    _emit_pix_status(on_status, "Gerando Pedidos importados...")
                    await open_route(session_id, credenciais["document_reports_url"], "PEDIDOS IMPORTADOS")
                    await click_report_button(session_id, "Pedidos importados")
                    await wait_modal(session_id, "Pedidos importados")
                    await set_modal_period(session_id, "#from_date input.dp__input", "#to_date input.dp__input", data_br, data_br)
                    await ensure_html_format(session_id)
                else:
                    _emit_pix_status(on_status, "Gerando Fechamento de caixa...")
                    await open_route(session_id, credenciais["finance_reports_url"], "FECHAMENTO DE CAIXA")
                    await click_report_button(session_id, "Fechamento de caixa")
                    await wait_modal(session_id, "Fechamento de caixa")
                    await set_modal_period(
                        session_id,
                        "#fromDate input.dp__input",
                        "#toDate input.dp__input",
                        fechamento_data_inicio_br,
                        fechamento_data_fim_br,
                    )
                    await ensure_html_format(session_id)
                    await prepare_fechamento_filters(session_id)

                report_url = str(await capture_report_url(session_id) or "").strip()
                if not report_url:
                    raise RuntimeError("O Zweb não retornou a URL do relatório solicitado.")

                _check_cancelled()
                resposta = requests.get(report_url, timeout=90.0)
                resposta.raise_for_status()
                return _decode_report_response_text(resposta)

            async def fetch_fiscal_nfce_status_map(session_id: str) -> dict:
                _check_cancelled()
                _emit_pix_status(on_status, "Consultando Fiscal > NFC-e...")
                await open_route(session_id, f"{credenciais['base_url']}/#/fiscal/nfce", "NFC-E")

                itens_encontrados = []
                pagina = 1
                max_results = 100

                while pagina <= 30:
                    _check_cancelled()
                    payload = {
                        "modelos": ["65", "59"],
                        "page": pagina,
                        "maxResults": max_results,
                    }
                    resposta = await eval_js(
                        session_id,
                        f"""
                        (async () => {{
                            const token = localStorage.getItem('token') || '';
                            const response = await fetch('https://api.zweb.com.br/rpc/v2/fiscal.get-nfe-paginate', {{
                                method: 'POST',
                                credentials: 'include',
                                headers: {{
                                    'Accept': 'application/json',
                                    'Content-Type': 'application/json',
                                    ...(token ? {{ 'Authorization': `Bearer ${{token}}` }} : {{}})
                                }},
                                body: JSON.stringify({json.dumps(payload, ensure_ascii=False)})
                            }});
                            const text = await response.text();
                            return {{
                                ok: response.ok,
                                status: response.status,
                                text
                            }};
                        }})()
                        """,
                    )
                    status_code = int((resposta or {}).get("status") or 0)
                    if status_code >= 400:
                        raise RuntimeError(
                            f"O Zweb retornou erro ao consultar Fiscal > NFC-e ({status_code})."
                        )

                    try:
                        payload_resposta = json.loads((resposta or {}).get("text") or "{}")
                    except json.JSONDecodeError as exc:
                        raise RuntimeError(
                            "O Zweb retornou um JSON inválido ao consultar Fiscal > NFC-e."
                        ) from exc

                    pagina_itens = payload_resposta.get("data") or []
                    if not isinstance(pagina_itens, list) or not pagina_itens:
                        break

                    datas_pagina = []
                    for item in pagina_itens:
                        emissao_iso = _extract_zweb_fiscal_emission_iso(item.get("emission", ""))
                        if not emissao_iso:
                            continue
                        datas_pagina.append(emissao_iso)
                        if emissao_iso == data_iso:
                            itens_encontrados.append(item)

                    if not datas_pagina:
                        break

                    data_mais_antiga = min(datas_pagina)
                    if data_mais_antiga < data_iso:
                        break

                    pagina += 1

                return _build_zweb_fiscal_status_map(itens_encontrados)

            try:
                _check_cancelled()
                target_id = (await cdp("Target.createTarget", {"url": "about:blank"})).get("targetId")
                if not target_id:
                    raise RuntimeError("Não foi possível abrir a aba oculta do Zweb.")

                session_id = (await cdp("Target.attachToTarget", {"targetId": target_id, "flatten": True})).get("sessionId")
                if not session_id:
                    raise RuntimeError("Não foi possível anexar a aba oculta do Zweb.")

                await cdp("Page.enable", session_id=session_id)
                await cdp("Runtime.enable", session_id=session_id)

                _check_cancelled()
                await ensure_logged_in(session_id)
                html_pedidos = await fetch_report_html(session_id, "pedidos_importados")
                html_fechamento = await fetch_report_html(session_id, "fechamento_caixa")
                try:
                    fiscal_status_map = await fetch_fiscal_nfce_status_map(session_id)
                except Exception:
                    fiscal_status_map = {}
                return html_pedidos, html_fechamento, fiscal_status_map
            finally:
                recv_task.cancel()
                try:
                    await recv_task
                except BaseException:
                    pass

    last_error = None
    html_pedidos = ""
    html_fechamento = ""
    caminho_html_pedidos = ""
    caminho_html_fechamento = ""
    fiscal_status_map = {}
    for tentativa in range(2):
        _check_cancelled()
        profile_dir = tempfile.mkdtemp(prefix="run_", dir=profile_root)
        port = _pick_free_local_port()
        _prepare_chromium_profile(profile_dir, _runtime_user_dir())
        browser_visible_debug = _browser_debug_visible_enabled()
        keep_browser_open = _browser_debug_keep_open_enabled()
        chrome_args = [
            navegador,
            f"--remote-debugging-port={port}",
            f"--user-data-dir={profile_dir}",
            "--no-first-run",
            "--no-default-browser-check",
            "--disable-background-networking",
            "--disable-component-update",
            "--disable-popup-blocking",
            "--disable-notifications",
            "--deny-permission-prompts",
            "--disable-save-password-bubble",
            "--disable-features=PasswordManagerOnboarding,AutofillServerCommunication",
            "--window-size=1400,900",
            "--disable-gpu",
            "about:blank",
        ]
        if browser_visible_debug:
            chrome_args.insert(-2, "--window-position=80,80")
        else:
            chrome_args.insert(-2, "--headless=new")

        _emit_pix_status(on_status, "Acessando Zweb...")
        proc = _launch_browser_process(chrome_args)
        try:
            html_pedidos, html_fechamento, fiscal_status_map = asyncio.run(
                asyncio.wait_for(_run(), timeout=180.0)
            )
            last_error = None
            break
        except TimeoutError:
            last_error = RuntimeError(
                "O Zweb demorou demais para responder durante a autenticação ou geração dos relatórios."
            )
            if keep_browser_open:
                raise last_error
            if tentativa >= 1:
                raise last_error
            time.sleep(1.0)
        except Exception as exc:
            last_error = exc
            if keep_browser_open:
                raise
            if tentativa >= 1:
                raise
            time.sleep(1.0)
        finally:
            if not keep_browser_open:
                proc.terminate()
                try:
                    proc.wait(timeout=5)
                except Exception:
                    proc.kill()
                shutil.rmtree(profile_dir, ignore_errors=True)

    if last_error is not None:
        raise last_error

    _emit_pix_status(on_status, "Salvando relatórios do Zweb na pasta atual...")
    caminho_html_pedidos = _save_zweb_html_report(data_br, "pedidos_importados", html_pedidos)
    caminho_html_fechamento = _save_zweb_html_report(data_br, "fechamento_caixa", html_fechamento)

    _emit_pix_status(on_status, "Processando Pedidos importados...")
    relatorio = _analisar_html_pedidos_importados_eh(html_pedidos, arquivo=os.path.basename(caminho_html_pedidos))
    relatorio["caminho"] = caminho_html_pedidos
    _emit_pix_status(on_status, "Processando Fechamento de caixa...")
    relatorio_fechamento = _analisar_html_fechamento_caixa_eh(html_fechamento, arquivo=os.path.basename(caminho_html_fechamento))
    should_filter_sales_date = (
        filtrar_fechamento_por_data_venda
        or _zweb_fechamento_has_sales_outside_date(relatorio_fechamento, data_br)
    )
    if should_filter_sales_date:
        relatorio_fechamento = _filter_zweb_fechamento_to_sales_date(relatorio_fechamento, data_br)
        relatorio_fechamento["fechamento_data_consulta"] = (
            f"{fechamento_data_inicio_br} - {fechamento_data_fim_br}"
            if fechamento_data_inicio_br != fechamento_data_fim_br
            else fechamento_data_inicio_br
        )
    requested_scope_windows = _scope_windows_for_mode(
        relatorio_fechamento.get("fechamento_janelas"),
        scope_mode,
    )
    if requested_scope_windows and _normalize_ascii_text(scope_mode or "") not in {"", "daily", "diario"}:
        relatorio_fechamento = _filter_fechamento_report_to_scope(relatorio_fechamento, requested_scope_windows)
        relatorio_fechamento["escopo_relatorio"] = _scope_mode_label(scope_mode)
    relatorio_fechamento["caminho"] = caminho_html_fechamento
    for report_pagamento in (relatorio_fechamento.get("relatorios_pagamento") or {}).values():
        if not isinstance(report_pagamento, dict):
            continue
        report_pagamento["arquivo"] = os.path.basename(caminho_html_fechamento)
        report_pagamento["caminho"] = caminho_html_fechamento
    relatorio_fechamento["fiscal_status_map"] = fiscal_status_map or {}
    relatorio = _aplicar_filtro_canceladas_pedidos_eh(relatorio, fiscal_status_map or {})
    scope_windows = _report_scope_windows(relatorio_fechamento)
    scope_label = " dentro do escopo horário do fechamento" if scope_windows else ""

    if local_card_pdf:
        _emit_pix_status(on_status, "Lendo relatório local de cartões...")
        try:
            relatorios_cartao = _build_card_reports_from_caixa(local_card_pdf, data_br)
            relatorios_validos = {}
            for key, report in relatorios_cartao.items():
                report_filtrado = _filter_payment_report_to_scope(report, scope_windows)
                if report_filtrado.get("itens_autorizados"):
                    relatorios_validos[key] = report_filtrado
            if relatorios_validos:
                relatorio_fechamento["relatorios_pagamento"].update(relatorios_validos)
            else:
                avisos_usuario.append(
                    f'O arquivo "{os.path.basename(local_card_pdf)}" não trouxe transações de cartão para {data_br}{scope_label} e foi ignorado.'
                )
        except Exception as exc:
            avisos_usuario.append(
                f'Não foi possível ler o arquivo "{os.path.basename(local_card_pdf)}" para {data_br}: {exc}'
            )

    if local_pix_pdf:
        _emit_pix_status(on_status, "Lendo relatorio local de PIX...")
        try:
            pix_suffix = _effective_local_report_suffix(local_pix_pdf)
            if pix_suffix == ".csv":
                relatorio_pix = _build_pix_report_from_caixa_csv(local_pix_pdf, data_br)
            elif pix_suffix == ".xlsx":
                relatorio_pix = _build_pix_report_from_caixa_xlsx(local_pix_pdf, data_br)
            else:
                relatorio_pix = _build_pix_report_from_caixa_pdf(local_pix_pdf, data_br)
            relatorio_pix = _filter_payment_report_to_scope(relatorio_pix, scope_windows)
            if relatorio_pix.get("quantidade_autorizados", 0) <= 0:
                avisos_usuario.append(
                    f'PIX N/A: o arquivo "{os.path.basename(local_pix_pdf)}" não trouxe transações identificáveis para {data_br}{scope_label} e foi ignorado.'
                )
                relatorio_pix = None
        except Exception as exc:
            avisos_usuario.append(
                f'PIX N/A: não foi possível ler o arquivo "{os.path.basename(local_pix_pdf)}" para {data_br}: {exc}'
            )
            relatorio_pix = None
    else:
        avisos_usuario.append(
            "PIX N/A: nenhum relatório identificável da Caixa/Azulzinha foi disponibilizado para a conciliação."
        )
        relatorio_pix = None

    if avisos_usuario:
        relatorio_fechamento["avisos_usuario"] = list(dict.fromkeys(avisos_usuario))
        if relatorio_pix is not None:
            relatorio_pix["avisos_usuario"] = list(dict.fromkeys(avisos_usuario))

    if relatorio_pix:
        relatorio_fechamento.setdefault("relatorios_pagamento", {})
        relatorio_fechamento["relatorios_pagamento"][str(relatorio_pix.get("categoria") or "pix_caixa")] = relatorio_pix

    _cleanup_eh_auto_payment_reports(local_pix_pdf, local_card_pdf)
    return relatorio, relatorio_fechamento, relatorio_pix


def _parse_caixa_pix_datetime(data_hora: str) -> tuple[str, datetime]:
    texto = str(data_hora or "").strip()
    if not texto:
        return "", datetime.min

    normalizado = texto.replace("Z", "+00:00")
    try:
        data = datetime.fromisoformat(normalizado)
        return data.strftime("%d/%m/%Y as %H:%M"), data
    except ValueError:
        pass

    match = re.match(r"(\d{4}-\d{2}-\d{2})[T\s](\d{2}:\d{2})(?::\d{2}(?:\.\d+)?)?", texto)
    if match:
        texto_br = f"{match.group(1)} {match.group(2)}"
        try:
            data = datetime.strptime(texto_br, "%Y-%m-%d %H:%M")
            return data.strftime("%d/%m/%Y as %H:%M"), data
        except ValueError:
            pass

    return texto, datetime.min


def _load_minhas_notas_credentials() -> tuple[str, str] | None:
    login = str(MINHAS_NOTAS_LOGIN or "").strip()
    password = str(MINHAS_NOTAS_PASSWORD or "").strip()
    if login and password:
        return login, password

    base_dir = _runtime_user_dir()
    for filename in ("credenciais.txt", "credencias.txt"):
        caminho = os.path.join(base_dir, filename)
        if not os.path.isfile(caminho):
            continue
        try:
            with open(caminho, "r", encoding="utf-8") as arquivo:
                linhas = [linha.strip() for linha in arquivo.readlines() if linha.strip()]
        except OSError:
            return None
        if len(linhas) >= 2:
            return linhas[0], linhas[1]
    return None


def _authenticate_minhas_notas(login: str, password: str) -> str:
    resposta = requests.post(
        "https://api.clippfacil.com.br/rpc/v2/application.authenticate",
        json={
            "login": login,
            "password": password,
            "isSharedAccess": True,
        },
        headers={
            "Accept": "application/json, text/plain, */*",
            "Content-Type": "application/json",
        },
        timeout=20,
    )
    resposta.raise_for_status()
    payload = resposta.json() or {}
    token = str(payload.get("access_token") or "").strip()
    if not token:
        raise ValueError("Não foi possível autenticar no Minhas Notas.")
    return token


def _fetch_minhas_notas_nfes(
    access_token: str,
    data_iso: str,
    *,
    model: str = "55",
    cache_namespace: str = "",
) -> list[dict]:
    model_text = str(model or "55").strip() or "55"
    cache_key = ((cache_namespace or access_token[-8:]).lower(), data_iso, model_text)
    if cache_key in _MINHAS_NOTAS_CACHE:
        return [dict(item) for item in _MINHAS_NOTAS_CACHE[cache_key]]

    headers = {
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "pt_BR",
        "Authorization-Compufacil": access_token,
        "Content-Type": "application/json;charset=UTF-8",
    }
    documentos = []
    pagina = 1
    max_results = 100

    while True:
        resposta = requests.post(
            "https://api.clippfacil.com.br/rpc/v1/clipp.get-xml-by-emissor",
            json={
                "page": pagina,
                "maxResults": max_results,
                "model": model_text,
                "fromEmission": data_iso,
                "toEmission": data_iso,
            },
            headers=headers,
            timeout=20,
        )
        resposta.raise_for_status()
        payload = resposta.json() or {}
        pagina_docs = payload.get("data") or []
        documentos.extend(pagina_docs)

        total = int(payload.get("total") or 0)
        if not pagina_docs or len(documentos) >= total or len(pagina_docs) < max_results:
            break
        pagina += 1

    normalizados = []
    for item in documentos:
        try:
            valor = round(float(item.get("totalValue", 0.0)), 2)
        except (TypeError, ValueError):
            continue
        normalizados.append(
            {
                "numero": str(item.get("number") or "").strip(),
                "valor": valor,
                "status": int(item.get("status") or 0),
                "model": model_text,
                "tipo": str(item.get("type") or "").strip(),
                "cliente": str(item.get("customerName") or "").strip(),
                "cpf_cnpj": str(item.get("customerIdentification") or "").strip(),
                "emissao": str(item.get("emission") or "").strip(),
                "cancelada": bool(item.get("canceledXmlFile")) or int(item.get("status") or 0) == 2,
                "canceled_xml": str(item.get("canceledXmlFile") or "").strip(),
            }
        )

    _MINHAS_NOTAS_CACHE[cache_key] = [dict(item) for item in normalizados]
    return [dict(item) for item in normalizados]


def _load_minhas_notas_mva_context(
    periodo: str,
) -> tuple[list[dict], dict[str, dict], str | None]:
    data_iso = _period_to_iso_date(periodo)
    if not data_iso:
        return [], {}, None

    credenciais = _load_minhas_notas_credentials()
    if not credenciais:
        return [], {}, None

    try:
        login, password = credenciais
        access_token = _authenticate_minhas_notas(login, password)
        nfes_modelo_55 = _fetch_minhas_notas_nfes(
            access_token,
            data_iso,
            model="55",
            cache_namespace=login,
        )
        nfces_modelo_65 = _fetch_minhas_notas_nfes(
            access_token,
            data_iso,
            model="65",
            cache_namespace=login,
        )
    except Exception as exc:
        return [], {}, str(exc)

    nfes_ativas = [
        item
        for item in nfes_modelo_55
        if item.get("status") == 1 and item.get("tipo") == "1"
    ]

    fiscal_status_map: dict[str, dict] = {}
    for item in sorted(
        nfces_modelo_65,
        key=lambda dado: (
            str(dado.get("numero") or ""),
            str(dado.get("emissao") or ""),
        ),
    ):
        numero = _normalize_fiscal_number(item.get("numero", ""))
        if not numero or numero in fiscal_status_map:
            continue
        fiscal_status_map[numero] = {
            "numero": numero,
            "numero_exibicao": _display_fiscal_number(numero),
            "valor": round(float(item.get("valor", 0.0) or 0.0), 2),
            "cancelada": bool(item.get("cancelada")),
            "status_codigo": int(item.get("status") or 0),
            "emissao": str(item.get("emissao") or "").strip(),
        }

    return nfes_ativas, fiscal_status_map, None


def _match_davs_with_minhas_notas_nfes_from_items(
    davs_sem_cupom: list[dict],
    nfes: list[dict],
) -> tuple[list[dict], list[dict]]:
    nfes_por_valor = {}
    for item in sorted(
        nfes,
        key=lambda dado: (
            round(float(dado.get("valor", 0.0)), 2),
            dado.get("numero", ""),
        ),
    ):
        valor = round(float(item.get("valor", 0.0)), 2)
        nfes_por_valor.setdefault(valor, []).append(item)

    restantes = []
    encontrados = []
    for item in sorted(davs_sem_cupom, key=lambda dado: dado.get("pedido", "")):
        valor = round(float(item.get("valor", 0.0)), 2)
        candidatos = nfes_por_valor.get(valor) or []
        if not candidatos:
            restantes.append(item)
            continue
        nfe = candidatos.pop(0)
        encontrados.append(
            {
                "pedido": str(item.get("pedido") or "").strip(),
                "valor": valor,
                "numero_nfe": str(nfe.get("numero") or "").strip(),
                "cliente_nfe": str(nfe.get("cliente") or "").strip(),
                "cpf_cnpj_nfe": str(nfe.get("cpf_cnpj") or "").strip(),
                "emissao_nfe": str(nfe.get("emissao") or "").strip(),
            }
        )

    return restantes, encontrados


def _match_davs_with_minhas_notas_nfes(
    davs_sem_cupom: list[dict],
    periodo: str,
) -> tuple[list[dict], list[dict], str | None]:
    data_iso = _period_to_iso_date(periodo)
    if not data_iso or not davs_sem_cupom:
        return list(davs_sem_cupom), [], None

    nfes_ativas, _fiscal_status_map, erro = _load_minhas_notas_mva_context(periodo)
    if erro:
        return list(davs_sem_cupom), [], erro

    restantes, encontrados = _match_davs_with_minhas_notas_nfes_from_items(
        davs_sem_cupom,
        nfes_ativas,
    )
    return restantes, encontrados, None


def _build_mva_cancelled_coupon_pool(
    itens_nfce: list[dict],
    fiscal_status_map: dict[str, dict],
) -> dict[str, dict]:
    numeros_presentes = {
        _normalize_fiscal_number(item.get("numero", ""))
        for item in itens_nfce or []
        if _normalize_fiscal_number(item.get("numero", ""))
    }
    return {
        numero: info
        for numero, info in (fiscal_status_map or {}).items()
        if numero not in numeros_presentes and bool((info or {}).get("cancelada"))
    }


def _match_davs_with_mva_cancelled_coupons(
    davs_sem_cupom: list[dict],
    cancelados_ausentes: dict[str, dict],
) -> tuple[list[dict], dict[str, dict]]:
    cancelados_por_valor: dict[float, list[tuple[str, dict]]] = {}
    for numero, info in sorted(cancelados_ausentes.items(), key=lambda item: int(item[0])):
        valor = round(float((info or {}).get("valor", 0.0) or 0.0), 2)
        cancelados_por_valor.setdefault(valor, []).append((numero, info))

    restantes: list[dict] = []
    cancelados_correspondentes: dict[str, dict] = {}
    for item in sorted(davs_sem_cupom, key=lambda dado: dado.get("pedido", "")):
        valor = round(float(item.get("valor", 0.0) or 0.0), 2)
        candidatos = cancelados_por_valor.get(valor) or []
        if not candidatos:
            restantes.append(item)
            continue
        numero, info = candidatos.pop(0)
        cancelados_correspondentes[numero] = info

    return restantes, cancelados_correspondentes


def _build_mva_cancelled_coupon_registros(
    cfs_faltantes: list[str],
    cancelados_ausentes: dict[str, dict],
) -> list[dict]:
    registros: list[dict] = []
    numeros_registrados: set[str] = set()

    for numero in cfs_faltantes:
        if not numero or numero in numeros_registrados:
            continue
        info = cancelados_ausentes.get(numero) or {}
        observacao = "Cupom cancelado" if info.get("cancelada") else "Cupom faltante na sequencia"
        valor = info.get("valor") if info.get("cancelada") else None
        registros.append(
            {
                "numero": numero,
                "numero_exibicao": f"CF {_display_fiscal_number(numero)}",
                "origem": "CF",
                "observacao": observacao,
                "valor": valor,
            }
        )
        numeros_registrados.add(numero)

    for numero, info in sorted(cancelados_ausentes.items(), key=lambda item: int(item[0])):
        if numero in numeros_registrados:
            continue
        registros.append(
            {
                "numero": numero,
                "numero_exibicao": f"CF {_display_fiscal_number(numero)}",
                "origem": "CF",
                "observacao": "Cupom cancelado",
                "valor": info.get("valor"),
            }
        )
        numeros_registrados.add(numero)

    return registros


def _build_cancelados_rows_from_pendencias(pendencias: list[dict]) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for item in pendencias or []:
        numero_exibicao = str(item.get("numero_exibicao") or item.get("numero") or "-").strip()
        if numero_exibicao.upper().startswith("CF "):
            cf_label = numero_exibicao
        else:
            cf_label = f"CF {numero_exibicao}"
        valor = item.get("valor")
        valor_texto = "-" if valor in (None, "") else f"R$ {format_number_br(valor)}"
        rows.append((cf_label, valor_texto))
    return rows


def _split_cancelled_payment_items(
    itens_fechamento: list[dict],
    fiscal_status_map: dict[str, dict],
) -> tuple[list[dict], list[dict]]:
    itens_ativos: list[dict] = []
    itens_cancelados: list[dict] = []
    for item in itens_fechamento or []:
        numero = _normalize_fiscal_number(item.get("numero", "") or item.get("numero_exibicao", ""))
        if numero and (fiscal_status_map.get(numero) or {}).get("cancelada"):
            info = fiscal_status_map.get(numero) or {}
            itens_cancelados.append(
                {
                    "numero": numero,
                    "numero_exibicao": item.get("numero_exibicao")
                    or info.get("numero_exibicao")
                    or _display_fiscal_number(numero),
                    "valor": round(float(item.get("valor_bruto", item.get("valor", 0.0)) or 0.0), 2),
                }
            )
            continue
        itens_ativos.append(item)
    return itens_ativos, itens_cancelados


def _find_missing_fiscal_numbers(numbers: list[str]) -> list[str]:
    normalized_numbers = [
        _normalize_fiscal_number(numero)
        for numero in numbers
        if _normalize_fiscal_number(numero)
    ]
    if not normalized_numbers:
        return []

    ints = sorted({int(numero) for numero in normalized_numbers})
    missing = []
    for current, nxt in zip(ints, ints[1:]):
        if nxt - current > 1:
            for numero in range(current + 1, nxt):
                missing.append(_normalize_fiscal_number(numero))
    return missing


def validar_periodo_relatorios_caixa(
    relatorio_caixa: dict,
    relatorio_nfce: dict,
    titulo_secundario: str = "Resumo NFC-e",
) -> tuple[bool, str]:
    inicio_caixa, fim_caixa = _extract_period_range(relatorio_caixa.get("periodo", ""))
    inicio_resumo, fim_resumo = _extract_period_range(relatorio_nfce.get("periodo", ""))

    if not all((inicio_caixa, fim_caixa, inicio_resumo, fim_resumo)):
        return False, "Não foi possível identificar o período dos dois relatórios."
    if inicio_caixa != fim_caixa:
        return False, "O relatorio de pedidos importados precisa ser de um unico dia."
    if inicio_resumo != fim_resumo:
        return False, f"O {titulo_secundario} precisa ser de um unico dia."
    if inicio_caixa != inicio_resumo:
        return False, (
            f"Os relatorios sao de dias diferentes.\n"
            f"Pedidos importados: {inicio_caixa}\n"
            f"{titulo_secundario}: {inicio_resumo}"
        )
    return True, inicio_caixa


def validar_relatorio_pedidos_importados(
    relatorio: dict,
    modelo_esperado: str | None = None,
) -> tuple[bool, str]:
    if relatorio and relatorio.get("pdf_sem_texto"):
        return False, _pdf_sem_texto_message(relatorio.get("arquivo"))

    modelo = (relatorio.get("caixa_modelo") or "").upper()
    modelo_esperado = (modelo_esperado or "").upper()

    if modelo_esperado and modelo and modelo != modelo_esperado:
        if modelo_esperado == "MVA":
            return False, "O arquivo selecionado no passo 1 não parece ser uma Exportação de dados da MVA."
        return False, "O arquivo selecionado no passo 1 não parece ser um relatório de pedidos importados da EH."

    if not relatorio or relatorio.get("pedidos_total", 0) <= 0:
        if modelo_esperado == "MVA":
            return False, "O arquivo selecionado no passo 1 não parece ser uma Exportação de dados da MVA."
        return False, "O arquivo selecionado no passo 1 não parece ser um relatório de pedidos importados."
    if not relatorio.get("periodo"):
        if modelo_esperado == "MVA":
            return True, ""
        return False, "Não foi possível identificar o período no relatório de pedidos importados."
    if relatorio.get("total_documento", 0.0) <= 0:
        if modelo_esperado == "MVA":
            return False, "A Exportação de dados da MVA não trouxe um total válido."
        return False, "O relatório de pedidos importados não trouxe um total válido."
    return True, ""


def validar_relatorio_resumo_nfce(
    relatorio: dict,
    modelo_esperado: str | None = None,
) -> tuple[bool, str]:
    if relatorio and relatorio.get("pdf_sem_texto"):
        return False, _pdf_sem_texto_message(relatorio.get("arquivo"))

    modelo = (relatorio.get("resumo_modelo") or "EH").upper()
    modelo_esperado = (modelo_esperado or "").upper()
    if modelo_esperado and modelo != modelo_esperado:
        if modelo_esperado == "MVA":
            return False, "O arquivo selecionado no último passo não parece ser o relatório de Cupons da MVA."
        return False, "O arquivo selecionado no passo 2 não parece ser um Resumo NFC-e."
    if not relatorio or relatorio.get("quantidade_nfce", 0) <= 0:
        if modelo_esperado == "MVA":
            return False, "O arquivo selecionado no último passo não parece ser o relatório de Cupons da MVA."
        return False, "O arquivo selecionado no passo 2 não parece ser um Resumo NFC-e."
    if not relatorio.get("periodo"):
        if modelo_esperado == "MVA":
            return False, "Não foi possível identificar o período no relatório de Cupons."
        return False, "Não foi possível identificar o período no Resumo NFC-e."
    if relatorio.get("total_nfce", 0.0) <= 0:
        if modelo_esperado == "MVA":
            return False, "O relatório de Cupons não trouxe um total válido."
        return False, "O Resumo NFC-e não trouxe um total válido."
    return True, ""








def _comparar_caixa_resumo_nfce_eh(relatorio_caixa: dict, relatorio_nfce: dict) -> dict:
    itens_caixa = relatorio_caixa.get("itens_caixa", [])
    itens_nfce = relatorio_nfce.get("nfces", [])
    fiscal_status_map = relatorio_nfce.get("fiscal_status_map") or {}
    relatorios_pagamento = dict(relatorio_nfce.get("relatorios_pagamento") or {})
    nf_report = _build_eh_nf_filtered_report(relatorio_caixa)
    if nf_report:
        relatorios_pagamento[nf_report["categoria"]] = nf_report

    fechamento_map = {
        _normalize_fiscal_number(item.get("numero", "")): {
            "numero": _normalize_fiscal_number(item.get("numero", "")),
            "numero_exibicao": item.get("numero_exibicao") or _display_fiscal_number(item.get("numero", "")),
            "valor": round(float(item.get("valor", 0.0)), 2),
            "descricao": item.get("descricao", ""),
        }
        for item in itens_nfce
        if _normalize_fiscal_number(item.get("numero", ""))
    }

    registros_map: dict[tuple[str, str, str], dict] = {}
    alert_rows: list[tuple[str, str, str]] = []
    alert_seen: set[tuple[str, str, str]] = set()
    pix_fechamento_only: list[dict] = []
    pix_machine_only: list[dict] = []
    card_fechamento_only: list[dict] = []
    card_machine_only: list[dict] = []

    def _money_text(value: float | None) -> str:
        return "-" if value in (None, "") else f"R$ {format_number_br(value)}"

    def _add_alert(tipo: str, detalhe: str, valor: str) -> None:
        key = (tipo, detalhe, valor)
        if key in alert_seen:
            return
        alert_seen.add(key)
        alert_rows.append(key)

    def _add_registro(numero: str, numero_exibicao: str, valor: float | None, origem: str, observacao: str) -> None:
        numero_normalizado = _normalize_fiscal_number(numero)
        key = (numero_normalizado, origem, observacao)
        valor_normalizado = None if valor in (None, "") else round(float(valor), 2)
        entry = registros_map.get(key)
        if entry is None:
            registros_map[key] = {
                "numero": numero_normalizado,
                "numero_exibicao": numero_exibicao or _display_fiscal_number(numero_normalizado),
                "origem": origem,
                "observacao": observacao,
                "valor": valor_normalizado,
            }
            return
        if valor_normalizado is not None:
            entry["valor"] = round(float(entry.get("valor") or 0.0) + valor_normalizado, 2)

    pedidos_cancelados = []
    pedidos_cancelados_map: dict[str, dict] = {}
    pedidos_cancelados_numeros: set[str] = set()
    numeros_pedidos_conferidos = set()
    numeros_pedidos_pendentes = set()

    for item in relatorio_caixa.get("itens_excluidos", []) or []:
        motivo_item = corrigir_texto(str(item.get("motivo", ""))).strip()
        documento_item = _normalize_caixa_client(item.get("documento", ""))
        if "cupom cancelado" not in motivo_item.casefold() and "CANCELADA" not in documento_item:
            continue
        numero = _normalize_fiscal_number(item.get("pedido", ""))
        if not numero or numero in pedidos_cancelados_numeros:
            continue
        valor = round(float(item.get("valor", 0.0)), 2)
        pendencia = {
            "numero": numero,
            "numero_exibicao": _display_fiscal_number(numero),
            "valor": valor,
            "motivo": motivo_item or "Cupom cancelado",
        }
        pedidos_cancelados.append(pendencia)
        pedidos_cancelados_map[numero] = dict(pendencia)
        pedidos_cancelados_numeros.add(numero)
        _add_alert("Cupom cancelado", f"CF {pendencia['numero_exibicao']}: {pendencia['motivo']}", _money_text(valor))

    for item in itens_caixa:
        numero = _normalize_fiscal_number(item.get("pedido", ""))
        if not numero:
            continue
        valor = round(float(item.get("valor", 0.0)), 2)
        fechamento_item = fechamento_map.get(numero)
        if fechamento_item and abs(float(fechamento_item.get("valor", 0.0)) - valor) < 0.01:
            numeros_pedidos_conferidos.add(numero)
            continue

        if fechamento_item:
            motivo = f"Valor divergente no Fechamento de caixa ({_money_text(fechamento_item.get('valor'))})"
        else:
            motivo = "CF não encontrado no Fechamento de caixa"

        pendencia = {
            "numero": numero,
            "numero_exibicao": _display_fiscal_number(numero),
            "valor": valor,
            "motivo": motivo,
        }
        if (fiscal_status_map.get(numero) or {}).get("cancelada"):
            if numero in pedidos_cancelados_numeros:
                continue
            pedidos_cancelados.append(pendencia)
            pedidos_cancelados_map[numero] = dict(pendencia)
            pedidos_cancelados_numeros.add(numero)
            _add_alert("Cupom cancelado", f"CF {pendencia['numero_exibicao']}: {motivo}", _money_text(valor))
        else:
            numeros_pedidos_pendentes.add(numero)
            _add_registro(numero, pendencia["numero_exibicao"], valor, "Pedido", motivo)
            _add_alert("Pedido pendente", f"CF {pendencia['numero_exibicao']}: {motivo}", _money_text(valor))

    dinheiro_report = relatorios_pagamento.get("dinheiro") or {}
    dinheiro_itens_ativos, _dinheiro_itens_cancelados = _split_cancelled_payment_items(
        list(dinheiro_report.get("itens_autorizados") or []),
        fiscal_status_map,
    )
    valores_dinheiro_confirmados = {
        round(float(item.get("valor_bruto", 0.0) or 0.0), 2)
        for item in dinheiro_itens_ativos
    }
    periodo_fechamento = str(relatorio_nfce.get("periodo") or relatorio_caixa.get("periodo") or "").split(" - ", 1)[0]
    for item in itens_caixa:
        numero = _display_fiscal_number(item.get("pedido", ""))
        if (periodo_fechamento, numero) in _EH_CARD_MACHINE_CASH_COUPONS:
            valores_dinheiro_confirmados.add(round(float(item.get("valor", 0.0) or 0.0), 2))
    for item in dinheiro_itens_ativos:
        numero = _normalize_fiscal_number(item.get("numero", ""))
        if not numero or numero in numeros_pedidos_conferidos or numero in numeros_pedidos_pendentes:
            continue
        if (fiscal_status_map.get(numero) or {}).get("cancelada"):
            continue
        valor = round(float(item.get("valor_bruto", 0.0)), 2)
        _add_registro(
            numero,
            item.get("numero_exibicao") or _display_fiscal_number(numero),
            valor,
            "Fechamento",
            "Dinheiro sem pedido correspondente",
        )
        _add_alert(
            "CF sem pedido",
            f"Dinheiro: CF {item.get('numero_exibicao') or _display_fiscal_number(numero)}",
            _money_text(valor),
        )

    correlacao_rows = []

    dinheiro_total = round(float(dinheiro_report.get("total_autorizado", 0.0) or 0.0), 2)
    correlacao_rows.append(
        (
            "Dinheiro",
            f"R$ {format_number_br(dinheiro_total)}",
            "-",
            "Interno",
        )
    )

    comparacoes = [
        (
            "PIX",
            relatorios_pagamento.get("pix_caixa"),
            relatorios_pagamento.get("pix_fechamento"),
            "valor_bruto",
        ),
        (
            "Cart\u00e3o Cr\u00e9dito",
            relatorios_pagamento.get("cartao_credito_caixa"),
            relatorios_pagamento.get("cartao_credito"),
            "valor_bruto",
        ),
        (
            "Cart\u00e3o D\u00e9bito",
            relatorios_pagamento.get("cartao_debito_caixa"),
            relatorios_pagamento.get("cartao_debito"),
            "valor_bruto",
        ),
    ]
    comparacoes_cartao = {"Cart\u00e3o Cr\u00e9dito", "Cart\u00e3o D\u00e9bito"}


    for titulo_pagamento, report_externo, report_fechamento, campo_valor in comparacoes:
        if not report_fechamento:
            continue
        itens_fechamento = list(report_fechamento.get("itens_autorizados") or [])
        itens_fechamento, itens_fechamento_cancelados = _split_cancelled_payment_items(
            itens_fechamento,
            fiscal_status_map,
        )
        for item_cancelado in itens_fechamento_cancelados:
            numero_cancelado = str(item_cancelado.get("numero") or "")
            if numero_cancelado in pedidos_cancelados_map:
                continue
            pedidos_cancelados_map[numero_cancelado] = {
                "numero": numero_cancelado,
                "numero_exibicao": item_cancelado.get("numero_exibicao") or _display_fiscal_number(numero_cancelado),
                "valor": item_cancelado.get("valor"),
                "motivo": f"{titulo_pagamento} cancelado permaneceu no fechamento",
            }
            _add_alert(
                "Cupom cancelado",
                f"CF {pedidos_cancelados_map[numero_cancelado]['numero_exibicao']}: {pedidos_cancelados_map[numero_cancelado]['motivo']}",
                _money_text(item_cancelado.get("valor")),
            )
        total_caixa_pagamento = round(float(report_fechamento.get("total_autorizado", 0.0) or 0.0), 2)
        if not report_externo:
            correlacao_rows.append(
                (
                    titulo_pagamento,
                    f"R$ {format_number_br(total_caixa_pagamento)}",
                    "N/A",
                    "N/A",
                )
            )
            _add_alert(
                "Relatório ausente",
                f"{titulo_pagamento}: N/A, relatório identificável da Caixa/Azulzinha não encontrado na pasta atual de execução.",
                "N/A",
            )
            continue

        itens_externos = list(report_externo.get("itens_autorizados") or [])
        itens_externos_compativeis = itens_externos
        itens_externos_com_valor_de_dinheiro: list[dict] = []
        if titulo_pagamento in comparacoes_cartao:
            itens_externos_compativeis = []
            for item in itens_externos:
                valor = round(float(item.get(campo_valor, 0.0) or 0.0), 2)
                if valor in valores_dinheiro_confirmados:
                    itens_externos_com_valor_de_dinheiro.append(item)
                else:
                    itens_externos_compativeis.append(item)

        _matched, externos_sem_fechamento, fechamento_sem_externo = _multiset_match_by_value(
            itens_externos_compativeis,
            itens_fechamento,
            campo_esquerda=campo_valor,
            campo_direita="valor_bruto",
        )
        externos_restantes = externos_sem_fechamento + itens_externos_com_valor_de_dinheiro
        total_pagamentos = round(
            sum(float(item.get(campo_valor, 0.0) or 0.0) for item in itens_externos),
            2,
        )
        status_correlacao = "Finalizado" if abs(total_caixa_pagamento - total_pagamentos) < 0.01 else "Divergente"
        correlacao_rows.append(
            (
                titulo_pagamento,
                f"R$ {format_number_br(total_caixa_pagamento)}",
                f"R$ {format_number_br(total_pagamentos)}",
                status_correlacao,
            )
        )

        for item in externos_restantes:
            valor = round(float(item.get(campo_valor, 0.0)), 2)
            detail = item.get("data_venda") or item.get("numero_exibicao") or item.get("numero") or "-"
            if titulo_pagamento == "PIX":
                pix_machine_only.append(
                    {
                        "titulo": titulo_pagamento,
                        "data_venda": detail,
                        "valor": valor,
                    }
                )
            if titulo_pagamento in comparacoes_cartao:
                card_machine_only.append(
                    {
                        "titulo": titulo_pagamento,
                        "data_venda": detail,
                        "valor": valor,
                    }
                )
            alert_rows.append(
                (
                    "Transação Bancária sem CF/NF",
                    f"{titulo_pagamento}: {detail}",
                    _money_text(valor),
                )
            )

        for item in fechamento_sem_externo:
            numero = _normalize_fiscal_number(item.get("numero", ""))
            if not numero or numero in numeros_pedidos_pendentes:
                continue
            if (fiscal_status_map.get(numero) or {}).get("cancelada"):
                continue
            valor = round(float(item.get("valor_bruto", 0.0)), 2)
            _add_registro(
                numero,
                item.get("numero_exibicao") or _display_fiscal_number(numero),
                valor,
                "Fechamento",
                f"{titulo_pagamento} sem pagamento correspondente na máquina",
            )
            if titulo_pagamento == "PIX":
                pix_fechamento_only.append(
                    {
                        "titulo": titulo_pagamento,
                        "numero_exibicao": item.get("numero_exibicao") or _display_fiscal_number(numero),
                        "valor": valor,
                    }
                )
            if titulo_pagamento in comparacoes_cartao:
                card_fechamento_only.append(
                    {
                        "titulo": titulo_pagamento,
                        "numero_exibicao": item.get("numero_exibicao") or _display_fiscal_number(numero),
                        "valor": valor,
                    }
                )
            alert_rows.append(
                (
                    "CF sem Transação Bancária",
                    f"{titulo_pagamento}: CF {item.get('numero_exibicao') or _display_fiscal_number(numero)}",
                    _money_text(valor),
                )
            )

    pix_caixa_report = relatorios_pagamento.get("pix_caixa")
    pix_fechamento_report = relatorios_pagamento.get("pix_fechamento")
    if pix_caixa_report and pix_fechamento_report:
        pix_cancelados = [
            item
            for item in (pix_caixa_report.get("itens_todos") or [])
            if item.get("tipo_pix") == "RECEBIDO" and "CANCEL" in _normalize_ascii_text(item.get("situacao", ""))
        ]
        pix_efetivados = list(pix_caixa_report.get("itens_autorizados") or [])
        valores_fechamento_pix = [round(float(item.get("valor_bruto", 0.0)), 2) for item in (pix_fechamento_report.get("itens_autorizados") or [])]
        for item in pix_cancelados:
            valor = round(float(item.get("valor_bruto", 0.0)), 2)
            if valor not in valores_fechamento_pix:
                continue
            ordem_cancelada = str(item.get("ordem") or "")
            tem_subsequente = any(
                round(float(outro.get("valor_bruto", 0.0)), 2) == valor
                and str(outro.get("ordem") or "") > ordem_cancelada
                for outro in pix_efetivados
            )
            if not tem_subsequente:
                alert_rows.append(
                    (
                        "PIX cancelado",
                        f"Cancelar cupom: PIX cancelado em {item.get('data_venda')} permaneceu no Fechamento",
                        _money_text(valor),
                    )
                )

    pedidos_cancelados = list(pedidos_cancelados_map.values())
    registros = list(registros_map.values())
    valor_canceladas_pendentes = round(sum(item.get("valor", 0.0) for item in pedidos_cancelados), 2)
    valor_registros_pendentes = round(
        sum(float(item.get("valor", 0.0)) for item in registros if item.get("valor") not in (None, "")),
        2,
    )
    valor_banco_pendente = round(
        sum(float(item.get("valor", 0.0)) for item in pix_fechamento_only + card_fechamento_only + pix_machine_only + card_machine_only),
        2,
    )
    valor_faltantes = round(valor_registros_pendentes + valor_banco_pendente, 2)
    total_caixa = round(float(relatorio_caixa.get("total_caixa", 0.0)), 2)
    total_resumo = round(float(relatorio_nfce.get("total_nfce", 0.0)), 2)

    alertas_report = _build_eh_alerts_report(
        relatorio_caixa.get("periodo"),
        alert_rows,
        pix_fechamento_rows=[
            (f"CF {item.get('numero_exibicao') or '-'}", f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in pix_fechamento_only
        ],
        pix_maquina_rows=[
            (str(item.get("data_venda") or "-"), f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in pix_machine_only
        ],
        cartao_fechamento_rows=[
            (
                f"{('Crédito' if 'CREDITO' in _normalize_caixa_client(item.get('titulo', '')) else 'Débito')}: CF {item.get('numero_exibicao') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in card_fechamento_only
        ],
        cartao_maquina_rows=[
            (
                f"{('Crédito' if 'CREDITO' in _normalize_caixa_client(item.get('titulo', '')) else 'Débito')}: {item.get('data_venda') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in card_machine_only
        ],
        cancelados_rows=_build_cancelados_rows_from_pendencias(pedidos_cancelados),
        allow_empty=True,
    )
    if alertas_report:
        alertas_report["hidden_in_menu"] = True
        alertas_report["summary_items"] = [
            ("Período", str(relatorio_caixa.get("periodo") or "Não identificado")),
            ("Pendências", str(_count_visible_alert_rows(alertas_report))),
            ("Total Pendências", f"R$ {format_number_br(valor_banco_pendente)}"),
        ]
        alertas_report["correlacao_rows"] = correlacao_rows
        alertas_report["valor_total_vendas"] = total_caixa
        alertas_report["valor_pendente"] = valor_banco_pendente
        alertas_report["hidden_pending_count"] = 0
        alertas_report["hidden_pending_value"] = 0.0
        alertas_report["texto_informativo"] = ""
        relatorios_pagamento[alertas_report["categoria"]] = alertas_report
        for key in (
            "pix_caixa",
            "pix_fechamento",
            "cartao_credito",
            "cartao_debito",
            "cartao_credito_caixa",
            "cartao_debito_caixa",
        ):
            if relatorios_pagamento.get(key):
                relatorios_pagamento[key]["hidden_in_menu"] = True

    pending_alert_rows = [row for row in alert_rows if not _is_cancelled_coupon_alert_row(row)]
    status = "Confere"
    if registros or pending_alert_rows:
        status = "Faltante"
    if alertas_report:
        alertas_report["status"] = status
    visible_alert_count = _count_visible_alert_rows(alertas_report)

    periodo_unico, _ = _extract_period_range(relatorio_caixa.get("periodo", ""))
    escopo_relatorio = (
        relatorio_nfce.get("escopo_relatorio")
        or relatorio_caixa.get("escopo_relatorio")
    )
    escopo_horario_aplicado = list(
        relatorio_nfce.get("escopo_horario_aplicado")
        or relatorio_caixa.get("escopo_horario_aplicado")
        or []
    )

    return {
        "caixa_modelo": "EH",
        "arquivo_caixa": relatorio_caixa.get("arquivo"),
        "arquivo_caixa_titulo": relatorio_caixa.get("arquivo_caixa_titulo") or "Arquivo Pedidos",
        "arquivo_resumo": relatorio_nfce.get("arquivo"),
        "arquivo_resumo_titulo": relatorio_nfce.get("arquivo_resumo_titulo"),
        "subtitle": relatorio_nfce.get("subtitle"),
        "periodo": periodo_unico or relatorio_caixa.get("periodo"),
        "total_caixa": total_caixa,
        "total_caixa_titulo": relatorio_caixa.get("total_caixa_titulo") or "Total Pedidos Caixa",
        "total_resumo_nfce": total_resumo,
        "total_resumo_titulo": relatorio_nfce.get("total_resumo_titulo"),
        "nfces_faltantes_count": len(registros),
        "valor_faltantes": valor_faltantes,
        "status": status,
        "canceladas_ignoradas_count": len(pedidos_cancelados),
        "canceladas_ignoradas_valor": valor_canceladas_pendentes,
        "canceladas_pendentes_count": 0,
        "canceladas_pendentes_valor": 0.0,
        "escopo_relatorio": escopo_relatorio,
        "escopo_horario_aplicado": escopo_horario_aplicado,
        "avisos_usuario": list(relatorio_nfce.get("avisos_usuario") or []),
        "relatorios_pagamento": relatorios_pagamento,
        "alertas_count": visible_alert_count,
        "registros_conferencia": sorted(
            registros,
            key=lambda item: (
                int(item["numero"]) if str(item.get("numero") or "").isdigit() else 0,
                item["origem"],
                item.get("observacao", ""),
            ),
        ),
    }


def _is_mva_cupom_client(cliente: str) -> bool:
    return _normalize_caixa_client(cliente) in {"CLIENTE BALCAO", "CLIENTES DIVERSOS"}


def _infer_mva_davs_sem_cupom(itens_caixa: list[dict], itens_nfce: list[dict]) -> list[dict]:
    elegiveis = [
        item
        for item in itens_caixa
        if _is_mva_cupom_client(item.get("cliente", ""))
    ]
    if not elegiveis or not itens_nfce:
        return sorted(elegiveis, key=lambda item: item.get("pedido", ""))

    davs_sorted = sorted(
        elegiveis,
        key=lambda item: (round(float(item.get("valor", 0.0)), 2), item.get("pedido", "")),
    )
    nfce_sorted = sorted(
        itens_nfce,
        key=lambda item: (round(float(item.get("valor", 0.0)), 2), item.get("numero", "")),
    )

    n = len(davs_sorted)
    m = len(nfce_sorted)

    def _melhor_estado(candidatos):
        prioridade = {"match": 0, "skip_nfce": 1, "skip_dav": 2}
        return min(
            candidatos,
            key=lambda candidato: (
                candidato[0][0],
                candidato[0][1],
                prioridade[candidato[1]],
            ),
        )

    dp = [[(0, 0.0)] * (m + 1) for _ in range(n + 1)]
    caminho = [[""] * (m + 1) for _ in range(n + 1)]

    for i in range(1, n + 1):
        dp[i][0] = (i, 0.0)
        caminho[i][0] = "skip_dav"
    for j in range(1, m + 1):
        dp[0][j] = (0, 0.0)
        caminho[0][j] = "skip_nfce"

    for i in range(1, n + 1):
        for j in range(1, m + 1):
            valor_dav = round(float(davs_sorted[i - 1].get("valor", 0.0)), 2)
            valor_nfce = round(float(nfce_sorted[j - 1].get("valor", 0.0)), 2)
            candidatos = [
                ((dp[i - 1][j][0] + 1, dp[i - 1][j][1]), "skip_dav"),
                (dp[i][j - 1], "skip_nfce"),
                ((dp[i - 1][j - 1][0], dp[i - 1][j - 1][1] + abs(valor_dav - valor_nfce)), "match"),
            ]
            melhor_estado, decisao = _melhor_estado(candidatos)
            dp[i][j] = melhor_estado
            caminho[i][j] = decisao

    faltantes = []
    i = n
    j = m
    while i > 0 or j > 0:
        decisao = caminho[i][j] if i >= 0 and j >= 0 else ""
        if decisao == "match":
            i -= 1
            j -= 1
        elif decisao == "skip_nfce":
            j -= 1
        else:
            if i > 0:
                faltantes.append(davs_sorted[i - 1])
            i -= 1

    return sorted(faltantes, key=lambda item: item.get("pedido", ""))


def _build_mva_conferencia_observation_rows(registros: list[dict]) -> list[tuple[str, str, str]]:
    rows: list[tuple[str, str, str]] = []
    for item in registros or []:
        origem = _normalize_caixa_client(item.get("origem", ""))
        numero_exibicao = str(item.get("numero_exibicao") or "-").strip()
        observacao = str(item.get("observacao") or "").strip()
        valor = item.get("valor")
        valor_texto = "-" if valor in (None, "") else f"R$ {format_number_br(valor)}"
        if origem == "DAV":
            tipo = "DAV pendente"
        elif origem == "CF":
            tipo = "CF pendente"
        else:
            tipo = "Pendência"
        detalhe = f"{numero_exibicao}: {observacao}" if observacao else numero_exibicao
        rows.append((tipo, detalhe, valor_texto))
    return rows


def _comparar_caixa_fechamento_mva_com_pagamentos(relatorio_caixa: dict, relatorio_fechamento: dict) -> dict:
    itens_caixa = relatorio_caixa.get("itens_caixa", [])
    itens_nfce = relatorio_fechamento.get("nfces", [])
    relatorios_pagamento = dict(relatorio_fechamento.get("relatorios_pagamento") or {})
    fiscal_status_map_mva = {
        _normalize_fiscal_number(numero): dict(info)
        for numero, info in (relatorio_fechamento.get("fiscal_status_map") or {}).items()
        if _normalize_fiscal_number(numero) and bool((info or {}).get("cancelada"))
    }
    if relatorio_fechamento.get("fiscal_status_source") == "clipp_movements":
        _nfes_ativas = []
        erro_minhas_notas = None
    else:
        _nfes_ativas, fiscal_status_map_mva, erro_minhas_notas = _load_minhas_notas_mva_context(
            relatorio_caixa.get("periodo", "")
        )

    davs_sem_cupom = _infer_mva_davs_sem_cupom(itens_caixa, itens_nfce)
    cancelados_ausentes = _build_mva_cancelled_coupon_pool(itens_nfce, fiscal_status_map_mva)
    davs_sem_cupom, _cancelados_correspondentes = _match_davs_with_mva_cancelled_coupons(
        davs_sem_cupom,
        cancelados_ausentes,
    )
    cfs_faltantes = sorted(
        {
            _normalize_fiscal_number(numero)
            for numero in relatorio_fechamento.get("nfces_faltantes_sequencia", [])
            if _normalize_fiscal_number(numero)
        },
        key=int,
    )

    registros = []
    for item in davs_sem_cupom:
        pedido = re.sub(r"\D", "", str(item.get("pedido", "")))
        registros.append(
            {
                "numero": pedido,
                "numero_exibicao": f"DAV {_display_fiscal_number(pedido) if pedido else item.get('pedido', '-')}",
                "origem": "DAV",
                "observacao": "DAV sem cupom no fechamento",
                "valor": round(float(item.get("valor", 0.0)), 2),
            }
        )
    registros.extend(
        _build_mva_cancelled_coupon_registros(
            cfs_faltantes,
            cancelados_ausentes,
        )
    )
    cupons_cancelados = [
        item for item in registros
        if item.get("origem") == "CF" and str(item.get("observacao") or "").strip() == "Cupom cancelado"
    ]
    registros_alerta = [
        item for item in registros
        if not (item.get("origem") == "CF" and str(item.get("observacao") or "").strip() == "Cupom cancelado")
    ]

    cancelados_pagamento_map = {str(item.get("numero") or ""): dict(item) for item in cupons_cancelados}

    correlacao_rows = []
    pix_fechamento_only: list[dict] = []
    pix_machine_only: list[dict] = []
    card_fechamento_only: list[dict] = []
    card_machine_only: list[dict] = []
    alert_rows: list[tuple[str, str, str]] = _build_mva_conferencia_observation_rows(registros_alerta)
    if erro_minhas_notas:
        avisos_minhas_notas = [
            "Nao foi possivel consultar o status dos cupons da MVA no Minhas Notas nesta analise."
        ]
    else:
        avisos_minhas_notas = []

    def _register_cancelled_payment_item(titulo_pagamento: str, item_cancelado: dict) -> None:
        numero_cancelado = str(item_cancelado.get("numero") or "")
        if not numero_cancelado:
            return
        numero_exibicao = (
            item_cancelado.get("numero_exibicao")
            or _display_fiscal_number(numero_cancelado)
        )
        valor = item_cancelado.get("valor")
        if numero_cancelado not in cancelados_pagamento_map:
            cancelados_pagamento_map[numero_cancelado] = {
                "numero": numero_cancelado,
                "numero_exibicao": numero_exibicao,
                "valor": valor,
                "observacao": "Cupom cancelado",
            }
            alert_rows.append(
                (
                    "Cupom cancelado",
                    f"{titulo_pagamento}: CF {numero_exibicao} cancelado permaneceu no fechamento",
                    f"R$ {format_number_br(valor or 0.0)}",
                )
            )

    dinheiro_report = relatorios_pagamento.get("dinheiro") or {}
    _dinheiro_itens_ativos, dinheiro_cancelados = _split_cancelled_payment_items(
        list(dinheiro_report.get("itens_autorizados") or []),
        fiscal_status_map_mva,
    )
    for item_cancelado in dinheiro_cancelados:
        _register_cancelled_payment_item("Dinheiro", item_cancelado)
    dinheiro_total = round(float(dinheiro_report.get("total_autorizado", 0.0) or 0.0), 2)
    correlacao_rows.append(
        (
            "Dinheiro",
            f"R$ {format_number_br(dinheiro_total)}",
            "-",
            "Interno",
        )
    )


    comparacoes = [
        (
            "PIX",
            relatorios_pagamento.get("pix_caixa"),
            relatorios_pagamento.get("pix_fechamento"),
        ),
        (
            "Cartão Crédito",
            relatorios_pagamento.get("cartao_credito_caixa"),
            relatorios_pagamento.get("cartao_credito"),
        ),
        (
            "Cartão Débito",
            relatorios_pagamento.get("cartao_debito_caixa"),
            relatorios_pagamento.get("cartao_debito"),
        ),
    ]

    for titulo_pagamento, report_externo, report_fechamento in comparacoes:
        if not report_externo and not report_fechamento:
            continue
        report_fechamento = report_fechamento or {}
        itens_fechamento = list(report_fechamento.get("itens_autorizados") or [])
        itens_fechamento, itens_fechamento_cancelados = _split_cancelled_payment_items(
            itens_fechamento,
            fiscal_status_map_mva,
        )
        for item_cancelado in itens_fechamento_cancelados:
            _register_cancelled_payment_item(titulo_pagamento, item_cancelado)
        itens_externos = list((report_externo or {}).get("itens_autorizados") or [])
        total_fechamento = round(float(report_fechamento.get("total_autorizado", 0.0) or 0.0), 2)
        total_externo = round(float((report_externo or {}).get("total_autorizado", 0.0) or 0.0), 2)
        status_correlacao = "Finalizado" if report_externo and abs(total_fechamento - total_externo) < 0.01 else "Divergente"
        correlacao_rows.append(
            (
                titulo_pagamento,
                f"R$ {format_number_br(total_fechamento)}",
                f"R$ {format_number_br(total_externo)}",
                status_correlacao,
            )
        )

        if not report_externo:
            alert_rows.append(
                (
                    "Relatório ausente",
                    f"{titulo_pagamento}: relatório local não encontrado na pasta atual de execução.",
                    "-",
                )
            )
            continue

        _matched, externos_sem_fechamento, fechamento_sem_externo = _multiset_match_by_value(
            itens_externos,
            itens_fechamento,
            campo_esquerda="valor_bruto",
            campo_direita="valor_bruto",
        )

        for item in externos_sem_fechamento:
            valor = round(float(item.get("valor_bruto", 0.0)), 2)
            detalhe = item.get("data_venda") or item.get("numero_exibicao") or item.get("numero") or "-"
            payload = {
                "titulo": titulo_pagamento,
                "data_venda": detalhe,
                "valor": valor,
            }
            if titulo_pagamento == "PIX":
                pix_machine_only.append(payload)
            else:
                card_machine_only.append(payload)

        for item in fechamento_sem_externo:
            numero = _normalize_fiscal_number(item.get("numero", "") or item.get("numero_exibicao", ""))
            if numero and (fiscal_status_map_mva.get(numero) or {}).get("cancelada"):
                continue
            valor = round(float(item.get("valor_bruto", 0.0)), 2)
            payload = {
                "titulo": titulo_pagamento,
                "numero_exibicao": item.get("numero_exibicao") or _display_fiscal_number(item.get("numero", "")),
                "valor": valor,
            }
            if titulo_pagamento == "PIX":
                pix_fechamento_only.append(payload)
            else:
                card_fechamento_only.append(payload)

    for item in pix_fechamento_only:
        alert_rows.append(
            (
                "CF sem Transação Bancária",
                f"PIX: CF {item.get('numero_exibicao') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )
    for item in card_fechamento_only:
        alert_rows.append(
            (
                "CF sem Transação Bancária",
                f"{item.get('titulo')}: CF {item.get('numero_exibicao') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )
    for item in pix_machine_only:
        alert_rows.append(
            (
                "Transação Bancária sem CF/NF",
                f"PIX: {item.get('data_venda') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )
    for item in card_machine_only:
        alert_rows.append(
            (
                "Transação Bancária sem CF/NF",
                f"{item.get('titulo')}: {item.get('data_venda') or '-'}",
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
        )

    cancelados_visiveis = list(cancelados_pagamento_map.values())

    alertas_report = _build_eh_alerts_report(
        relatorio_caixa.get("periodo"),
        alert_rows,
        pix_fechamento_rows=[
            (f"CF {item.get('numero_exibicao') or '-'}", f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in pix_fechamento_only
        ],
        pix_maquina_rows=[
            ("PIX", str(item.get("data_venda") or "-"), f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in pix_machine_only
        ],
        cartao_fechamento_rows=[
            (f"{item.get('titulo')}: CF {item.get('numero_exibicao') or '-'}", f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in card_fechamento_only
        ],
        cartao_maquina_rows=[
            (str(item.get("titulo") or "Cartão"), str(item.get("data_venda") or "-"), f"R$ {format_number_br(item.get('valor', 0.0))}")
            for item in card_machine_only
        ],
        cancelados_rows=_build_cancelados_rows_from_pendencias(cancelados_visiveis),
        allow_empty=True,
    )

    total_caixa = round(float(relatorio_caixa.get("total_caixa", 0.0)), 2)
    total_resumo = round(float(relatorio_fechamento.get("total_nfce", 0.0)), 2)
    valor_davs_pendentes = round(
        sum(float(item.get("valor", 0.0)) for item in registros_alerta if item.get("valor") not in (None, "")),
        2,
    )
    valor_banco_pendente = round(
        sum(float(item.get("valor", 0.0)) for item in pix_fechamento_only + card_fechamento_only + pix_machine_only + card_machine_only),
        2,
    )
    valor_faltantes = round(valor_davs_pendentes + valor_banco_pendente, 2)

    if alertas_report:
        alertas_report["hidden_in_menu"] = True
        alertas_report["caixa_modelo"] = "MVA"
        alertas_report["summary_items"] = [
            ("Período", str(relatorio_caixa.get("periodo") or "Não identificado")),
            ("Pendências", str(len(alert_rows))),
            ("Total Pendências", f"R$ {format_number_br(valor_banco_pendente)}"),
        ]
        alertas_report["summary_items"][1] = (
            str(alertas_report["summary_items"][1][0]),
            str(_count_visible_alert_rows(alertas_report)),
        )
        alertas_report["correlacao_rows"] = correlacao_rows
        alertas_report["valor_total_vendas"] = total_caixa
        alertas_report["valor_pendente"] = valor_banco_pendente
        alertas_report["texto_informativo"] = ""
        relatorios_pagamento[alertas_report["categoria"]] = alertas_report
        for key in (
            "pix_caixa",
            "pix_fechamento",
            "cartao_credito",
            "cartao_debito",
            "cartao_credito_caixa",
            "cartao_debito_caixa",
        ):
            if relatorios_pagamento.get(key):
                relatorios_pagamento[key]["hidden_in_menu"] = True

    pending_alert_rows = [row for row in alert_rows if not _is_cancelled_coupon_alert_row(row)]
    status = "Confere" if not registros_alerta and not pending_alert_rows else "Faltante"
    if alertas_report:
        alertas_report["status"] = status
    visible_alert_count = _count_visible_alert_rows(alertas_report)

    periodo_unico, _ = _extract_period_range(relatorio_caixa.get("periodo", ""))
    cupons_cancelados = list(cancelados_visiveis)
    subtitle = str(relatorio_fechamento.get("subtitle") or "").strip()
    if cupons_cancelados:
        fonte_cancelamentos = (
            "Clipp"
            if relatorio_fechamento.get("fiscal_status_source") == "clipp_movements"
            else "Minhas Notas"
        )
        subtitle = (
            (subtitle + " ") if subtitle else ""
        ) + f"Cupons cancelados identificados no {fonte_cancelamentos}: {len(cupons_cancelados)}."
    escopo_relatorio = (
        relatorio_fechamento.get("escopo_relatorio")
        or relatorio_caixa.get("escopo_relatorio")
    )
    escopo_horario_aplicado = list(
        relatorio_fechamento.get("escopo_horario_aplicado")
        or relatorio_caixa.get("escopo_horario_aplicado")
        or []
    )
    return {
        "fechamento_modelo": "MVA",
        "caixa_modelo": "MVA",
        "subtitle": subtitle,
        "arquivo_caixa": relatorio_caixa.get("arquivo"),
        "arquivo_resumo": relatorio_fechamento.get("arquivo"),
        "arquivo_resumo_titulo": relatorio_fechamento.get("arquivo_resumo_titulo") or "Arquivo Fechamento",
        "periodo": periodo_unico or relatorio_caixa.get("periodo"),
        "total_caixa": total_caixa,
        "total_caixa_titulo": "Total DAVs finalizados",
        "total_resumo_nfce": total_resumo,
        "total_resumo_titulo": relatorio_fechamento.get("total_resumo_titulo") or "Total Fechamento de caixa",
        "nfces_faltantes_count": len(registros_alerta),
        "faltantes_titulo": "DAVs/CF faltantes",
        "valor_faltantes": valor_faltantes,
        "status": status,
        "cupons_cancelados_count": len(cupons_cancelados),
        "cupons_cancelados_valor": round(
            sum(float(item.get("valor", 0.0) or 0.0) for item in cupons_cancelados),
            2,
        ),
        "secao_titulo": "DAVs/CF para conferência",
        "empty_message": "Nenhum DAV/CF faltante encontrado.",
        "escopo_relatorio": escopo_relatorio,
        "escopo_horario_aplicado": escopo_horario_aplicado,
        "registros_conferencia": sorted(
            registros,
            key=lambda item: (
                0 if item.get("origem") == "DAV" else 1,
                int(item["numero"]) if item.get("numero") else 0,
            ),
        ),
        "relatorios_pagamento": relatorios_pagamento,
        "alertas_count": visible_alert_count,
        "avisos_usuario": list(relatorio_fechamento.get("avisos_usuario") or []) + avisos_minhas_notas,
    }


def _comparar_caixa_resumo_nfce_mva(relatorio_caixa: dict, relatorio_nfce: dict) -> dict:
    if relatorio_nfce.get("arquivo_tipo") == "fechamento_caixa_clipp_mva":
        return _comparar_caixa_fechamento_mva_com_pagamentos(relatorio_caixa, relatorio_nfce)

    itens_caixa = relatorio_caixa.get("itens_caixa", [])
    itens_nfce = relatorio_nfce.get("nfces", [])
    itens_cupom_base = [
        item
        for item in itens_caixa
        if _is_mva_cupom_client(item.get("cliente", ""))
    ]

    davs_sem_cupom = _infer_mva_davs_sem_cupom(itens_caixa, itens_nfce)
    nfes_ativas, fiscal_status_map_mva, erro_minhas_notas = _load_minhas_notas_mva_context(
        relatorio_caixa.get("periodo", "")
    )
    if nfes_ativas:
        davs_sem_cupom, nfes_identificadas = _match_davs_with_minhas_notas_nfes_from_items(
            davs_sem_cupom,
            nfes_ativas,
        )
    else:
        nfes_identificadas = []
    cancelados_ausentes = _build_mva_cancelled_coupon_pool(itens_nfce, fiscal_status_map_mva)
    davs_sem_cupom, _cancelados_correspondentes = _match_davs_with_mva_cancelled_coupons(
        davs_sem_cupom,
        cancelados_ausentes,
    )
    cfs_faltantes = sorted(
        {
            _normalize_fiscal_number(numero)
            for numero in relatorio_nfce.get("nfces_faltantes_sequencia", [])
            if _normalize_fiscal_number(numero)
        },
        key=int,
    )

    registros = []
    for item in davs_sem_cupom:
        pedido = re.sub(r"\D", "", str(item.get("pedido", "")))
        registros.append(
            {
                "numero": pedido,
                "numero_exibicao": f"DAV {_display_fiscal_number(pedido) if pedido else item.get('pedido', '-')}",
                "origem": "DAV",
                "observacao": "DAV sem cupom",
                "valor": round(float(item.get("valor", 0.0)), 2),
            }
        )
    registros.extend(
        _build_mva_cancelled_coupon_registros(
            cfs_faltantes,
            cancelados_ausentes,
        )
    )

    total_caixa = round(sum(float(item.get("valor", 0.0)) for item in itens_cupom_base), 2)
    total_resumo = round(float(relatorio_nfce.get("total_nfce", 0.0)), 2)
    cupons_cancelados = [
        item for item in registros
        if item.get("origem") == "CF" and str(item.get("observacao") or "").strip() == "Cupom cancelado"
    ]
    valor_cupons_cancelados = round(
        sum(float(item.get("valor", 0.0) or 0.0) for item in cupons_cancelados),
        2,
    )
    registros_alerta = [
        item for item in registros
        if not (item.get("origem") == "CF" and str(item.get("observacao") or "").strip() == "Cupom cancelado")
    ]
    if nfes_identificadas:
        valor_faltantes = round(
            sum(float(item.get("valor", 0.0)) for item in registros_alerta if item.get("valor") not in (None, "")),
            2,
        )
    else:
        valor_faltantes = round(total_caixa - total_resumo - valor_cupons_cancelados, 2)
    status = "Confere" if abs(valor_faltantes) < 0.01 else "Faltante"
    periodo_unico, _ = _extract_period_range(relatorio_caixa.get("periodo", ""))
    subtitle = (
        "Compara os DAVs aptos para cupom com o relatório de Cupons e aponta DAVs/CF para conferência."
    )
    if nfes_identificadas:
        subtitle += (
            f" NF-e identificadas automaticamente no Minhas Notas: {len(nfes_identificadas)}."
        )
    if cupons_cancelados:
        subtitle += f" Cupons cancelados identificados no Minhas Notas: {len(cupons_cancelados)}."
    elif erro_minhas_notas:
        subtitle += " Consulta ao Minhas Notas indisponivel nesta analise."
    escopo_relatorio = (
        relatorio_nfce.get("escopo_relatorio")
        or relatorio_caixa.get("escopo_relatorio")
    )
    escopo_horario_aplicado = list(
        relatorio_nfce.get("escopo_horario_aplicado")
        or relatorio_caixa.get("escopo_horario_aplicado")
        or []
    )

    alert_rows = _build_mva_conferencia_observation_rows(registros_alerta)
    if erro_minhas_notas:
        alert_rows.append(("Minhas Notas", "Consulta indisponível nesta análise.", "-"))

    relatorios_pagamento: dict[str, dict] = {}
    alertas_report = _build_eh_alerts_report(
        relatorio_caixa.get("periodo"),
        alert_rows,
        cancelados_rows=_build_cancelados_rows_from_pendencias(cupons_cancelados),
        allow_empty=False,
    )
    if alertas_report:
        alertas_report["hidden_in_menu"] = True
        alertas_report["caixa_modelo"] = "MVA"
        alertas_report["summary_items"] = [
            ("Período", str(relatorio_caixa.get("periodo") or "Não identificado")),
            ("Pendências", str(len(alert_rows))),
            ("Total Pendências", f"R$ {format_number_br(valor_faltantes)}"),
        ]
        alertas_report["summary_items"][1] = (
            str(alertas_report["summary_items"][1][0]),
            str(_count_visible_alert_rows(alertas_report)),
        )
        alertas_report["correlacao_rows"] = []
        alertas_report["valor_total_vendas"] = total_caixa
        alertas_report["valor_pendente"] = valor_faltantes
        alertas_report["texto_informativo"] = ""
        alertas_report["status"] = status
        relatorios_pagamento[alertas_report["categoria"]] = alertas_report
    visible_alert_count = _count_visible_alert_rows(alertas_report)

    return {
        "fechamento_modelo": "MVA",
        "caixa_modelo": "MVA",
        "subtitle": subtitle,
        "arquivo_caixa": relatorio_caixa.get("arquivo"),
        "arquivo_resumo": relatorio_nfce.get("arquivo"),
        "arquivo_resumo_titulo": "Arquivo Cupons",
        "periodo": periodo_unico or relatorio_caixa.get("periodo"),
        "total_caixa": total_caixa,
        "total_caixa_titulo": "Total DAVs para cupom",
        "total_resumo_nfce": total_resumo,
        "total_resumo_titulo": "Total Cupons",
        "nfces_faltantes_count": len(registros_alerta),
        "faltantes_titulo": "DAVs/CF faltantes",
        "valor_faltantes": valor_faltantes,
        "nfes_identificadas_count": len(nfes_identificadas),
        "nfes_identificadas_valor": round(
            sum(float(item.get("valor", 0.0)) for item in nfes_identificadas),
            2,
        ),
        "cupons_cancelados_count": len(cupons_cancelados),
        "cupons_cancelados_valor": valor_cupons_cancelados,
        "status": status,
        "secao_titulo": "DAVs/CF para conferência",
        "empty_message": "Nenhum DAV/CF faltante encontrado.",
        "escopo_relatorio": escopo_relatorio,
        "escopo_horario_aplicado": escopo_horario_aplicado,
        "registros_conferencia": sorted(
            registros,
            key=lambda item: (
                0 if item.get("origem") == "DAV" else 1,
                int(item["numero"]) if item.get("numero") else 0,
            ),
        ),
        "alertas_count": visible_alert_count,
        "relatorios_pagamento": relatorios_pagamento,
        "nfes_identificadas": nfes_identificadas,
        "erro_minhas_notas": erro_minhas_notas,
        "avisos_usuario": (
            ["Nao foi possivel consultar o status dos cupons da MVA no Minhas Notas nesta analise."]
            if erro_minhas_notas
            else []
        ),
    }


def comparar_caixa_resumo_nfce(relatorio_caixa: dict, relatorio_nfce: dict) -> dict:
    if (relatorio_caixa.get("caixa_modelo") or "").upper() == "MVA" or (
        relatorio_nfce.get("resumo_modelo") or ""
    ).upper() == "MVA":
        return _comparar_caixa_resumo_nfce_mva(relatorio_caixa, relatorio_nfce)
    return _comparar_caixa_resumo_nfce_eh(relatorio_caixa, relatorio_nfce)

def canonicalize_name(raw: str) -> str:
    _ensure_mapping_loaded()
    key = _normalize_key(raw)

    # 1) se existe como abreviação no mapping
    if key in mapping:
        return mapping[key]

    # 2) se já é o nome completo
    if key in CANON_BY_VALUE_UPPER:
        return CANON_BY_VALUE_UPPER[key]

    prefix_matches = [
        canon for canon_upper, canon in CANON_BY_VALUE_UPPER.items()
        if canon_upper.startswith(f"{key} ")
    ]
    if len(prefix_matches) == 1:
        return prefix_matches[0]

    # 3) fuzzy matching
    match = difflib.get_close_matches(key, list(CANON_BY_VALUE_UPPER.keys()), n=1, cutoff=0.93)
    if match:
        return CANON_BY_VALUE_UPPER[match[0]]

    # fallback
    return raw.strip().title()

# --- Funções principais ---

def criar_etiquetas_legacy():
    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas
    from global_vars import results_by_source

    # precisa ter MVA e EH carregados
    if not results_by_source["MVA"] or not results_by_source["EH"]:
        messagebox.showwarning("Aviso", "É necessário carregar os dois PDFs (MVA e EH).")
        return

    caminho = filedialog.asksaveasfilename(
        defaultextension=".pdf",
        filetypes=[("Arquivo PDF", "*.pdf")],
        title="Salvar etiquetas"
    )
    if not caminho:
        return False

    c = canvas.Canvas(caminho, pagesize=A4)
    largura, altura = A4
    y = altura - 50
    c.setFont("Helvetica", 11)

    # junta os vendedores que aparecem em qualquer um dos dois
    vendedores = set()
    for _, res in results_by_source["MVA"]:
        vendedores.update(res.keys())
    for _, res in results_by_source["EH"]:
        vendedores.update(res.keys())

    for vendedor in sorted(vendedores):
        total_mva = total_eh = 0.0
        atendidos_mva = atendidos_eh = 0
        clientes_mva = clientes_eh = 0

        # soma MVA
        for _, res in results_by_source["MVA"]:
            if vendedor in res:
                total_mva += parse_number(res[vendedor].get("total_vendas", 0))
                atendidos_mva += res[vendedor].get("atendidos", 0)
                clientes_mva += res[vendedor].get("total_clientes", 0)

        # soma EH
        for _, res in results_by_source["EH"]:
            if vendedor in res:
                total_eh += parse_number(res[vendedor].get("total_vendas", 0))
                atendidos_eh += res[vendedor].get("atendidos", 0)
                clientes_eh += res[vendedor].get("total_clientes", 0)

        total_final = total_mva + total_eh
        clientes_total = clientes_mva + clientes_eh

        # imprime no PDF em duas linhas
        linha1 = f"{vendedor} = {format_number_br(total_mva)} + {format_number_br(total_eh)} = {format_number_br(total_final)}"
        linha2 = f"Clientes atendidos = {clientes_mva} + {clientes_eh} = {clientes_total}"

        c.drawString(50, y, linha1)
        y -= 15
        c.drawString(50, y, linha2)
        y -= 30

        if y < 50:  # quebra página
            c.showPage()
            c.setFont("Helvetica", 11)
            y = altura - 50

    c.save()
    messagebox.showinfo("Sucesso", f"✅ Etiquetas geradas em:\n{caminho}")

def _rows_from_tree_for_labels(tree):
    rows = []
    if tree is None:
        return rows

    for item in tree.get_children():
        values = tree.item(item).get("values", [])
        if not values:
            continue

        vendedor = str(values[0]).strip() if len(values) > 0 else ""
        if not vendedor:
            continue

        atendidos = int(parse_number(values[1])) if len(values) > 1 else 0
        devolucoes = int(parse_number(values[2])) if len(values) > 2 else 0
        total_clientes = int(parse_number(values[3])) if len(values) > 3 else 0
        total_vendas = parse_number(values[4]) if len(values) > 4 else 0.0

        rows.append({
            "vendedor": vendedor,
            "atendidos": atendidos,
            "devolucoes": devolucoes,
            "total_clientes": total_clientes,
            "total_vendas": total_vendas,
        })

    return rows


def criar_etiquetas(tree=None):
    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas
    from global_vars import results_by_source

    rows_from_table = _rows_from_tree_for_labels(tree)

    if not rows_from_table:
        if not results_by_source["MVA"] or not results_by_source["EH"]:
            messagebox.showwarning("Aviso", "E necessario carregar os dois PDFs (MVA e EH).")
            return

    caminho = filedialog.asksaveasfilename(
        defaultextension=".pdf",
        filetypes=[("Arquivo PDF", "*.pdf")],
        title="Salvar etiquetas"
    )
    if not caminho:
        return False

    c = canvas.Canvas(caminho, pagesize=A4)
    largura, altura = A4
    y = altura - 50
    c.setFont("Helvetica", 11)

    if rows_from_table:
        for row in sorted(rows_from_table, key=lambda x: x["vendedor"].lower()):
            linha1 = f"{row['vendedor']} = {format_number_br(row['total_vendas'])}"
            linha2 = (
                f"Atendidos: {row['atendidos']} | "
                f"Devolucoes: {row['devolucoes']} | "
                f"Total Final: {row['total_clientes']}"
            )
            c.drawString(50, y, linha1)
            y -= 15
            c.drawString(50, y, linha2)
            y -= 30
            if y < 50:
                c.showPage()
                c.setFont("Helvetica", 11)
                y = altura - 50
    else:
        vendedores = set()
        for _, res in results_by_source["MVA"]:
            vendedores.update(res.keys())
        for _, res in results_by_source["EH"]:
            vendedores.update(res.keys())

        for vendedor in sorted(vendedores):
            total_mva = total_eh = 0.0
            clientes_mva = clientes_eh = 0
            for _, res in results_by_source["MVA"]:
                if vendedor in res:
                    total_mva += parse_number(res[vendedor].get("total_vendas", 0))
                    clientes_mva += res[vendedor].get("total_clientes", 0)
            for _, res in results_by_source["EH"]:
                if vendedor in res:
                    total_eh += parse_number(res[vendedor].get("total_vendas", 0))
                    clientes_eh += res[vendedor].get("total_clientes", 0)

            total_final = total_mva + total_eh
            clientes_total = clientes_mva + clientes_eh
            linha1 = f"{vendedor} = {format_number_br(total_mva)} + {format_number_br(total_eh)} = {format_number_br(total_final)}"
            linha2 = f"Clientes atendidos = {clientes_mva} + {clientes_eh} = {clientes_total}"
            c.drawString(50, y, linha1)
            y -= 15
            c.drawString(50, y, linha2)
            y -= 30
            if y < 50:
                c.showPage()
                c.setFont("Helvetica", 11)
                y = altura - 50

    c.save()
    messagebox.showinfo("Sucesso", f"Etiquetas geradas em:\n{caminho}")


def extrair_planilha_online():
    import gspread
    from oauth2client.service_account import ServiceAccountCredentials
    pd = _get_pd()

    global LAST_MVA, LAST_EH  # usar globais para comparar depois

    scope = [
        "https://spreadsheets.google.com/feeds",
        "https://www.googleapis.com/auth/drive"
    ]
    cred_path = resource_path(os.path.join("data", "credenciaisAPI.json"))

    creds = ServiceAccountCredentials.from_json_keyfile_name(cred_path, scope)
    client = gspread.authorize(creds)

    SPREADSHEET_ID = "1eiHbe-NkZ4cM5tMtq2JN574rwa2thR6X7T40EZM_3TA"

    sheetMVA = client.open_by_key(SPREADSHEET_ID).worksheet("MVA")
    sheetEH = client.open_by_key(SPREADSHEET_ID).worksheet("EH")

    valoresMVA = sheetMVA.get_all_values()
    valoresEH = sheetEH.get_all_values()

    # pega cabeçalho da linha 2
    colsMVA = valoresMVA[1]
    colsEH = valoresEH[1]

    # corrige duplicados
    colsMVA = [f"col{i}_{c}" if colsMVA.count(c) > 1 else c for i, c in enumerate(colsMVA)]
    colsEH = [f"col{i}_{c}" if colsEH.count(c) > 1 else c for i, c in enumerate(colsEH)]

    dfMVA = pd.DataFrame(valoresMVA[2:], columns=colsMVA)
    dfEH = pd.DataFrame(valoresEH[2:], columns=colsEH)

    # 🔎 COMPARAÇÃO com os últimos dados exportados (mantém compatibilidade)
    if LAST_MVA is not None and LAST_EH is not None:
        try:
            if dfMVA.equals(LAST_MVA) and dfEH.equals(LAST_EH):
                return None
        except Exception:
            # se ocorrer qualquer erro de comparação, continua (não bloqueia)
            pass

    # Atualiza os globais com os novos dados (mantém comportamento anterior)
    LAST_MVA, LAST_EH = dfMVA.copy(), dfEH.copy()

    # --- Agregação por vendedor (soma MVA + EH) ---
    agregados = {}
    canon_cache = {}

    # concatena ambas as abas para processar de forma uniforme
    df_total = pd.concat([dfMVA, dfEH], ignore_index=True)

    for row in df_total.itertuples(index=False):
        vendedor_raw = str(row[0]).strip()
        if not vendedor_raw or vendedor_raw.lower() in ["nan", "none", ""]:
            continue

        if vendedor_raw in canon_cache:
            vendedor = canon_cache[vendedor_raw]
        else:
            vendedor = canonicalize_name(vendedor_raw)
            canon_cache[vendedor_raw] = vendedor

        if vendedor not in agregados:
            agregados[vendedor] = {"atendidos": 0, "total_vendas": 0.0}

        atend_row = 0
        total_row = 0.0

        # percorre o resto das colunas da linha somando valores numéricos
        for v in row[1:]:
            if pd.isna(v) or str(v).strip() == "":
                continue
            try:
                num = parse_number(str(v))
                total_row += num
                atend_row += 1
            except Exception:
                # ignora conteúdos não numéricos
                continue

        agregados[vendedor]["atendidos"] += atend_row
        agregados[vendedor]["total_vendas"] += total_row

    # transforma em DataFrame ordenado
    df_agg = pd.DataFrame(
        [(v, d["atendidos"], d["total_vendas"]) for v, d in agregados.items()],
        columns=["vendedor", "atendidos", "total_vendas"]
    ).sort_values("vendedor").reset_index(drop=True)

    return dfMVA, dfEH, df_agg

def carregar_planilha_async(tree_planilha, progress_var, progress_bar, root):
    btn_merge_spreadsheet = _UI_REFS.get("btn_merge_spreadsheet")
    pd = _get_pd()

    try:
        cancel_event.clear()
        progress_var.set(0)
        set_btn_cancel(state="normal")

        def worker():
            progressQueuePlanilha.put(("ui", {"action": "start_indeterminate"}))
            try:
                resultado = extrair_planilha_online()
                if resultado is None:
                    progressQueuePlanilha.put(("no_changes", None))
                    return

                # agora extrai também o DataFrame agregado
                dfMVA, dfEH, df_agg = resultado

                total_rows = len(df_agg)
                resultados = []

                # percorre o df_agg (já somado por vendedor)
                for i, row in enumerate(df_agg.itertuples(index=False, name=None), start=1):
                    # 🔹 Verifica se foi cancelado
                    if cancel_event.is_set():
                        progressQueuePlanilha.put(("done_planilha", {"__cancelled__": True}))
                        return

                    vendedor = str(row[0]).strip()
                    if not vendedor:
                        continue

                    atendidos = int(row[1]) if not pd.isna(row[1]) else 0
                    total = float(row[2]) if not pd.isna(row[2]) else 0.0

                    if atendidos > 0 or total > 0:
                        resultados.append((vendedor, atendidos, total))

                    # 🔹 Atualiza progresso gradualmente
                    progresso = int(i * 100 / max(1, total_rows))
                    progressQueuePlanilha.put(("progress", progresso))

                progressQueuePlanilha.put(("done_planilha", resultados))

            except Exception as e:
                progressQueuePlanilha.put(("error", f"Erro ao carregar planilha: {e}"))

        progressQueuePlanilha = queue.Queue()
        worker_thread = threading.Thread(target=worker, daemon=True)
        worker_thread.start()

        def poll_queue_planilha():
            try:
                for _ in range(50):
                    kind, payload = progressQueuePlanilha.get_nowait()
                    if kind == "progress":
                        if str(progress_bar["mode"]) == "indeterminate":
                            progress_bar.stop()
                            progress_bar.config(mode="determinate")
                        progress_var.set(payload)
                        progress_bar.update_idletasks()
                    elif kind == "ui":
                        action = payload.get("action")
                        if action == "start_indeterminate":
                            progress_bar.config(mode="indeterminate")
                            progress_bar.start(10)
                    elif kind == "no_changes":
                        set_btn_cancel()
                        progress_bar.stop()
                        progress_bar.config(mode="determinate")
                        progress_var.set(0)
                        messagebox.showinfo("Aviso", "Nenhum dado novo foi adicionado.")
                        return
                    elif kind == "done_planilha":
                        set_btn_cancel()
                        if isinstance(payload, dict) and payload.get("__cancelled__"):
                            progress_bar.stop()
                            progress_bar.config(mode="determinate")
                            progress_var.set(0)
                            messagebox.showinfo("Cancelado", "Carregamento da planilha foi cancelado.")
                        else:
                            for item in tree_planilha.get_children():
                                tree_planilha.delete(item)
                            if btn_merge_spreadsheet:
                                btn_merge_spreadsheet.configure(state="normal")
                            for vendedor, atendidos, total in payload:
                                tree_planilha.insert(
                                    "",
                                    "end",
                                    values=(
                                        vendedor,
                                        atendidos,
                                        f"R$ {total:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
                                    )
                                )
                            messagebox.showinfo("Sucesso", "Planilha online carregada com sucesso.")
                        return
                    elif kind == "error":
                        set_btn_cancel()
                        messagebox.showerror("Erro", payload)
                        return
            except queue.Empty:
                pass
            root.after(10, poll_queue_planilha)

        poll_queue_planilha()

    except Exception as e:
        set_btn_cancel()
        messagebox.showerror("Erro", f"Erro ao iniciar carregamento da planilha: {e}")

def carregar_planilhas_duplas_async(tree_mva, tree_eh, progress_var, progress_bar, root):
    """Carrega as planilhas online (MVA e EH) em paralelo, cada uma no seu Treeview."""
    import threading, queue
    pd = _get_pd()
    global cancel_event
    btn_merge_spreadsheet = _UI_REFS.get("btn_merge_spreadsheet")

    try:
        cancel_event.clear()
        progress_var.set(0)
        set_btn_cancel(state="normal")
        progressQueuePlanilha = queue.Queue()

        def worker():
            progressQueuePlanilha.put(("ui", {"action": "start_indeterminate"}))
            try:
                resultado = extrair_planilha_online()
                if resultado is None:
                    progressQueuePlanilha.put(("no_changes", None))
                    return

                dfMVA, dfEH, _ = resultado  # ignoramos o df_agg por enquanto

                # Preenche as duas tabelas
                def collect_tree_rows(df):
                    total_rows = len(df)
                    rows: list[tuple[str, int, str]] = []
                    for i, row in enumerate(df.itertuples(index=False, name=None), start=1):
                        if cancel_event.is_set():
                            progressQueuePlanilha.put(("done_planilha", {"__cancelled__": True}))
                            return None
                        vendedor = str(row[0]).strip()
                        if not vendedor:
                            continue
                        valores = row[1:]
                        atendidos = sum(1 for v in valores if str(v).strip() != "")
                        total = 0.0
                        for v in valores:
                            try:
                                total += parse_number(str(v))
                            except Exception:
                                pass
                        if atendidos > 0 or total > 0:
                            rows.append(
                                (
                                    vendedor,
                                    atendidos,
                                    f"R$ {total:,.2f}".replace(",", "X").replace(".", ",").replace("X", "."),
                                )
                            )
                        progresso = int(i * 50 / max(1, total_rows))  # 50% pra cada tabela
                        progressQueuePlanilha.put(("progress", progresso))
                    return rows

                rows_mva = collect_tree_rows(dfMVA)
                if rows_mva is None:
                    return
                rows_eh = collect_tree_rows(dfEH)
                if rows_eh is None:
                    return

                progressQueuePlanilha.put(
                    (
                        "done_planilha",
                        {
                            "status": "ok",
                            "rows_mva": rows_mva,
                            "rows_eh": rows_eh,
                        },
                    )
                )

            except Exception as e:
                progressQueuePlanilha.put(("error", f"Erro ao carregar planilhas: {e}"))

        threading.Thread(target=worker, daemon=True).start()

        def poll_queue():
            try:
                for _ in range(50):
                    kind, payload = progressQueuePlanilha.get_nowait()
                    if kind == "progress":
                        if str(progress_bar["mode"]) == "indeterminate":
                            progress_bar.stop()
                            progress_bar.config(mode="determinate")
                        progress_var.set(payload)
                        progress_bar.update_idletasks()
                    elif kind == "ui":
                        if payload.get("action") == "start_indeterminate":
                            progress_bar.config(mode="indeterminate")
                            progress_bar.start(10)
                    elif kind == "no_changes":
                        set_btn_cancel()
                        progress_bar.stop()
                        progress_bar.config(mode="determinate")
                        progress_var.set(0)
                        messagebox.showinfo("Aviso", "Nenhum dado novo foi adicionado.")
                        return
                    elif kind == "done_planilha":
                        set_btn_cancel()
                        progress_bar.stop()
                        progress_bar.config(mode="determinate")
                        if isinstance(payload, dict) and payload.get("__cancelled__"):
                            progress_var.set(0)
                            messagebox.showinfo("Cancelado", "Carregamento da planilha foi cancelado.")
                            return
                        if isinstance(payload, dict):
                            for tree in (tree_mva, tree_eh):
                                for item in tree.get_children():
                                    tree.delete(item)
                            if btn_merge_spreadsheet:
                                btn_merge_spreadsheet.configure(state="normal")
                            for values in payload.get("rows_mva", []):
                                tree_mva.insert("", "end", values=values)
                            for values in payload.get("rows_eh", []):
                                tree_eh.insert("", "end", values=values)
                            _scroll_tree_to_top(tree_mva)
                            _scroll_tree_to_top(tree_eh)
                            progress_var.set(100)
                            messagebox.showinfo("Sucesso", "Planilhas online carregadas com sucesso.")
                            return
                        return
                    elif kind == "error":
                        set_btn_cancel()
                        messagebox.showerror("Erro", payload)
                        return
            except queue.Empty:
                pass
            root.after(10, poll_queue)

        poll_queue()

    except Exception as e:
        set_btn_cancel()
        messagebox.showerror("Erro", f"Erro ao iniciar carregamento das planilhas: {e}")


  
def tree_update(tree):
    for item in tree.get_children():
        tree.delete(item)
    
    mesclado = mesclar_resultados(list_results)
    
    for vendedor, dados in _sorted_rows_by_total_vendas(mesclado):
        if not _has_visible_data(dados):
            continue
        total_vendas_str = ""
        if dados["total_vendas"] > 0:
            total_vendas_str = format_number_br(dados["total_vendas"])
        else:
            total_vendas_str = format_number_br(abs(dados["total_vendas"]))   

        tree.insert("", "end", values=(
            vendedor,
            dados['atendidos'],
            dados['devolucoes'],
            dados['total_clientes'],
            total_vendas_str
        ))
    _scroll_tree_to_top(tree)

def mesclar_resultados(list_results):
    mesclado = {}
    cache_canon = {}  # 🔹 Cache para memoização de canonicalize_name

    for res in list_results:
        for vend, dados in res.items():
            # Usa o cache para evitar chamadas repetidas a canonicalize_name
            if vend in cache_canon:
                canon = cache_canon[vend]
            else:
                canon = canonicalize_name(vend)
                cache_canon[vend] = canon

            if canon not in mesclado:
                mesclado[canon] = {
                    "atendidos": 0,
                    "devolucoes": 0,
                    "total_clientes": 0,
                    "total_vendas": 0.0
                }

            mesclado[canon]["atendidos"]      += dados.get("atendidos", 0)
            mesclado[canon]["devolucoes"]     += dados.get("devolucoes", 0)

            tv_str = str(dados.get("total_vendas", ""))
            mesclado[canon]["total_vendas"] += parse_number(tv_str)

    # 🔹 Recalcula clientes finais uma vez ao final
    for dados in mesclado.values():
        dados["total_clientes"] = dados["atendidos"] - dados["devolucoes"]

    return mesclado


def _resolve_merge_planilha_sources(results_by_source, tree_mva, tree_eh) -> tuple[list[str], list[str], list[str]]:
    imported_sources = [
        source
        for source in ("MVA", "EH")
        if list((results_by_source or {}).get(source) or [])
    ]
    online_sources = [
        source
        for source, tree_view in (("MVA", tree_mva), ("EH", tree_eh))
        if tree_view is not None and tree_view.get_children()
    ]
    selected_sources = [source for source in imported_sources if source in online_sources]
    return imported_sources, online_sources, selected_sources


def ordenar_coluna(tree, col, reverse):
    dados = [(tree.set(k, col), k) for k in tree.get_children()]
    
    def try_num(v):
        v = str(v)
        try:
            return float(v.replace(".", "").replace(",", "."))
        except:
            return v.lower()
        
    dados.sort(key=lambda t: try_num(t[0]), reverse=reverse)

    for index, (val, k) in enumerate(dados):
        tree.move(k, '', index)

    tree.heading(col, command=lambda: ordenar_coluna(tree, col, not reverse))

def check_for_updates(root):
    import requests
    import zipfile
    import shutil
    import subprocess
    import sys
    import re

    def version_key(raw: str):
        text = (raw or "").strip().lstrip("vV")
        nums = [int(x) for x in re.findall(r"\d+", text)]
        while len(nums) < 4:
            nums.append(0)
        return tuple(nums[:4])

    def resolve_latest_release() -> dict | None:
        headers = {"Accept": "application/vnd.github+json", "User-Agent": "RelatorioClientes-Updater"}
        timeout = 20

        # 1) endpoint direto do latest
        try:
            resp = requests.get(f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest", headers=headers, timeout=timeout)
            resp.raise_for_status()
            data = resp.json()
            if data and data.get("tag_name"):
                return data
        except Exception:
            pass

        # 2) fallback: lista releases e pega maior versao valida (nao pre-release)
        try:
            resp = requests.get(f"https://api.github.com/repos/{GITHUB_REPO}/releases", headers=headers, timeout=timeout)
            resp.raise_for_status()
            releases = resp.json() or []
            candidates = [r for r in releases if not r.get("draft") and not r.get("prerelease") and r.get("tag_name")]
            if not candidates:
                return None
            candidates.sort(key=lambda r: version_key(r.get("tag_name", "")), reverse=True)
            return candidates[0]
        except Exception:
            return None

    def worker():
        try:
            data = resolve_latest_release()
            if not data or not data.get("tag_name"):
                return

            latest_version = data["tag_name"].lstrip("vV")

            if version_key(latest_version) > version_key(APP_VERSION):
                # Mostra dialogo na thread principal usando after()
                def ask_user():
                    if messagebox.askyesno("Atualizacao Disponivel",
                        f"Uma nova versão ({latest_version}) está disponível! Deseja baixar agora?"):
                        assets = data.get("assets", [])
                        zip_asset = None
                        for asset in assets:
                            name = asset.get("name", "").lower()
                            if name.endswith(".zip"):
                                zip_asset = asset
                                break
                        if not zip_asset:
                            messagebox.showerror("Erro", "Nenhum arquivo .zip encontrado na release.")
                            return

                        asset_url = zip_asset["browser_download_url"]
                        base_dir = os.path.join(os.getenv("LOCALAPPDATA", "."), "RelatorioClientes")
                        os.makedirs(base_dir, exist_ok=True)
                        zip_path = os.path.join(base_dir, f"RelatorioClientes-{latest_version}.zip")
                        extract_dir = os.path.join(base_dir, f"app-{latest_version}")
                        try:
                            download = requests.get(asset_url, stream=True, timeout=30)
                            with open(zip_path, "wb") as f:
                                for chunk in download.iter_content(8192):
                                    f.write(chunk)
                            if os.path.exists(extract_dir):
                                shutil.rmtree(extract_dir, ignore_errors=True)
                            with zipfile.ZipFile(zip_path, "r") as zf:
                                zf.extractall(extract_dir)

                            exe_path = os.path.join(extract_dir, "Relatorio de Clientes.exe")
                            if not os.path.exists(exe_path):
                                for root_dir, _dirs, files in os.walk(extract_dir):
                                    for fname in files:
                                        if fname.lower().endswith(".exe"):
                                            exe_path = os.path.join(root_dir, fname)
                                            break
                                    if os.path.exists(exe_path):
                                        break

                            if not os.path.exists(exe_path):
                                messagebox.showerror("Erro", "Não foi possível localizar o executável na atualização.")
                                return

                            messagebox.showinfo("Atualizado",
                                "Nova versão baixada e extraída. O aplicativo será reiniciado.")
                            try:
                                subprocess.Popen([exe_path])
                            except Exception as e:
                                messagebox.showerror("Erro", f"Falha ao iniciar nova versao: {e}")
                                return
                            sys.exit(0)
                        except Exception as e:
                            messagebox.showerror("Erro no Download", f"Ocorreu um erro: {e}")
                root.after(0, ask_user)  # root e sua janela principal
            else:
                print("App atualizado.")

        except Exception as e:
            root.after(0, lambda: messagebox.showerror("Erro na Atualizacao",
                                                       f"Ocorreu um erro ao checar atualizacoes: {e}"))

    threading.Thread(target=worker, daemon=True).start()

def limpar_tabelas(tree, tree_planilha, label_files_var, progress_var):
    
    global LAST_EH, LAST_MVA, LAST_STATE_SPREADSHEET, LAST_HASH_MERGE

    # limpa as tabelas
    for item in tree.get_children():
        tree.delete(item)
    for item in tree_planilha.get_children():
        tree_planilha.delete(item)

    # reseta variáveis da UI
    label_files_var.set("Nenhum arquivo carregado")
    progress_var.set(0)

    # 🧹 Limpa histórico da mesclagem
    LAST_EH = None      
    LAST_MVA = None
    LAST_HASH_MERGE = None
    LAST_STATE_SPREADSHEET = {}    
    
    # também limpa lista de resultados
    from global_vars import list_results, listFiles
    btn_add_mais = _UI_REFS.get("btn_add_mais")
    btn_merge_spreadsheet = _UI_REFS.get("btn_merge_spreadsheet")
    btn = _UI_REFS.get("btn_select_pdf")
    btn_tag = _UI_REFS.get("btn_tag")

    from global_vars import results_by_source
    results_by_source["MVA"].clear()
    results_by_source["EH"].clear()

    if btn_merge_spreadsheet:
        btn_merge_spreadsheet.configure(state="normal")
    if btn_add_mais:
        btn_add_mais.configure(state="normal")
    if btn:
        btn.configure(state="normal")
    if btn_tag:
        btn_tag.configure(state="disabled", fg_color="#EE9919", text_color_disabled="gray45")
    
    list_results.clear()
    listFiles.clear()

    messagebox.showinfo("Limpo", "Todas as tabelas foram limpas com sucesso!")
            
def _excel_export(tree):
    pd = _get_pd()
    # Extrai os dados
    cols = [tree.heading(col)["text"] for col in tree["columns"]]
    dados = [tree.item(item)["values"] for item in tree.get_children()]

    if not dados:
        messagebox.showwarning("Aviso", "Não há dados para exportar.")
        return

    df = pd.DataFrame(dados, columns=cols)

    # Converter colunas numéricas
    colunas_numericas = ["Atendidos", "Devoluções", "Total Final", "Total Vendas"]
    for col in colunas_numericas:
        if col in df.columns:
            df[col] = pd.to_numeric(
                df[col].astype(str)
                .str.replace(".", "", regex=False)
                .str.replace(",", ".", regex=False),
                errors="coerce"
            ).fillna(0.0)

    caminho = filedialog.asksaveasfilename(
        defaultextension=".xlsx",
        filetypes=[("Arquivo Excel", "*.xlsx")],
        title="Salvar relatório"
    )
    
    if not caminho:
        return False
    
    df.to_excel(caminho, index=False, engine="openpyxl")
    
    messagebox.showinfo("Sucesso", f"✅ Relatório exportado para:\n{caminho}")

def _pdf_export(tree) -> bool:

    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas
    
    # Extrai os dados
    cols = [tree.heading(col)["text"] for col in tree["columns"]]
    dados = [tree.item(item)["values"] for item in tree.get_children()]

    if not dados:
        messagebox.showwarning("Aviso", "Não há dados para exportar.")
        return

    caminho = filedialog.asksaveasfilename(
        defaultextension=".pdf",
        filetypes=[("Arquivo PDF", "*.pdf")],
        title="Salvar relatório PDF"
    )
    if not caminho:
        return False

    # Criar PDF simples
    c = canvas.Canvas(caminho, pagesize=A4)
    largura, altura = A4
    y = altura - 50
    c.setFont("Helvetica-Bold", 12)
    c.drawString(50, y, "Relatório de Vendas")
    y -= 30

    # Cabeçalho
    c.setFont("Helvetica-Bold", 10)
    for i, col in enumerate(cols):
        c.drawString(50 + i * 120, y, col)
    y -= 20

    # Dados
    c.setFont("Helvetica", 9)
    for row in dados:
        for i, valor in enumerate(row):
            c.drawString(50 + i * 120, y, str(valor))
        y -= 20
        if y < 50:
            c.showPage()
            y = altura - 50

    c.save()
    messagebox.showinfo("Sucesso", f"✅ Relatório exportado para:\n{caminho}")

def limpar_tabelas_duplas(tree, tree_mva, tree_eh, label_files_var, progress_var):
    """Limpa todas as tabelas (PDF + MVA + EH) e reseta os indicadores."""
    global LAST_EH, LAST_MVA, LAST_STATE_SPREADSHEET, LAST_HASH_MERGE


    confirm = messagebox.askyesno("Confirmação", "Deseja realmente limpar todas as tabelas?")
    if not confirm:
        return

    for t in (tree, tree_mva, tree_eh):
        for item in t.get_children():
            t.delete(item)
            
        # 🧹 Limpa histórico da mesclagem
    LAST_EH = None      
    LAST_MVA = None
    LAST_HASH_MERGE = None
    LAST_STATE_SPREADSHEET = {}    
    
    # também limpa lista de resultados
    from global_vars import list_results, listFiles
    btn_add_mais = _UI_REFS.get("btn_add_mais")
    btn_merge_spreadsheet = _UI_REFS.get("btn_merge_spreadsheet")
    btn = _UI_REFS.get("btn_select_pdf")
    btn_tag = _UI_REFS.get("btn_tag")
    from global_vars import results_by_source
    results_by_source["MVA"].clear()
    results_by_source["EH"].clear()

    
    if btn_merge_spreadsheet:
        btn_merge_spreadsheet.configure(state="normal")
    if btn_add_mais:
        btn_add_mais.configure(state="normal")
    if btn:
        btn.configure(state="normal")
    if btn_tag:
        btn_tag.configure(state="disabled", fg_color="#EE9919", text_color_disabled="gray45")
    
    list_results.clear()
    listFiles.clear()

    label_files_var.set("Nenhum arquivo selecionado")
    progress_var.set(0)
    messagebox.showinfo("Limpeza concluída", "🧹 Todas as tabelas foram limpas com sucesso.")

def _hash_tree_snapshot(trees):
    import hashlib

    hasher = hashlib.md5()
    for tree in trees:
        for item in tree.get_children():
            values = tree.item(item)["values"]
            for val in values:
                hasher.update(str(val).encode("utf-8"))
                hasher.update(b"\x1f")
            hasher.update(b"\x1e")
    return hasher.hexdigest()



def mesclar_tabelas_duplas(tree, progress_var, progress_bar, root, label_files_var,
                           tree_mva, tree_eh):
    """
    Mescla os valores das planilhas online (MVA e EH) com a tabela de PDFs (tree).
    Soma os dados das duas planilhas e atualiza a barra de progresso.
    """
    btn_merge_spreadsheet = _UI_REFS.get("btn_merge_spreadsheet")
    btn_add_mais = _UI_REFS.get("btn_add_mais")
    btn = _UI_REFS.get("btn_select_pdf")
    global LAST_HASH_MERGE, LAST_STATE_SPREADSHEET

    import threading, queue
    if btn_merge_spreadsheet:
        btn_merge_spreadsheet.configure(state="enabled")

    # 🔹 Verifica se alguma tabela está vazia
    if not tree.get_children():
        messagebox.showwarning("Aviso", "A tabela de PDFs está vazia. Importe pelo menos um PDF antes de mesclar.")
        return
    if not tree_mva.get_children() and not tree_eh.get_children():
        messagebox.showwarning("Aviso", "As tabelas online estão vazias. Carregue as planilhas MVA e EH antes de mesclar.")
        return
    try:
        from global_vars import results_by_source
    except Exception:
        results_by_source = {"MVA": [], "EH": []}
    imported_sources, online_sources, selected_sources = _resolve_merge_planilha_sources(
        results_by_source,
        tree_mva,
        tree_eh,
    )
    if not imported_sources:
        messagebox.showwarning("Aviso", "Importe pelo menos um PDF antes de mesclar.")
        return
    if not selected_sources:
        messagebox.showwarning(
            "Aviso",
            "Nenhuma planilha online correspondente aos PDFs importados foi carregada.",
        )
        return
    if len(imported_sources) == 1:
        only_source = imported_sources[0]
        if not messagebox.askyesno(
            "Mesclar Planilhas",
            (
                f"Apenas o PDF da {only_source} foi importado.\n\n"
                f"A mesclagem será feita somente com a planilha online da {only_source}.\n\n"
                "Se quiser mesclar MVA e EH, clique em Não e importe mais um arquivo."
            ),
        ):
            return
    elif len(selected_sources) == 1 and len(imported_sources) == 2:
        only_source = selected_sources[0]
        if not messagebox.askyesno(
            "Mesclar Planilhas",
            (
                "Os PDFs de MVA e EH já foram importados.\n\n"
                f"No momento, só a planilha online da {only_source} está carregada para mesclagem.\n\n"
                f"Deseja continuar mesclando somente a {only_source}?\n"
                "Se quiser mesclar MVA e EH, clique em Não e carregue a outra planilha."
            ),
        ):
            return

    # Snapshot dos dados atuais (pra detectar duplicacoes)
    novo_hash = _hash_tree_snapshot((tree, tree_mva, tree_eh))
    if LAST_HASH_MERGE == novo_hash:
        messagebox.showinfo("Aviso", "⚠️ Esses dados já foram mesclados. Nenhuma alteração detectada.")
        return

    LAST_HASH_MERGE = novo_hash
    merge_queue = queue.Queue()

    # ------------------ THREAD WORKER ------------------
    def worker():
        try:
            # 1️⃣ Extrai dados da tabela de PDFs
            dados_pdf = {}
            for item in tree.get_children():
                vals = tree.item(item)["values"]
                vendedor = str(vals[0]).strip()
                atendidos = int(vals[1])
                devolucoes = int(vals[2])
                total_clientes = int(vals[3])
                total_vendas = parse_number(str(vals[4]) if vals[4] else "0")
                dados_pdf[vendedor] = {
                    "atendidos": atendidos,
                    "devolucoes": devolucoes,
                    "total_clientes": total_clientes,
                    "total_vendas": total_vendas
                }

            # 2️⃣ Extrai dados das planilhas MVA e EH
            def extrair_dados(tree_view):
                dados = {}
                for item in tree_view.get_children():
                    vals = tree_view.item(item)["values"]
                    vendedor = str(vals[0]).strip()
                    atendidos = int(vals[1])
                    total_vendas = parse_number(str(vals[2]) if vals[2] else "0")
                    if vendedor:
                        if vendedor not in dados:
                            dados[vendedor] = {"atendidos": 0, "total_vendas": 0.0}
                        dados[vendedor]["atendidos"] += atendidos
                        dados[vendedor]["total_vendas"] += total_vendas
                return dados

            dados_planilha_total = {}
            source_trees = {"MVA": tree_mva, "EH": tree_eh}
            for source in selected_sources:
                dados_source = extrair_dados(source_trees[source])
                for vendedor, dados in dados_source.items():
                    if vendedor not in dados_planilha_total:
                        dados_planilha_total[vendedor] = {
                            "atendidos": 0,
                            "total_vendas": 0.0,
                        }
                    dados_planilha_total[vendedor]["atendidos"] += dados.get("atendidos", 0)
                    dados_planilha_total[vendedor]["total_vendas"] += dados.get("total_vendas", 0.0)

            # 4️⃣ Aplica controle de duplicação incremental (igual ao código original)
            novos_planilha = {}
            for idx, (vendedor, dados) in enumerate(dados_planilha_total.items(), start=1):
                ultimo = LAST_STATE_SPREADSHEET.get(vendedor, {"atendidos": 0, "total_vendas": 0.0})
                delta_atendidos = max(0, dados["atendidos"] - ultimo["atendidos"])
                delta_vendas = max(0, dados["total_vendas"] - ultimo["total_vendas"])
                if delta_atendidos == 0 and delta_vendas == 0:
                    continue

                novos_planilha[vendedor] = {
                    "atendidos": delta_atendidos,
                    "total_vendas": delta_vendas
                }
                LAST_STATE_SPREADSHEET[vendedor] = dados
                progresso = int(idx * 40 / max(1, len(dados_planilha_total)))
                merge_queue.put(("progress", progresso))

            # 5️⃣ Mescla tudo
            total_vendedores = len(set(dados_pdf.keys()) | set(novos_planilha.keys()))
            for idx, vendedor in enumerate(set(dados_pdf.keys()) | set(novos_planilha.keys()), start=1):
                pdf_data = dados_pdf.get(vendedor, {"atendidos": 0, "devolucoes": 0, "total_clientes": 0, "total_vendas": 0})
                plan_data = novos_planilha.get(vendedor, {"atendidos": 0, "total_vendas": 0})

                merged = {
                    "atendidos": pdf_data["atendidos"] + plan_data["atendidos"],
                    "devolucoes": pdf_data["devolucoes"],
                    "total_clientes": (pdf_data["atendidos"] + plan_data["atendidos"]) - pdf_data["devolucoes"],
                    "total_vendas": pdf_data["total_vendas"] + plan_data["total_vendas"]
                }
                dados_pdf[vendedor] = merged

                progresso = 40 + int(idx * 60 / max(1, total_vendedores))
                merge_queue.put(("progress", progresso))

            merge_queue.put(("done", dados_pdf))

        except Exception as e:
            merge_queue.put(("error", str(e)))

    threading.Thread(target=worker, daemon=True).start()

    # ------------------ POLL QUEUE ------------------
    def poll_merge_queue():
        try:
            for _ in range(50):
                kind, payload = merge_queue.get_nowait()
                if kind == "progress":
                    progress_var.set(payload)
                    progress_bar.update_idletasks()
                elif kind == "done":
                    if btn_merge_spreadsheet:
                        btn_merge_spreadsheet.configure(state="disabled")
                    if btn_add_mais:
                        btn_add_mais.configure(state="disabled")
                    if btn:
                        btn.configure(state="disabled")

                    for item in tree.get_children():
                        tree.delete(item)

                    for vendedor, dados in _sorted_rows_by_total_vendas(payload):
                        if not _has_visible_data(dados):
                            continue
                        tree.insert("", "end", values=(
                            vendedor,
                            dados["atendidos"],
                            dados["devolucoes"],
                            dados["total_clientes"],
                            format_number_br(dados["total_vendas"])
                        ))
                    _scroll_tree_to_top(tree)
                    progress_var.set(100)
                    scope_label = " + ".join(selected_sources)
                    messagebox.showinfo("Concluído", f"Mesclagem das tabelas (PDF + {scope_label}) finalizada!")
                    return
                elif kind == "error":
                    messagebox.showerror("Erro", f"Erro na mesclagem: {payload}")
                    return
        except queue.Empty:
            pass
        root.after(10, poll_merge_queue)

    poll_merge_queue()

def analisar_SALES_PERIOD(caminho_pdf):
    """
    Analisa as datas de vendas em um PDF e retorna o período de vendas.
    """
    
    from datetime import datetime
    global SALES_PERIOD
    datas = []

    try:
        pdfplumber = _get_pdfplumber()
        with pdfplumber.open(caminho_pdf) as pdf:
            for pagina in pdf.pages:
                texto = pagina.extract_text() or ""
                for linha in texto.splitlines():
                    data_str = _extract_sale_date(linha)
                    if not data_str:
                        continue
                    try:
                        data = datetime.strptime(data_str, "%d/%m/%Y")
                        datas.append(data)
                    except ValueError:
                        pass

        if not datas:
            SALES_PERIOD = None
            return None

        primeira = min(datas)
        ultima = max(datas)
        SALES_PERIOD = f"{primeira.strftime('%d/%m/%Y')} - {ultima.strftime('%d/%m/%Y')}"
        return SALES_PERIOD

    except Exception as e:
        print(f"Erro ao analisar período de vendas: {e}")
        SALES_PERIOD = None
        return None



# Importações delegadas ao pdf_parser
from pdf_parser import (_get_pd, _get_pdfplumber, _inspect_pdf_text_layer, _pdf_sem_texto_message, _analisar_pdf_caixa_eh, _analisar_pdf_caixa_mva, analisar_pdf_caixa, _analisar_pdf_resumo_nfce_eh, _analisar_pdf_resumo_nfce_mva, analisar_pdf_resumo_nfce, source_pdf_async, adicionar_pdf, processar_pdf_sem_ui)

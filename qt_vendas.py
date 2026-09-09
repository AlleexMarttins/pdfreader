from __future__ import annotations

import sys
import os
import re
import time
import json
import datetime as dt
import tempfile
import queue
import threading
import difflib
import unicodedata
import atexit
from typing import Callable, List, Optional
from pathlib import Path

from PySide6 import QtCore, QtGui, QtWidgets, QtPrintSupport

from clipp_mva import ClippMvaConnectionError, ClippMvaReader, database_is_configured

from utils import (
    source_pdf_async,
    adicionar_pdf,
    analisar_pdf_caixa,
    analisar_pdf_resumo_nfce,
    analisar_pdf_fechamento_caixa_mva_clipp,
    combinar_relatorios_caixa_mva,
    comparar_caixa_resumo_nfce,
    criar_relatorio_orcamentos_mva_vazio,
    aplicar_escopo_relatorio_caixa,
    describe_closing_scope,
    gerar_relatorios_caixa_eh_zweb,
    baixar_relatorios_caixa_eh_azulzinha,
    validar_periodo_relatorios_caixa,
    validar_arquivo_caixa_mva,
    validar_relatorio_pedidos_importados,
    validar_relatorio_resumo_nfce,
    ordenar_coluna,
    process_cancel,
    carregar_planilhas_duplas_async,
    limpar_tabelas_duplas,
    check_for_updates,
    resource_path,
    mesclar_tabelas_duplas,
    _pdf_export,
    _excel_export,
    parse_number,
    format_number_br,
    corrigir_texto,
    corrigir_estrutura_texto,
    criar_etiquetas,
    set_ui_refs,
    _active_report_dir,
    _get_gmail_api_credentials,
    cleanup_generated_auto_reports,
    get_gmail_oauth_status,
    list_generated_auto_reports,
)
from ui_dialogs import messagebox, filedialog, set_parent
from qt_adapters import (
    QtRootAdapter,
    QtVar,
    QtProgressBarAdapter,
    QtButtonAdapter,
    QtTreeAdapter,
)


_LEXEND_REPORTLAB_FONT_NAME: str | None = None


def _format_exception_message(exc: BaseException, fallback: str = "Falha inesperada.") -> str:
    message = corrigir_texto(str(exc)).strip()
    if message:
        return message
    exc_name = type(exc).__name__.strip()
    if exc_name:
        return f"{fallback} ({exc_name})"
    return fallback


def _center_message_box_buttons(box: QtWidgets.QMessageBox) -> None:
    box.setFont(_popup_font(box))
    button_box = box.findChild(QtWidgets.QDialogButtonBox)
    if button_box is not None:
        button_box.setCenterButtons(True)
    for button in box.buttons():
        button.setMinimumWidth(110)


def _popup_font(reference: QtWidgets.QWidget | None = None) -> QtGui.QFont:
    app = QtWidgets.QApplication.instance()
    base = None
    if reference is not None:
        try:
            base = reference.font()
        except Exception:
            base = None
    if base is None and app is not None:
        base = app.font()
    font = QtGui.QFont(base or QtGui.QFont())
    if font.pointSizeF() <= 0:
        font.setPointSize(10)
    else:
        font.setPointSizeF(10.0)
    return font


def _build_empty_table_icon(size: int = 90) -> QtGui.QPixmap:
    pixmap = QtGui.QPixmap(size, size)
    pixmap.fill(QtCore.Qt.transparent)

    painter = QtGui.QPainter(pixmap)
    painter.setRenderHint(QtGui.QPainter.Antialiasing, True)

    stroke = QtGui.QColor("#F0F5F7")
    accent = QtGui.QColor("#22D3E6")
    secondary = QtGui.QColor("#A7B6C2")
    pen_width = max(4, round(size * 0.055))

    page_left = size * 0.26
    page_top = size * 0.12
    page_right = size * 0.72
    page_bottom = size * 0.84
    fold = size * 0.16
    radius = size * 0.06

    path = QtGui.QPainterPath()
    path.moveTo(page_left + radius, page_top)
    path.lineTo(page_right - fold, page_top)
    path.lineTo(page_right, page_top + fold)
    path.lineTo(page_right, page_bottom - radius)
    path.quadTo(page_right, page_bottom, page_right - radius, page_bottom)
    path.lineTo(page_left + radius, page_bottom)
    path.quadTo(page_left, page_bottom, page_left, page_bottom - radius)
    path.lineTo(page_left, page_top + radius)
    path.quadTo(page_left, page_top, page_left + radius, page_top)

    painter.setPen(QtGui.QPen(stroke, pen_width, QtCore.Qt.SolidLine, QtCore.Qt.RoundCap, QtCore.Qt.RoundJoin))
    painter.setBrush(QtCore.Qt.NoBrush)
    painter.drawPath(path)
    painter.drawLine(
        QtCore.QPointF(page_right - fold, page_top),
        QtCore.QPointF(page_right - fold, page_top + fold),
    )
    painter.drawLine(
        QtCore.QPointF(page_right - fold, page_top + fold),
        QtCore.QPointF(page_right, page_top + fold),
    )

    painter.setPen(QtGui.QPen(secondary, max(2, pen_width - 2), QtCore.Qt.SolidLine, QtCore.Qt.RoundCap))
    bullet_x = page_left + size * 0.08
    line_start = bullet_x + size * 0.06
    line_end = page_right - size * 0.08
    for index in range(3):
        y = page_top + size * (0.22 + index * 0.12)
        painter.setBrush(secondary)
        painter.drawEllipse(QtCore.QPointF(bullet_x, y), size * 0.012, size * 0.012)
        painter.drawLine(QtCore.QPointF(line_start, y), QtCore.QPointF(line_end, y))

    painter.setPen(QtCore.Qt.NoPen)
    painter.setBrush(accent)
    dot_radius = size * 0.08
    painter.drawEllipse(
        QtCore.QPointF(page_right - size * 0.01, page_bottom - size * 0.02),
        dot_radius,
        dot_radius,
    )

    painter.end()
    return pixmap


def _apply_soft_shadow(
    widget: QtWidgets.QWidget,
    *,
    blur: float = 26.0,
    offset_y: float = 8.0,
    color: QtGui.QColor | None = None,
) -> None:
    effect = QtWidgets.QGraphicsDropShadowEffect(widget)
    effect.setBlurRadius(blur)
    effect.setOffset(0.0, offset_y)
    effect.setColor(color or QtGui.QColor(6, 10, 16, 120))
    widget.setGraphicsEffect(effect)


class ScrollLockTableView(QtWidgets.QTableView):
    def wheelEvent(self, event: QtGui.QWheelEvent) -> None:
        super().wheelEvent(event)
        event.accept()


class ScrollLockTableWidget(QtWidgets.QTableWidget):
    def wheelEvent(self, event: QtGui.QWheelEvent) -> None:
        super().wheelEvent(event)
        event.accept()


class EmptyStateTableWidget(ScrollLockTableWidget):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self._empty_state = QtWidgets.QWidget(self.viewport())
        self._empty_state.setObjectName("tableEmptyState")
        self._empty_state.setAttribute(QtCore.Qt.WA_TransparentForMouseEvents, True)
        layout = QtWidgets.QVBoxLayout(self._empty_state)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(8)
        layout.setAlignment(QtCore.Qt.AlignCenter)

        self._empty_icon = QtWidgets.QLabel()
        self._empty_icon.setObjectName("tableEmptyStateIcon")
        self._empty_icon.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(self._empty_icon, 0, QtCore.Qt.AlignCenter)

        self._empty_hint = QtWidgets.QLabel("")
        self._empty_hint.setObjectName("tableEmptyStateHint")
        self._empty_hint.setAlignment(QtCore.Qt.AlignCenter)
        self._empty_hint.hide()
        layout.addWidget(self._empty_hint, 0, QtCore.Qt.AlignCenter)

        model = self.model()
        model.rowsInserted.connect(self._sync_empty_state_visibility)
        model.rowsRemoved.connect(self._sync_empty_state_visibility)
        model.modelReset.connect(self._sync_empty_state_visibility)
        self._sync_empty_state_visibility()

    def set_empty_state(self, pixmap: QtGui.QPixmap, message: str = "") -> None:
        self._empty_icon.setPixmap(pixmap)
        message = corrigir_texto(str(message or "")).strip()
        self._empty_hint.setText(message)
        self._empty_hint.setVisible(bool(message))
        self._sync_empty_state_geometry()
        self._sync_empty_state_visibility()

    def resizeEvent(self, event: QtGui.QResizeEvent) -> None:
        super().resizeEvent(event)
        self._sync_empty_state_geometry()

    def empty_state_visible(self) -> bool:
        return self._empty_state.isVisible()

    def _sync_empty_state_geometry(self) -> None:
        self._empty_state.setGeometry(self.viewport().rect())
        self._empty_state.raise_()

    def _sync_empty_state_visibility(self, *_args) -> None:
        self._sync_empty_state_geometry()
        self._empty_state.setVisible(self.rowCount() == 0)


def _get_reportlab_font_names() -> tuple[str, str]:
    global _LEXEND_REPORTLAB_FONT_NAME

    if _LEXEND_REPORTLAB_FONT_NAME:
        return (_LEXEND_REPORTLAB_FONT_NAME, _LEXEND_REPORTLAB_FONT_NAME)

    try:
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfbase.ttfonts import TTFont

        font_path = resource_path(os.path.join("data", "Lexend-Regular.ttf"))
        if os.path.exists(font_path):
            font_name = "Lexend"
            if font_name not in pdfmetrics.getRegisteredFontNames():
                pdfmetrics.registerFont(TTFont(font_name, font_path))
            _LEXEND_REPORTLAB_FONT_NAME = font_name
            return (font_name, font_name)
    except Exception:
        pass

    _LEXEND_REPORTLAB_FONT_NAME = "Helvetica"
    return ("Helvetica-Bold", "Helvetica")


def _create_a4_printer() -> QtPrintSupport.QPrinter:
    printer = QtPrintSupport.QPrinter(QtPrintSupport.QPrinter.HighResolution)
    printer.setPageOrientation(QtGui.QPageLayout.Portrait)
    printer.setPageSize(QtGui.QPageSize(QtGui.QPageSize.A4))
    printer.setPageMargins(QtCore.QMarginsF(6, 6, 6, 6), QtGui.QPageLayout.Millimeter)
    printer.setFullPage(False)
    return printer


def _configure_printer_for_a4(printer: QtPrintSupport.QPrinter) -> QtPrintSupport.QPrinter:
    printer.setPageOrientation(QtGui.QPageLayout.Portrait)
    printer.setPageSize(QtGui.QPageSize(QtGui.QPageSize.A4))
    printer.setPageMargins(QtCore.QMarginsF(6, 6, 6, 6), QtGui.QPageLayout.Millimeter)
    printer.setFullPage(False)
    return printer


def _resolve_default_printer() -> QtPrintSupport.QPrinter:
    printer_info = QtPrintSupport.QPrinterInfo.defaultPrinter()
    printer_name = str(printer_info.printerName() or "").strip()
    if printer_info.isNull() or not printer_name:
        raise RuntimeError("Nenhuma impressora padrao esta configurada no Windows.")

    printer = _create_a4_printer()
    printer.setPrinterName(printer_name)
    _configure_printer_for_a4(printer)
    if not printer.isValid():
        raise RuntimeError(
            f"A impressora padrão '{printer_name}' não está disponível para impressão."
        )
    return printer


def _pending_print_jobs_path() -> Path:
    return Path(_active_report_dir()) / "pending_print_jobs.json"


def _next_pending_print_retry_dt(now: dt.datetime | None = None) -> dt.datetime:
    now = now or dt.datetime.now()
    target = now.replace(hour=8, minute=0, second=0, microsecond=0) + dt.timedelta(days=1)
    return target


def _parse_pending_print_datetime(value: object) -> dt.datetime | None:
    text = str(value or "").strip()
    if not text:
        return None
    try:
        return dt.datetime.fromisoformat(text)
    except ValueError:
        return None


def _print_document_page_style() -> str:
    return "width:100%;max-width:none;margin:0 auto;padding:8pt 0 0;text-align:center;"


def _render_html_document_to_printer(
    html: str,
    printer: QtPrintSupport.QPrinter,
    font_family: str | None = None,
) -> None:
    _configure_printer_for_a4(printer)
    document = QtGui.QTextDocument()
    document.setDefaultFont(
        QtGui.QFont(font_family or QtWidgets.QApplication.font().family() or "Lexend", 8)
    )
    page_rect = printer.pageRect(QtPrintSupport.QPrinter.Point)
    if page_rect.width() <= 0 or page_rect.height() <= 0:
        raise RuntimeError("A impressora selecionada não retornou uma área de página válida.")
    document.setPageSize(page_rect.size())
    document.setHtml(html)
    document.print_(printer)


class ReadOnlyTableModel(QtCore.QAbstractTableModel):
    def __init__(
        self,
        headers: tuple[str, ...],
        rows: list[tuple[str, ...]],
        *,
        highlight_status_column: bool = False,
        parent: QtCore.QObject | None = None,
    ) -> None:
        super().__init__(parent)
        self._headers = [corrigir_texto(str(header)) for header in headers]
        self._rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in rows
        ]
        self._highlight_status_column = highlight_status_column

    def rowCount(self, parent: QtCore.QModelIndex = QtCore.QModelIndex()) -> int:
        if parent.isValid():
            return 0
        return len(self._rows)

    def columnCount(self, parent: QtCore.QModelIndex = QtCore.QModelIndex()) -> int:
        if parent.isValid():
            return 0
        return len(self._headers)

    def data(self, index: QtCore.QModelIndex, role: int = QtCore.Qt.DisplayRole):
        if not index.isValid():
            return None
        try:
            value = self._rows[index.row()][index.column()]
        except IndexError:
            return None

        if role == QtCore.Qt.DisplayRole:
            return value
        if role == QtCore.Qt.TextAlignmentRole:
            return int(QtCore.Qt.AlignCenter)
        if role == QtCore.Qt.ForegroundRole:
            color = self._foreground_for_cell(index.column(), value)
            if color is not None:
                return QtGui.QBrush(color)
        return None

    def headerData(
        self,
        section: int,
        orientation: QtCore.Qt.Orientation,
        role: int = QtCore.Qt.DisplayRole,
    ):
        if role != QtCore.Qt.DisplayRole:
            return None
        if orientation == QtCore.Qt.Horizontal:
            try:
                return self._headers[section]
            except IndexError:
                return None
        return str(section + 1)

    def _foreground_for_cell(self, column: int, value: str) -> QtGui.QColor | None:
        normalized = corrigir_texto(str(value or "")).strip().casefold()
        if not normalized:
            return None
        if self._highlight_status_column and column == max(0, len(self._headers) - 1):
            if any(token in normalized for token in ("confere", "finalizado", "interno")):
                return QtGui.QColor("#2FA36B")
            if any(token in normalized for token in ("divergente", "faltante", "pendente", "cancelado")):
                return QtGui.QColor("#D96C3F")
        if normalized.startswith("r$ -"):
            return QtGui.QColor("#A3A3A3")
        return None


class SourceDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle("Origem do PDF")
        self.setModal(True)
        layout = QtWidgets.QVBoxLayout(self)
        label = QtWidgets.QLabel("Este PDF pertence a qual empresa?")
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        self._choice = None

        btn_mva = QtWidgets.QPushButton("MVA")
        btn_eh = QtWidgets.QPushButton("HORIZONTE")
        btn_mva.clicked.connect(lambda: self._set_choice("MVA"))
        btn_eh.clicked.connect(lambda: self._set_choice("EH"))
        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch()
        for btn in (btn_mva, btn_eh):
            btn.setStyleSheet("text-align:center;")
            btn.setMinimumWidth(120)
            buttons.addWidget(btn)
        buttons.addStretch()
        layout.addLayout(buttons)

        self.setFixedSize(280, 140)

    def _set_choice(self, value: str) -> None:
        self._choice = value
        self.accept()

    def choice(self) -> Optional[str]:
        if self.exec() == QtWidgets.QDialog.Accepted:
            return self._choice
        return None


class InstructionDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget, title: str, message: str) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle(corrigir_texto(title))
        self.setModal(True)
        self.resize(430, 170)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(12)

        label = QtWidgets.QLabel(corrigir_texto(message))
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label, 1)

        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch()

        btn_continue = QtWidgets.QPushButton("Continuar")
        btn_continue.setStyleSheet("text-align:center;")
        btn_continue.setMinimumWidth(120)

        btn_continue.clicked.connect(self.accept)

        buttons.addWidget(btn_continue)
        buttons.addStretch()
        layout.addLayout(buttons)

    def confirmed(self) -> bool:
        return self.exec() == QtWidgets.QDialog.Accepted


class MvaBudgetMissingDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget) -> None:
        super().__init__(parent)
        self._choice: str | None = None
        self.setFont(_popup_font(self))
        self.setWindowTitle("Caixa MVA - Passo 2 de 3")
        self.setModal(True)
        self.resize(520, 220)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(14)

        label = QtWidgets.QLabel(
            corrigir_texto(
                "O app não encontrou um PDF de Orçamento da MVA.\n\n"
                "Se não houve orçamento neste dia, clique em Ignorar orçamento para seguir apenas com os DAVs."
            )
        )
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label, 1)

        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch()

        btn_select = QtWidgets.QPushButton("Selecionar orçamento")
        btn_select.setStyleSheet("text-align:center;")
        btn_select.setMinimumWidth(150)
        btn_select.clicked.connect(lambda: self._set_choice("select"))
        buttons.addWidget(btn_select)

        btn_ignore = QtWidgets.QPushButton("Ignorar orçamento")
        btn_ignore.setStyleSheet("text-align:center;")
        btn_ignore.setMinimumWidth(150)
        btn_ignore.clicked.connect(lambda: self._set_choice("ignore"))
        buttons.addWidget(btn_ignore)

        btn_cancel = QtWidgets.QPushButton("Cancelar")
        btn_cancel.setStyleSheet("text-align:center;")
        btn_cancel.setMinimumWidth(120)
        btn_cancel.clicked.connect(self.reject)
        buttons.addWidget(btn_cancel)

        buttons.addStretch()
        layout.addLayout(buttons)

    def _set_choice(self, value: str) -> None:
        self._choice = value
        self.accept()

    def choice(self) -> str | None:
        if self.exec() == QtWidgets.QDialog.Accepted:
            return self._choice
        return None


class LoadingStatusDialog(QtWidgets.QDialog):
    cancel_requested = QtCore.Signal()

    def __init__(self, parent: QtWidgets.QWidget, title: str, message: str) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self._cancelled = False
        self._closing_programmatically = False
        self._last_log_message = ""
        self.setWindowTitle(corrigir_texto(title))
        self.setModal(True)
        self.setWindowFlag(QtCore.Qt.WindowCloseButtonHint, True)
        self.resize(620, 340)
        self.setMinimumSize(620, 340)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(12)

        self._label = QtWidgets.QLabel(corrigir_texto(message))
        self._label.setWordWrap(True)
        self._label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(self._label, 1)

        self._bar = QtWidgets.QProgressBar()
        self._bar.setRange(0, 0)
        self._bar.setTextVisible(False)
        self._bar.setMinimumHeight(16)
        layout.addWidget(self._bar)

        debug_title = QtWidgets.QLabel("Debug em tempo real")
        debug_title.setAlignment(QtCore.Qt.AlignLeft | QtCore.Qt.AlignVCenter)
        layout.addWidget(debug_title)

        self._debug_log = QtWidgets.QPlainTextEdit()
        self._debug_log.setReadOnly(True)
        self._debug_log.setUndoRedoEnabled(False)
        self._debug_log.document().setMaximumBlockCount(300)
        self._debug_log.setLineWrapMode(QtWidgets.QPlainTextEdit.WidgetWidth)
        self._debug_log.setMinimumHeight(180)
        layout.addWidget(self._debug_log, 2)

        self.append_log(message)

    def set_status(self, message: str) -> None:
        normalized = corrigir_texto(message)
        self._label.setText(normalized)
        self.append_log(normalized)

    def append_log(self, message: str) -> None:
        normalized = corrigir_texto(message)
        if not normalized:
            return
        if normalized == self._last_log_message:
            return
        self._last_log_message = normalized
        timestamp = time.strftime("%H:%M:%S")
        self._debug_log.appendPlainText(f"[{timestamp}] {normalized}")
        scrollbar = self._debug_log.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())

    def was_cancelled(self) -> bool:
        return self._cancelled

    def close_gracefully(self) -> None:
        self._closing_programmatically = True
        self.close()

    def closeEvent(self, event: QtGui.QCloseEvent) -> None:
        if not self._closing_programmatically:
            self._cancelled = True
            self.cancel_requested.emit()
            self.set_status("Cancelando...")
            event.ignore()
            return
        super().closeEvent(event)


class AutomationTimeDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget, current_time: QtCore.QTime) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle("Horario da automacao")
        self.setModal(True)
        self.setFixedSize(320, 150)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(16, 16, 16, 16)
        layout.setSpacing(12)

        label = QtWidgets.QLabel(
            corrigir_texto("Escolha o horario diario da automacao.")
        )
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)

        self._time_edit = QtWidgets.QTimeEdit(current_time)
        self._time_edit.setDisplayFormat("HH:mm")
        self._time_edit.setAlignment(QtCore.Qt.AlignCenter)
        self._time_edit.setCalendarPopup(False)
        self._time_edit.setMinimumWidth(120)
        layout.addWidget(self._time_edit, alignment=QtCore.Qt.AlignHCenter)

        buttons = QtWidgets.QDialogButtonBox()
        btn_confirm = buttons.addButton("Confirmar", QtWidgets.QDialogButtonBox.AcceptRole)
        btn_cancel = buttons.addButton("Cancelar", QtWidgets.QDialogButtonBox.RejectRole)
        btn_confirm.setStyleSheet("text-align:center;")
        btn_cancel.setStyleSheet("text-align:center;")
        buttons.setCenterButtons(True)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def selected_time(self) -> QtCore.QTime | None:
        if self.exec() == QtWidgets.QDialog.Accepted:
            return self._time_edit.time()
        return None


class CaixaCnpjDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle("Caixa - CNPJ")
        self.setModal(True)
        self._choice = None
        self.resize(460, 160)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(12)

        label = QtWidgets.QLabel("Selecione o CNPJ para o fluxo de Caixa.")
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)

        btn_mva = QtWidgets.QPushButton("MVA")
        btn_eh = QtWidgets.QPushButton("Eletrônica Horizonte")
        buttons_row = QtWidgets.QHBoxLayout()
        buttons_row.setSpacing(12)
        buttons_row.addStretch()
        for btn in (btn_mva, btn_eh):
            btn.setStyleSheet("text-align:center;")
            btn.setMinimumHeight(36)
            btn.setMinimumWidth(150)
            btn.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Fixed)
            buttons_row.addWidget(btn)
        buttons_row.addStretch()
        layout.addLayout(buttons_row)

        btn_mva.clicked.connect(lambda: self._set_choice("MVA"))
        btn_eh.clicked.connect(lambda: self._set_choice("EH"))

    def _set_choice(self, value: str) -> None:
        self._choice = value
        self.accept()

    def choice(self) -> Optional[str]:
        if self.exec() == QtWidgets.QDialog.Accepted:
            return self._choice
        return None


class CaixaDateDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget, title: str, message: str) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle(title)
        self.setModal(True)
        self.resize(300, 160)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setSpacing(12)

        label = QtWidgets.QLabel(message)
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)

        self._date_edit = QtWidgets.QDateEdit(QtCore.QDate.currentDate())
        self._date_edit.setCalendarPopup(True)
        self._date_edit.setDisplayFormat("dd/MM/yyyy")
        self._date_edit.setAlignment(QtCore.Qt.AlignCenter)
        self._date_edit.setMinimumHeight(34)
        layout.addWidget(self._date_edit, alignment=QtCore.Qt.AlignCenter)

        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch()
        btn_continue = QtWidgets.QPushButton("Continuar")
        btn_continue.setMinimumWidth(120)
        btn_continue.setStyleSheet("text-align:center;")
        btn_continue.clicked.connect(self.accept)
        buttons.addWidget(btn_continue)
        buttons.addStretch()
        layout.addLayout(buttons)

    def selected_date(self) -> str | None:
        if self.exec() != QtWidgets.QDialog.Accepted:
            return None
        return self._date_edit.date().toString("dd/MM/yyyy")


class CaixaScopeDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent: QtWidgets.QWidget,
        *,
        company_label: str,
    ) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle(f"Caixa {company_label}")
        self.setModal(True)
        self.resize(560, 220)
        self._choice: str | None = None

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(18, 18, 18, 18)
        layout.setSpacing(12)

        label = QtWidgets.QLabel("O Fechamento de caixa foi concluído")
        label.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)

        info = QtWidgets.QLabel("Qual relatório deve ser gerado?")
        info.setWordWrap(True)
        info.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(info)

        buttons_row = QtWidgets.QHBoxLayout()
        buttons_row.setSpacing(12)
        buttons_row.addStretch()

        btn_daily = QtWidgets.QPushButton("Diário")
        btn_morning = QtWidgets.QPushButton("Manhã")
        btn_afternoon = QtWidgets.QPushButton("Tarde")
        btn_cancel = QtWidgets.QPushButton("Cancelar")
        for btn in (btn_daily, btn_morning, btn_afternoon, btn_cancel):
            btn.setMinimumHeight(36)
            btn.setMinimumWidth(104)
            btn.setStyleSheet("text-align:center;")
            buttons_row.addWidget(btn)

        buttons_row.addStretch()
        layout.addLayout(buttons_row)

        btn_daily.clicked.connect(lambda: self._set_choice("daily"))
        btn_morning.clicked.connect(lambda: self._set_choice("morning"))
        btn_afternoon.clicked.connect(lambda: self._set_choice("afternoon"))
        btn_cancel.clicked.connect(self.reject)

    def _set_choice(self, value: str) -> None:
        self._choice = value
        self.accept()

    def choice(self) -> str | None:
        if self.exec() == QtWidgets.QDialog.Accepted:
            return self._choice
        return None


class CaixaSettingsDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent: QtWidgets.QWidget,
        *,
        eh_special_enabled: bool,
        mva_special_enabled: bool,
    ) -> None:
        super().__init__(parent)
        self.setFont(_popup_font(self))
        self.setWindowTitle("Configurações de Caixa")
        self.setModal(True)
        self.resize(560, 300)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(22, 20, 22, 20)
        layout.setSpacing(14)

        title = QtWidgets.QLabel("Tratamento diferenciado de relatórios")
        title.setObjectName("dialogTitleLabel")
        title.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(title)

        info = QtWidgets.QLabel(
            "Use quando o caixa foi aberto em um dia e fechado no dia seguinte. "
            "O app filtra a data alvo e não soma caixas de dias diferentes."
        )
        info.setWordWrap(True)
        info.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(info)

        options_frame = QtWidgets.QFrame()
        options_frame.setObjectName("contentSubCard")
        options_layout = QtWidgets.QVBoxLayout(options_frame)
        options_layout.setContentsMargins(16, 14, 16, 14)
        options_layout.setSpacing(12)

        self.chk_eh_special = QtWidgets.QCheckBox("Horizonte: caixa fechado no dia seguinte")
        self.chk_mva_special = QtWidgets.QCheckBox("MVA: caixa fechado no dia seguinte")
        self.chk_eh_special.setChecked(eh_special_enabled)
        self.chk_mva_special.setChecked(mva_special_enabled)

        for checkbox in (self.chk_eh_special, self.chk_mva_special):
            checkbox.setCursor(QtGui.QCursor(QtCore.Qt.PointingHandCursor))
            checkbox.setStyleSheet("QCheckBox{text-align:center;}")
            row = QtWidgets.QHBoxLayout()
            row.addStretch(1)
            row.addWidget(checkbox, 0, QtCore.Qt.AlignCenter)
            row.addStretch(1)
            options_layout.addLayout(row)

        layout.addWidget(options_frame)

        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch(1)
        btn_save = QtWidgets.QPushButton("Salvar")
        btn_cancel = QtWidgets.QPushButton("Cancelar")
        for button in (btn_save, btn_cancel):
            button.setMinimumHeight(36)
            button.setMinimumWidth(120)
            button.setStyleSheet("text-align:center;")
            buttons.addWidget(button)
        buttons.addStretch(1)
        layout.addLayout(buttons)

        btn_save.clicked.connect(self.accept)
        btn_cancel.clicked.connect(self.reject)

    def values(self) -> tuple[bool, bool] | None:
        if self.exec() != QtWidgets.QDialog.Accepted:
            return None
        return self.chk_eh_special.isChecked(), self.chk_mva_special.isChecked()


class CaixaReportDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent: QtWidgets.QWidget,
        relatorio_caixa: dict,
        fechamento: dict | None = None,
        relatorio_pix: dict | None = None,
    ) -> None:
        super().__init__(parent)
        self._relatorio_caixa = relatorio_caixa
        self._fechamento = fechamento
        self._relatorio_pix = relatorio_pix
        self._payment_tab_widgets: dict[str, QtWidgets.QWidget] = {}
        self._payment_reports: dict[str, dict] = {}
        self._lazy_static_tabs: dict[QtWidgets.QWidget, tuple[str, object]] = {}
        self._static_tab_count = 1 + int(fechamento is not None)
        self._tabs: QtWidgets.QTabWidget | None = None
        if relatorio_pix:
            payment_key = str(relatorio_pix.get("categoria") or "pagamentos_digitais_nfce").strip() or "pagamentos_digitais_nfce"
            self._payment_reports[payment_key] = relatorio_pix
        if fechamento:
            for key, report in (fechamento.get("relatorios_pagamento") or {}).items():
                if report:
                    self._payment_reports[str(key)] = report
        caixa_title = "Relatório de Caixa"
        if fechamento:
            caixa_title = self._build_caixa_dialog_title(fechamento)
        self.setWindowTitle(caixa_title)
        self.resize(1040, 760)

        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(18, 18, 18, 18)
        layout.setSpacing(14)

        layout.addWidget(self._build_dialog_header(caixa_title, relatorio_caixa, fechamento))

        tabs = QtWidgets.QTabWidget()
        self._tabs = tabs
        tabs.setTabsClosable(True)
        tabs.tabCloseRequested.connect(self._handle_tab_close_requested)
        tabs.currentChanged.connect(self._ensure_lazy_static_tab)
        self._add_lazy_static_tab(self._build_davs_tab_title(relatorio_caixa), lambda: self._build_davs_tab(relatorio_caixa))
        if fechamento:
            self._add_lazy_static_tab("Fechamento Caixa", lambda: self._build_fechamento_tab(fechamento))
        self._hide_static_tab_close_buttons()
        layout.addWidget(tabs, 1)
        self._ensure_lazy_static_tab(0)

        btn_close = QtWidgets.QPushButton("Fechar")
        btn_close.setObjectName("secondaryActionButton")
        btn_close.clicked.connect(self.accept)
        layout.addWidget(btn_close, alignment=QtCore.Qt.AlignHCenter)

    def _apply_soft_shadow(
        self,
        widget: QtWidgets.QWidget,
        *,
        blur: float = 26.0,
        offset_y: float = 8.0,
        color: QtGui.QColor | None = None,
    ) -> None:
        _apply_soft_shadow(widget, blur=blur, offset_y=offset_y, color=color)

    def _build_davs_tab_title(self, relatorio: dict) -> str:
        if relatorio.get("caixa_modelo") == "EH":
            return "Pedidos Caixa"
        return "DAVs Importados"

    def _build_fechamento_scope_suffix(self, report: dict | None) -> str:
        escopo_texto = corrigir_texto(str((report or {}).get("escopo_relatorio") or "")).strip().casefold()
        if escopo_texto.startswith("manh") or escopo_texto == "morning":
            return " (M)"
        if escopo_texto.startswith("tard") or escopo_texto == "afternoon":
            return " (T)"
        return ""

    def _build_caixa_dialog_title(self, relatorio: dict) -> str:
        suffix = self._build_fechamento_scope_suffix(relatorio)
        if relatorio.get("caixa_modelo") == "EH":
            return f"Fechamento de Caixa - Eletrônica Horizonte{suffix}"
        return f"Fechamento de Caixa - MVA{suffix}"

    def _build_dialog_header(
        self,
        title_text: str,
        relatorio_caixa: dict,
        fechamento: dict | None,
    ) -> QtWidgets.QFrame:
        frame = QtWidgets.QFrame()
        frame.setObjectName("dialogHeaderCard")
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(18, 16, 18, 16)
        layout.setSpacing(8)

        top_row = QtWidgets.QHBoxLayout()
        top_row.setSpacing(10)
        badge = QtWidgets.QLabel("EH" if relatorio_caixa.get("caixa_modelo") == "EH" else "MVA")
        badge.setObjectName("reportBadge")
        badge.setAlignment(QtCore.Qt.AlignCenter)
        badge.setFixedWidth(52)
        top_row.addWidget(badge, 0, QtCore.Qt.AlignLeft)

        title = QtWidgets.QLabel(corrigir_texto(title_text))
        title.setObjectName("dialogTitleLabel")
        title.setAlignment(QtCore.Qt.AlignCenter)
        top_row.addWidget(title, 1)

        status_text = corrigir_texto(str((fechamento or {}).get("status") or "Preparado"))
        status_chip = QtWidgets.QLabel(status_text)
        status_chip.setAlignment(QtCore.Qt.AlignCenter)
        status_chip.setObjectName("statusChipSuccess" if status_text == "Confere" else "statusChipWarning")
        status_chip.setMinimumWidth(96)
        top_row.addWidget(status_chip, 0, QtCore.Qt.AlignRight)
        layout.addLayout(top_row)

        meta_items = [
            ("Período", self._display_periodo((fechamento or relatorio_caixa).get("periodo"))),
            ("Escopo", corrigir_texto(str((fechamento or {}).get("escopo_relatorio") or "Diário"))),
            ("Pendências", str(int((fechamento or {}).get("alertas_count", 0) or 0))),
        ]
        meta_row = QtWidgets.QHBoxLayout()
        meta_row.setSpacing(10)
        for label_text, value_text in meta_items:
            meta_row.addWidget(self._build_meta_chip(label_text, value_text))
        layout.addLayout(meta_row)
        self._apply_soft_shadow(frame, blur=22.0, offset_y=7.0, color=QtGui.QColor(10, 16, 24, 110))
        return frame

    def _build_meta_chip(self, label_text: str, value_text: str) -> QtWidgets.QFrame:
        frame = QtWidgets.QFrame()
        frame.setObjectName("metaChip")
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(10, 8, 10, 8)
        layout.setSpacing(2)
        label = QtWidgets.QLabel(corrigir_texto(label_text))
        label.setObjectName("metaChipLabel")
        value = QtWidgets.QLabel(corrigir_texto(value_text))
        value.setObjectName("metaChipValue")
        label.setAlignment(QtCore.Qt.AlignCenter)
        value.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        layout.addWidget(value)
        self._apply_soft_shadow(frame, blur=14.0, offset_y=4.0, color=QtGui.QColor(8, 14, 20, 80))
        return frame

    def _add_lazy_static_tab(self, title: str, builder) -> None:
        if self._tabs is None:
            return
        placeholder = QtWidgets.QWidget()
        self._lazy_static_tabs[placeholder] = (title, builder)
        self._tabs.addTab(placeholder, corrigir_texto(title))

    def _ensure_lazy_static_tab(self, index: int) -> None:
        if self._tabs is None or index < 0:
            return
        placeholder = self._tabs.widget(index)
        if placeholder not in self._lazy_static_tabs:
            return
        title, builder = self._lazy_static_tabs.pop(placeholder)
        built_widget = self._wrap_report_tab(builder())
        self._tabs.removeTab(index)
        placeholder.deleteLater()
        self._tabs.insertTab(index, built_widget, corrigir_texto(title))
        self._tabs.setCurrentIndex(index)
        self._hide_static_tab_close_buttons()

    def _wrap_report_tab(self, content: QtWidgets.QWidget) -> QtWidgets.QWidget:
        scroll = QtWidgets.QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QtWidgets.QFrame.NoFrame)
        scroll.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAsNeeded)
        scroll.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarAsNeeded)
        wrapper = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(wrapper)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.addWidget(content)
        layout.addStretch()
        scroll.setWidget(wrapper)
        return scroll


    def _display_periodo(self, periodo: str | None) -> str:
        periodo_texto = str(periodo or "").strip()
        if not periodo_texto:
            return "Não identificado"
        partes = [parte.strip() for parte in periodo_texto.split(" - ", 1)]
        if len(partes) == 2 and partes[0] == partes[1]:
            return partes[0]
        return periodo_texto

    def _bank_row_has_explicit_origin(self, row: tuple[str, ...] | list[str]) -> bool:
        if len(row) < 3:
            return False
        origem = corrigir_texto(str(row[0] or "")).strip().casefold()
        return origem == "pix" or origem.startswith("cart")

    def _wrap_centered(self, widget: QtWidgets.QWidget, max_width: int | None = None) -> QtWidgets.QWidget:
        if max_width is not None:
            widget.setMaximumWidth(max_width)
        widget.setSizePolicy(QtWidgets.QSizePolicy.Maximum, widget.sizePolicy().verticalPolicy())
        container = QtWidgets.QWidget()
        row = QtWidgets.QHBoxLayout(container)
        row.setContentsMargins(0, 0, 0, 0)
        row.setSpacing(0)
        row.addStretch()
        row.addWidget(widget)
        row.addStretch()
        return container

    def _ordered_payment_reports(self) -> list[tuple[str, dict]]:
        ordem = {
            "pix_caixa": 0,
            "pix_fechamento": 1,
            "pagamentos_digitais_nfce": 1,
            "dinheiro": 2,
            "alertas_eh": 3,
            "cartao_credito": 5,
            "cartao_debito": 6,
            "cartao_credito_caixa": 7,
            "cartao_debito_caixa": 8,
            "nf_pedidos_eh": 9,
        }
        return sorted(
            [
                (key, report)
                for key, report in self._payment_reports.items()
                if not (report or {}).get("hidden_in_menu")
            ],
            key=lambda item: (
                ordem.get(item[0], 99),
                str((item[1] or {}).get("tab_title") or item[0]).casefold(),
            ),
        )

    def _hide_static_tab_close_buttons(self) -> None:
        if self._tabs is None:
            return
        tab_bar = self._tabs.tabBar()
        static_count = int(self._static_tab_count)
        for index in range(min(static_count, self._tabs.count())):
            tab_bar.setTabButton(index, QtWidgets.QTabBar.LeftSide, None)
            tab_bar.setTabButton(index, QtWidgets.QTabBar.RightSide, None)

    def _build_davs_summary_items(self, relatorio: dict):
        if relatorio.get("caixa_modelo") == "MVA":
            return (
                ("Período", self._display_periodo(relatorio.get("periodo"))),
                ("Pedidos totais", str(relatorio.get("pedidos_total", 0))),
                ("Finalizados", str(relatorio.get("pedidos_caixa", 0))),
                ("Editando", str(relatorio.get("pedidos_editando", 0))),
                ("Outros status", str(relatorio.get("pedidos_outros_status", 0))),
                ("Pedidos excluídos", str(relatorio.get("pedidos_excluidos", 0))),
                ("Total do documento", f"R$ {format_number_br(relatorio.get('total_documento', 0.0))}"),
                ("Total excluído", f"R$ {format_number_br(relatorio.get('total_excluido', 0.0))}"),
                ("Total Caixa", f"R$ {format_number_br(relatorio.get('total_caixa', 0.0))}"),
            )

        return (
            ("Período", self._display_periodo(relatorio.get("periodo"))),
            ("Pedidos totais", str(relatorio.get("pedidos_total", 0))),
            ("Pedidos Caixa", str(relatorio.get("pedidos_caixa", 0))),
            ("Fora do balcão", str(relatorio.get("pedidos_excluidos_cliente", 0))),
            ("NF-e excluídas", str(relatorio.get("pedidos_excluidos_documento", 0))),
            ("Cupons cancelados", str(relatorio.get("pedidos_excluidos_cancelados", 0))),
            ("Pedidos excluídos", str(relatorio.get("pedidos_excluidos", 0))),
            ("Total do documento", f"R$ {format_number_br(relatorio.get('total_documento', 0.0))}"),
            ("Total excluído", f"R$ {format_number_br(relatorio.get('total_excluido', 0.0))}"),
            ("Total Caixa", f"R$ {format_number_br(relatorio.get('total_caixa', 0.0))}"),
        )

    def _build_davs_table_headers(self, relatorio: dict) -> tuple[str, ...]:
        if relatorio.get("caixa_modelo") == "MVA":
            return ("Pedido", "Descrição", "Status", "Valor")
        return ("Pedido", "Cliente", "Documento", "Valor")

    def _build_davs_table_widths(self, relatorio: dict) -> list[int]:
        if relatorio.get("caixa_modelo") == "MVA":
            return [100, 250, 110, 120]
        return [90, 280, 190, 120]

    def _build_davs_section_title(self, relatorio: dict) -> str:
        if relatorio.get("caixa_modelo") == "MVA":
            return "Pedidos não finalizados"
        return "Pedidos excluídos do cálculo"

    def _build_davs_empty_message(self, relatorio: dict) -> str:
        if relatorio.get("caixa_modelo") == "MVA":
            return "Nenhum pedido não finalizado encontrado."
        return "Nenhum pedido excluído encontrado."

    def _build_fechamento_subtitle(self, fechamento: dict) -> str:
        return ""

    def _build_fechamento_summary_items(self, fechamento: dict):
        return (
            ("Período", self._display_periodo(fechamento.get("periodo"))),
            (
                fechamento.get("total_resumo_titulo", "Total Resumo NFC-e"),
                f"R$ {format_number_br(fechamento.get('total_resumo_nfce', 0.0))}",
            ),
            ("Valor das faltantes", f"R$ {format_number_br(fechamento.get('valor_faltantes', 0.0))}"),
            ("Status", fechamento.get("status", "-")),
        )

    def _build_fechamento_section_title(self, fechamento: dict) -> str:
        return fechamento.get("secao_titulo", "NFC-e faltantes")

    def _build_fechamento_empty_message(self, fechamento: dict) -> str:
        return fechamento.get("empty_message", "Nenhuma NFC-e faltante encontrada.")

    def _get_fechamento_bank_report(self, fechamento: dict) -> dict | None:
        relatorios_pagamento = fechamento.get("relatorios_pagamento") or {}
        report = relatorios_pagamento.get("alertas_eh")
        if report:
            return report
        return self._payment_reports.get("alertas_eh")

    def _enrich_eh_bank_report(self, fechamento: dict, relatorio_pagamento: dict) -> dict:
        report = corrigir_estrutura_texto(dict(relatorio_pagamento or {}))
        periodo = fechamento.get("periodo") or report.get("periodo")
        valor_total_vendas = round(float(report.get("valor_total_vendas", fechamento.get("total_caixa", 0.0)) or 0.0), 2)
        valor_pendente = round(float(report.get("valor_pendente", fechamento.get("valor_faltantes", 0.0)) or 0.0), 2)
        status = str(fechamento.get("status") or report.get("status") or "-")
        report["periodo"] = periodo
        report["valor_total_vendas"] = valor_total_vendas
        report["valor_pendente"] = valor_pendente
        report["status"] = status
        report["caixa_modelo"] = fechamento.get("caixa_modelo") or report.get("caixa_modelo") or "EH"
        report["escopo_relatorio"] = (
            fechamento.get("escopo_relatorio")
            or report.get("escopo_relatorio")
            or ""
        )
        report["escopo_horario_aplicado"] = list(
            fechamento.get("escopo_horario_aplicado")
            or report.get("escopo_horario_aplicado")
            or []
        )
        report["texto_informativo"] = ""
        hidden_pending_count = int(report.get("hidden_pending_count", 0) or 0)
        pendencias_count = sum(
            len(report.get(key) or [])
            for key in (
                "pix_fechamento_rows",
                "cartao_fechamento_rows",
                "pix_maquina_rows",
                "cartao_maquina_rows",
            )
        )
        pendencias_count += hidden_pending_count
        report["pendencias_count"] = pendencias_count
        report["summary_items"] = (
            ("Período", self._display_periodo(periodo)),
            ("Pendências", str(int(report.get("pendencias_count", 0) or 0))),
            ("Total Pendências", f"R$ {format_number_br(valor_pendente)}"),
        )
        return report

    def _build_eh_bank_sections(
        self,
        relatorio_pagamento: dict,
    ) -> list[tuple[str, tuple[str, ...], list[tuple[str, ...]], list[int], str]]:
        relatorio_pagamento = corrigir_estrutura_texto(relatorio_pagamento or {})
        correlation_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("correlacao_rows") or [])
            if row
        ]
        pix_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("pix_fechamento_rows") or [])
            if row
        ]
        cartao_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("cartao_fechamento_rows") or [])
            if row
        ]
        cancelados_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("cancelados_rows") or [])
            if row
        ]

        bank_rows: list[tuple[str, str, str]] = []
        for row in (relatorio_pagamento.get("pix_maquina_rows") or []):
            if not row:
                continue
            origem = corrigir_texto(str(row[0] or "")).strip() if len(row) >= 1 else ""
            if self._bank_row_has_explicit_origin(row):
                bank_rows.append(tuple(corrigir_texto(str(value)) for value in row[:3]))
            elif len(row) >= 2:
                bank_rows.append(("PIX", corrigir_texto(str(row[0])), corrigir_texto(str(row[1]))))
        for row in (relatorio_pagamento.get("cartao_maquina_rows") or []):
            if not row:
                continue
            origem = corrigir_texto(str(row[0] or "")).strip() if len(row) >= 1 else ""
            if self._bank_row_has_explicit_origin(row):
                bank_rows.append(tuple(corrigir_texto(str(value)) for value in row[:3]))
            elif len(row) >= 2:
                bank_rows.append(("Cartão", corrigir_texto(str(row[0])), corrigir_texto(str(row[1]))))

        sections = [
            (
                "Correlação de Valores",
                ("Pagamento", "Caixa", "Pagamentos", "Status"),
                correlation_rows,
                [150, 92, 96, 92],
                "Nenhuma correlação de valores disponível.",
            ),
            (
                "CF sem Transação Bancária - PIX",
                ("CF", "Valor"),
                pix_rows,
                [180, 120],
                "Nenhum CF PIX sem transação bancária encontrado.",
            ),
            (
                "CF sem Transação Bancária - Cartão",
                ("CF", "Valor"),
                cartao_rows,
                [180, 120],
                "Nenhum CF de cartão sem transação bancária encontrado.",
            ),
            (
                "Transações Bancárias sem CF/NF",
                ("Origem", "Detalhe", "Valor"),
                bank_rows,
                [76, 220, 105],
                "Nenhuma transação bancária sem CF/NF encontrada.",
            ),
        ]
        sections.insert(
            3,
            (
                "Cupons Cancelados",
                ("CF", "Valor"),
                cancelados_rows,
                [180, 100],
                "Nenhum cupom cancelado pendente encontrado.",
            ),
        )
        return sections

    def _build_bank_sections(
        self,
        relatorio_pagamento: dict,
    ) -> list[tuple[str, tuple[str, ...], list[tuple[str, ...]], list[int], str]]:
        relatorio_pagamento = corrigir_estrutura_texto(relatorio_pagamento or {})
        caixa_modelo = str(relatorio_pagamento.get("caixa_modelo") or "EH").upper()
        fechamento_label = "Fechamento EH" if caixa_modelo == "EH" else "Fechamento MVA"

        correlation_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("correlacao_rows") or [])
            if row
        ]
        pix_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("pix_fechamento_rows") or [])
            if row
        ]
        cartao_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("cartao_fechamento_rows") or [])
            if row
        ]
        cancelados_rows = [
            tuple(corrigir_texto(str(value)) for value in row)
            for row in (relatorio_pagamento.get("cancelados_rows") or [])
            if row
        ]

        bank_rows: list[tuple[str, str, str]] = []
        for row in (relatorio_pagamento.get("pix_maquina_rows") or []):
            if not row:
                continue
            origem = corrigir_texto(str(row[0] or "")).strip() if len(row) >= 1 else ""
            if self._bank_row_has_explicit_origin(row):
                bank_rows.append(tuple(corrigir_texto(str(value)) for value in row[:3]))
            elif len(row) >= 2:
                bank_rows.append(("PIX", corrigir_texto(str(row[0])), corrigir_texto(str(row[1]))))
        for row in (relatorio_pagamento.get("cartao_maquina_rows") or []):
            if not row:
                continue
            origem = corrigir_texto(str(row[0] or "")).strip() if len(row) >= 1 else ""
            if self._bank_row_has_explicit_origin(row):
                bank_rows.append(tuple(corrigir_texto(str(value)) for value in row[:3]))
            elif len(row) >= 2:
                bank_rows.append(("Cartão", corrigir_texto(str(row[0])), corrigir_texto(str(row[1]))))

        sections = [
            (
                "Correlação de Valores",
                ("Pagamento", "Caixa", "Pagamentos", "Status"),
                correlation_rows,
                [180, 92, 76, 92],
                "Nenhuma correlação de valores disponível.",
            ),
            (
                "CF sem Transação Bancária - PIX",
                (fechamento_label, "Valor"),
                pix_rows,
                [170, 100],
                "Nenhum CF PIX sem transação bancária encontrado.",
            ),
            (
                "CF sem Transação Bancária - Cartão",
                (fechamento_label, "Valor"),
                cartao_rows,
                [170, 100],
                "Nenhum CF de cartão sem transação bancária encontrado.",
            ),
            (
                "Transações Bancárias sem CF/NF",
                ("Origem", "Detalhe", "Valor"),
                bank_rows,
                [76, 220, 100],
                "Nenhuma transação bancária sem CF/NF encontrada.",
            ),
        ]
        sections.insert(
            3,
            (
                "Cupons Cancelados",
                (fechamento_label, "Valor"),
                cancelados_rows,
                [170, 100],
                "Nenhum cupom cancelado pendente encontrado.",
            ),
        )
        return sections

    def _build_pix_summary_items(self, relatorio_pix: dict):
        summary_label = relatorio_pix.get("summary_label") or "Pagamentos digitais"
        total_label = relatorio_pix.get("total_label") or f"Total {str(summary_label).casefold()}"
        return (
            ("Período", self._display_periodo(relatorio_pix.get("periodo"))),
            (summary_label, str(relatorio_pix.get("quantidade_autorizados", 0))),
            (
                total_label,
                f"R$ {format_number_br(relatorio_pix.get('total_autorizado', 0.0))}",
            ),
        )

    def _build_pix_empty_message(self, relatorio_pix: dict) -> str:
        return relatorio_pix.get(
            "mensagem",
            relatorio_pix.get("empty_message") or "Nenhum pagamento encontrado para este dia.",
        )

    def _build_davs_tab(self, relatorio: dict) -> QtWidgets.QWidget:
        widget = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(widget)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(14)

        summary_items = self._build_davs_summary_items(relatorio)
        dav_actions: dict[str, QtWidgets.QWidget] | None = None
        if (
            relatorio.get("caixa_modelo") == "EH"
            and "nf_pedidos_eh" in self._payment_reports
        ):
            dav_actions = {
                "NF-e excluídas": self._create_filtered_payment_toggle_button({"nf_pedidos_eh"}),
            }
        layout.addWidget(
            self._wrap_centered(
                self._build_summary_frame(summary_items, {"Total Caixa"}, action_widgets=dav_actions),
                760,
            )
        )

        actions = QtWidgets.QHBoxLayout()
        actions.addStretch()
        actions.addWidget(
            self._create_export_button(
                "Imprimir",
                lambda: self._export_davs_pdf(relatorio),
            )
        )
        actions.addStretch()
        layout.addLayout(actions)

        itens_excluidos = relatorio.get("itens_excluidos", [])
        rows = [
            (
                self._display_numero(item.get("pedido", "")),
                str(item.get("cliente", "")),
                str(item.get("documento", "")),
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in itens_excluidos
        ]
        layout.addWidget(
            self._build_section_card(
                self._build_davs_section_title(relatorio),
                self._build_simple_centered_table(
                    self._build_davs_table_headers(relatorio),
                    rows,
                    self._build_davs_table_widths(relatorio),
                    self._build_davs_empty_message(relatorio),
                    selection_mode=QtWidgets.QAbstractItemView.SingleSelection,
                ),
            ),
            1,
        )

        return widget

    def _build_fechamento_tab(self, fechamento: dict) -> QtWidgets.QWidget:
        bank_report = self._get_fechamento_bank_report(fechamento)
        if bank_report:
            return self._build_bank_reconciliation_tab(self._enrich_eh_bank_report(fechamento, bank_report))

        widget = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(widget)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(14)

        subtitle_text = self._build_fechamento_subtitle(fechamento)
        if subtitle_text:
            subtitle = QtWidgets.QLabel(subtitle_text)
            subtitle.setWordWrap(True)
            subtitle.setAlignment(QtCore.Qt.AlignCenter)
            layout.addWidget(self._wrap_centered(subtitle, 760))

        summary_items = self._build_fechamento_summary_items(fechamento)
        action_widgets: dict[str, QtWidgets.QWidget] | None = None
        if self._payment_reports:
            action_widgets = {
                fechamento.get("total_resumo_titulo", "Total Resumo NFC-e"): self._create_payment_toggle_button(),
            }
        layout.addWidget(
            self._wrap_centered(
                self._build_summary_frame(
                    summary_items,
                    {"Total Pendências"},
                    fechamento=fechamento,
                    action_widgets=action_widgets,
                ),
                760,
            )
        )

        actions = QtWidgets.QHBoxLayout()
        actions.addStretch()
        actions.addWidget(
            self._create_export_button(
                "Imprimir",
                lambda: self._export_fechamento_pdf(fechamento),
            )
        )
        actions.addStretch()
        layout.addLayout(actions)

        registros = fechamento.get("registros_conferencia", [])
        rows = []
        for item in registros:
            valor = item.get("valor")
            valor_texto = "-" if valor in (None, "") else f"R$ {format_number_br(valor)}"
            rows.append((item.get("numero_exibicao", ""), valor_texto))

        total_frame = QtWidgets.QFrame()
        total_frame.setObjectName("inlineTotalCard")
        total_frame.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Fixed)
        total_layout = QtWidgets.QHBoxLayout(total_frame)
        total_layout.setContentsMargins(12, 8, 12, 8)
        total_layout.setSpacing(0)
        total_label = QtWidgets.QLabel(
            f"Total faltante: R$ {format_number_br(fechamento.get('valor_faltantes', 0.0))}"
        )
        total_font = total_label.font()
        total_font.setBold(False)
        total_label.setFont(total_font)
        total_label.setAlignment(QtCore.Qt.AlignCenter)
        total_color = "#59C734" if fechamento.get("status") == "Confere" else "#FF4D4F"
        total_label.setStyleSheet(f"color:{total_color};")
        total_layout.addStretch()
        total_layout.addWidget(total_label)
        total_layout.addStretch()

        section_body = QtWidgets.QWidget()
        section_layout = QtWidgets.QVBoxLayout(section_body)
        section_layout.setContentsMargins(0, 0, 0, 0)
        section_layout.setSpacing(10)
        section_layout.addWidget(
            self._build_simple_centered_table(
                ("Número", "Valor"),
                rows,
                [185, 145],
                self._build_fechamento_empty_message(fechamento),
            )
        )
        section_layout.addWidget(total_frame)
        layout.addWidget(
            self._build_section_card(
                self._build_fechamento_section_title(fechamento),
                section_body,
                tone="warning" if rows else "default",
            ),
            1,
        )
        return widget

    def _create_payment_toggle_button(self) -> QtWidgets.QWidget:
        return self._create_filtered_payment_toggle_button(None)

    def _create_filtered_payment_toggle_button(self, allowed_keys: set[str] | None) -> QtWidgets.QWidget:
        button = QtWidgets.QToolButton()
        button.setArrowType(QtCore.Qt.DownArrow)
        button.setPopupMode(QtWidgets.QToolButton.InstantPopup)
        button.setToolButtonStyle(QtCore.Qt.ToolButtonIconOnly)
        button.setAutoRaise(True)
        button.setFixedSize(16, 16)
        button.setIconSize(QtCore.QSize(8, 8))
        button.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Fixed)
        button.setStyleSheet(
            "QToolButton{padding:0px;margin:0px;border:none;}"
            "QToolButton::menu-indicator{image:none;width:0px;}"
        )
        button.setCursor(QtGui.QCursor(QtCore.Qt.PointingHandCursor))
        button.setToolTip("Abrir detalhes de pagamentos")

        menu = QtWidgets.QMenu(button)
        for report_key, report in self._ordered_payment_reports():
            if allowed_keys is not None and report_key not in allowed_keys:
                continue
            action = menu.addAction(
                report.get("menu_text") or f"Abrir {str(report.get('tab_title') or report_key).casefold()}"
            )
            action.triggered.connect(
                lambda _checked=False, key=report_key: self._open_payment_tab(key)
            )
        button.setMenu(menu)
        return button

    def _open_payment_tab(self, report_key: str) -> None:
        if self._tabs is None:
            return
        report = self._payment_reports.get(report_key)
        if report is None:
            return
        if report_key not in self._payment_tab_widgets:
            widget = self._wrap_report_tab(self._build_pix_tab(report))
            self._payment_tab_widgets[report_key] = widget
            self._tabs.addTab(widget, report.get("tab_title") or "Pagamentos")
        self._tabs.setCurrentWidget(self._payment_tab_widgets[report_key])

    def _close_payment_tab(self, report_key: str) -> None:
        if self._tabs is None:
            return
        widget = self._payment_tab_widgets.pop(report_key, None)
        if widget is None:
            return
        index = self._tabs.indexOf(widget)
        if index >= 0:
            self._tabs.removeTab(index)
        widget.deleteLater()

    def _handle_tab_close_requested(self, index: int) -> None:
        if self._tabs is None:
            return
        widget = self._tabs.widget(index)
        for report_key, report_widget in list(self._payment_tab_widgets.items()):
            if report_widget is widget:
                self._close_payment_tab(report_key)
                return

    def _build_payment_table_rows(self, relatorio_pagamento: dict) -> list[tuple[str, ...]]:
        if relatorio_pagamento.get("table_rows"):
            return [tuple(str(value) for value in row) for row in relatorio_pagamento.get("table_rows", [])]
        headers = tuple(relatorio_pagamento.get("table_headers") or ())
        mode = relatorio_pagamento.get("table_mode") or ("numero_data_valor" if len(headers) == 3 else "data_valor")
        rows: list[tuple[str, ...]] = []
        for item in relatorio_pagamento.get("itens_autorizados", []):
            valor_texto = f"R$ {format_number_br(item.get('valor_bruto', 0.0))}"
            if mode == "numero_data_valor":
                rows.append(
                    (
                        item.get("numero_exibicao", ""),
                        item.get("data_venda", ""),
                        valor_texto,
                    )
                )
            else:
                rows.append(
                    (
                        item.get("data_venda", ""),
                        valor_texto,
                    )
                )
        return rows

    def _build_payment_table_widths(self, relatorio_pagamento: dict) -> list[int]:
        if relatorio_pagamento.get("table_widths"):
            return list(relatorio_pagamento.get("table_widths") or [])
        headers = tuple(relatorio_pagamento.get("table_headers") or ())
        mode = relatorio_pagamento.get("table_mode") or ("numero_data_valor" if len(headers) == 3 else "data_valor")
        if mode == "numero_data_valor":
            return [110, 120, 130]
        return [230, 140]

    def _build_simple_centered_table(
        self,
        headers: tuple[str, ...],
        rows: list[tuple[str, ...]],
        widths: list[int],
        empty_message: str,
        *,
        highlight_status: bool = False,
        selection_mode: QtWidgets.QAbstractItemView.SelectionMode = QtWidgets.QAbstractItemView.NoSelection,
    ) -> QtWidgets.QWidget:
        headers = tuple(corrigir_texto(str(value)) for value in headers)
        rows = [tuple(corrigir_texto(str(value)) for value in row) for row in rows]
        empty_message = corrigir_texto(empty_message)
        table_rows = rows or [tuple([empty_message] + [""] * max(0, len(headers) - 1))]
        model = ReadOnlyTableModel(
            headers,
            table_rows,
            highlight_status_column=highlight_status,
            parent=self,
        )
        table = ScrollLockTableView()
        table.setModel(model)
        table.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
        table.setSelectionMode(selection_mode)
        table.setAlternatingRowColors(True)
        table.verticalHeader().setVisible(False)
        table.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Preferred)
        table.setMinimumSize(0, 0)
        table.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)
        table.setWordWrap(True)
        table.setSortingEnabled(False)
        self._configure_resizable_table(table, widths)
        self._set_report_table_height(table, len(table_rows))

        if not rows:
            table.setSpan(0, 0, 1, len(headers))

        wrap = QtWidgets.QWidget()
        wrap_layout = QtWidgets.QHBoxLayout(wrap)
        wrap_layout.setContentsMargins(0, 0, 0, 0)
        wrap_layout.addStretch()
        wrap_layout.addWidget(table)
        wrap_layout.addStretch()
        return wrap

    def _build_section_card(
        self,
        title: str,
        content: QtWidgets.QWidget,
        *,
        tone: str = "default",
    ) -> QtWidgets.QFrame:
        frame = QtWidgets.QFrame()
        frame.setObjectName("reportSectionCard")
        frame.setProperty("tone", tone)
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(14, 14, 14, 14)
        layout.setSpacing(10)
        label = QtWidgets.QLabel(corrigir_texto(title))
        label.setObjectName("sectionTitleLabel")
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        layout.addWidget(content)
        shadow_color = QtGui.QColor(12, 18, 28, 92)
        if tone == "warning":
            shadow_color = QtGui.QColor(44, 26, 16, 96)
        self._apply_soft_shadow(frame, blur=18.0, offset_y=5.0, color=shadow_color)
        return frame

    def _build_bank_reconciliation_tab(self, relatorio_pagamento: dict) -> QtWidgets.QWidget:
        relatorio_pagamento = corrigir_estrutura_texto(relatorio_pagamento or {})
        widget = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(widget)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(14)

        if relatorio_pagamento.get("categoria") == "alertas_eh":
            summary_items = relatorio_pagamento.get("summary_items") or ()
            layout.addWidget(
                self._wrap_centered(
                    self._build_summary_frame(summary_items, {"Total Pendências"}),
                    760,
                )
            )
            sections = self._build_bank_sections(relatorio_pagamento)
            keep_empty_sections = True

        else:
            summary_items = self._build_pix_summary_items(relatorio_pagamento)
            layout.addWidget(
                self._wrap_centered(
                    self._build_summary_frame(
                        summary_items,
                        {corrigir_texto(relatorio_pagamento.get("total_label") or "Total pendências")},
                    ),
                    760,
                )
            )
            sections = [
                (
                    "PIX - CF sem Transação Bancária",
                    ("Fechamento EH", "Valor EH"),
                    list(relatorio_pagamento.get("pix_fechamento_rows") or []),
                    [160, 92],
                    "Nenhum CF PIX sem transação bancária encontrado.",
                ),
                (
                    "PIX - Transação Bancária sem CF/NF",
                    ("Máquina", "Valor Banco"),
                    list(relatorio_pagamento.get("pix_maquina_rows") or []),
                    [160, 92],
                    "Nenhuma transação PIX sem CF/NF encontrada.",
                ),
                (
                    "Cartões - CF sem Transação Bancária",
                    ("Fechamento EH", "Valor EH"),
                    list(relatorio_pagamento.get("cartao_fechamento_rows") or []),
                    [160, 92],
                    "Nenhum CF de cartão sem transação bancária encontrado.",
                ),
                (
                    "Cartões - Transação Bancária sem CF/NF",
                    ("Máquina", "Valor Banco"),
                    list(relatorio_pagamento.get("cartao_maquina_rows") or []),
                    [160, 92],
                    "Nenhuma transação de cartão sem CF/NF encontrada.",
                ),
                (
                    "Observações",
                    ("Tipo", "Detalhe", "Valor"),
                    list(relatorio_pagamento.get("observacao_rows") or []),
                    [120, 210, 92],
                    "Nenhuma observação adicional encontrada.",
                ),
            ]
            keep_empty_sections = False

        actions = QtWidgets.QHBoxLayout()
        actions.addStretch()
        actions.addWidget(
            self._create_export_button(
                "Imprimir",
                lambda: self._export_pix_pdf(relatorio_pagamento),
            )
        )
        actions.addStretch()
        layout.addLayout(actions)

        for title, headers, rows, widths, empty_message in sections:
            if not rows and not keep_empty_sections and title != "Observações":
                continue
            layout.addWidget(
                self._build_section_card(
                    title,
                    self._build_simple_centered_table(
                        headers,
                        rows,
                        widths,
                        empty_message,
                        highlight_status=title == "Correlação de Valores",
                    ),
                    tone="warning" if rows and title != "Correlação de Valores" else "default",
                )
            )

        layout.addStretch()
        return widget

    def _build_pix_tab(self, relatorio_pix: dict) -> QtWidgets.QWidget:
        relatorio_pix = corrigir_estrutura_texto(relatorio_pix or {})
        if relatorio_pix.get("categoria") == "alertas_eh":
            return self._build_bank_reconciliation_tab(relatorio_pix)

        widget = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(widget)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(14)

        summary_items = self._build_pix_summary_items(relatorio_pix)
        layout.addWidget(
            self._wrap_centered(
                self._build_summary_frame(
                    summary_items,
                    {corrigir_texto(relatorio_pix.get("total_label") or "Total pagamentos digitais")},
                ),
                760,
            )
        )

        if relatorio_pix.get("arquivo"):
            actions = QtWidgets.QHBoxLayout()
            actions.addStretch()
            actions.addWidget(
                self._create_export_button(
                    "Imprimir",
                    lambda: self._export_pix_pdf(relatorio_pix),
                )
            )
            actions.addStretch()
            layout.addLayout(actions)

        headers = tuple(corrigir_texto(str(value)) for value in (relatorio_pix.get("table_headers") or ("Data da venda", "Valor bruto")))
        rows = self._build_payment_table_rows(relatorio_pix)
        layout.addWidget(
            self._build_section_card(
                relatorio_pix.get("section_label") or "Transações de pagamento",
                self._build_simple_centered_table(
                    headers,
                    rows,
                    self._build_payment_table_widths(relatorio_pix),
                    self._build_pix_empty_message(relatorio_pix),
                    selection_mode=QtWidgets.QAbstractItemView.SingleSelection,
                ),
            ),
            1,
        )

        return widget

    def _build_summary_frame(
        self,
        items,
        highlighted_labels: set[str] | None = None,
        fechamento: dict | None = None,
        action_widgets: dict[str, QtWidgets.QWidget] | None = None,
    ) -> QtWidgets.QFrame:
        highlighted_labels = {corrigir_texto(str(label)) for label in (highlighted_labels or set())}
        action_widgets = action_widgets or {}
        frame = QtWidgets.QFrame()
        frame.setObjectName("summaryCard")
        frame.setSizePolicy(QtWidgets.QSizePolicy.Maximum, QtWidgets.QSizePolicy.Fixed)
        layout = QtWidgets.QGridLayout(frame)
        layout.setContentsMargins(14, 12, 14, 12)
        layout.setHorizontalSpacing(18)
        layout.setVerticalSpacing(10)
        layout.setAlignment(QtCore.Qt.AlignCenter)

        for row, (label_text, value_text) in enumerate(items):
            label_text = corrigir_texto(str(label_text))
            value_text = corrigir_texto(str(value_text))
            label = QtWidgets.QLabel(f"{label_text}:")
            value = QtWidgets.QLabel(value_text)
            label.setAlignment(QtCore.Qt.AlignCenter)
            value.setAlignment(QtCore.Qt.AlignCenter)
            label_font = label.font()
            label_font.setPointSize(max(10, label_font.pointSize() + 1))
            label.setFont(label_font)
            value_font_base = value.font()
            value_font_base.setPointSize(max(10, value_font_base.pointSize() + 1))
            value.setFont(value_font_base)

            if label_text in highlighted_labels:
                value_font = value.font()
                value_font.setBold(False)
                value_font.setPointSize(value_font.pointSize())
                value.setFont(value_font)

            if label_text in highlighted_labels and label_text not in {"Total Pendências"}:
                value.setStyleSheet("color:#59C734;")
            if label_text in {"Total Pendências"}:
                cor = "#59C734"
                if fechamento and fechamento.get("status") != "Confere":
                    cor = "#FF4D4F"
                value.setStyleSheet(f"color:{cor};")

            value_box = QtWidgets.QWidget()
            value_layout = QtWidgets.QHBoxLayout(value_box)
            value_layout.setContentsMargins(0, 0, 0, 0)
            value_layout.setSpacing(4)
            value_layout.addStretch()
            value_layout.addWidget(value, 0, QtCore.Qt.AlignCenter)
            if label_text in action_widgets:
                value_layout.addWidget(action_widgets[label_text], 0, QtCore.Qt.AlignCenter)
            value_layout.addStretch()

            layout.addWidget(label, row, 0, QtCore.Qt.AlignCenter)
            layout.addWidget(value_box, row, 1, QtCore.Qt.AlignCenter)

        return frame

    def _create_export_button(self, text: str, callback) -> QtWidgets.QPushButton:
        button = QtWidgets.QPushButton(text)
        button.setObjectName("primaryActionButton")
        button.clicked.connect(callback)
        return button

    def _build_empty_table_icon(self, size: int = 90) -> QtGui.QPixmap:
        return _build_empty_table_icon(size)

    def _configure_resizable_table(self, table: QtWidgets.QTableView, widths: list[int]) -> None:
        header = table.horizontalHeader()
        header.setSectionResizeMode(QtWidgets.QHeaderView.Interactive)
        table.setHorizontalScrollMode(QtWidgets.QAbstractItemView.ScrollPerPixel)
        table.setVerticalScrollMode(QtWidgets.QAbstractItemView.ScrollPerPixel)
        table.setMinimumSize(0, 0)
        effective_widths = [max(68, int(width or 0)) for width in list(widths or [])]
        for index, width in enumerate(effective_widths):
            table.setColumnWidth(index, width)
        reserve_width = table.verticalScrollBar().sizeHint().width()
        compact_width = header.length() + reserve_width + table.frameWidth() * 2 + 6
        table.setFixedWidth(max(compact_width, 280))
        header.setMinimumSectionSize(68)
        table.verticalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)

    def _set_report_table_height(self, table: QtWidgets.QTableView, row_count: int) -> None:
        table.resizeRowsToContents()
        header_height = max(28, table.horizontalHeader().height())
        default_row_height = max(30, table.verticalHeader().defaultSectionSize())
        visible_rows = max(3, min(max(row_count, 1), 5))
        body_height = 0
        for index in range(min(row_count, visible_rows)):
            body_height += max(default_row_height, table.rowHeight(index))
        if row_count < visible_rows:
            body_height += default_row_height * (visible_rows - row_count)
        fixed_height = max(156, header_height + body_height + table.frameWidth() * 2 + 8)
        table.setFixedHeight(fixed_height)

    def _fit_table_width(self, table: QtWidgets.QTableView) -> None:
        width = table.horizontalHeader().length() + table.frameWidth() * 2 + 2
        if table.verticalScrollBar().isVisible():
            width += table.verticalScrollBar().sizeHint().width()
        table.setFixedWidth(width)

    def _create_configured_printer(self) -> QtPrintSupport.QPrinter:
        return _create_a4_printer()

    def _get_default_printer(self) -> QtPrintSupport.QPrinter:
        return _resolve_default_printer()

    def _print_section_widths(
        self,
        section_title: object,
        headers: tuple[str, ...],
        widths: object,
    ) -> object:
        normalized_title = corrigir_texto(str(section_title or "")).strip().casefold()
        if normalized_title == "transacoes bancarias sem cf/nf" and len(headers) == 3:
            return [85, 325, 170]
        return widths

    def _column_width_percentages(self, widths: object, column_count: int) -> list[float]:
        values: list[float] = []
        for raw in list(widths or [])[:column_count]:
            try:
                value = float(raw)
            except (TypeError, ValueError):
                value = 0.0
            values.append(max(0.0, value))
        if len(values) < column_count:
            values.extend([0.0] * (column_count - len(values)))
        total = sum(values)
        if total <= 0:
            return []
        return [(value / total) * 100.0 for value in values]

    def _build_print_document_html(
        self,
        title: str,
        summary_items,
        sections,
    ) -> str:
        from html import escape

        def _cell(value: object) -> str:
            return escape(corrigir_texto(str(value or "")))

        font_family = escape(corrigir_texto(self.font().family() or "Lexend"))
        html_parts = [
            "<html><head><meta charset='utf-8'>",
            "<style>",
            f"body{{font-family:'{font_family}',Arial,Helvetica,sans-serif;font-size:7.4pt;color:#000;margin:0;padding:0;}}",
            f".page{{{_print_document_page_style()}}}",
            "h1{font-size:9pt;text-align:center;margin:0 0 4px 0;white-space:nowrap;overflow-wrap:normal;word-break:normal;}",
            "h2{font-size:7pt;text-align:center;margin:3px 0 2px 0;font-weight:400;}",
            "table{width:100%;border-collapse:collapse;table-layout:fixed;margin:0 0 6px 0;}",
            ".section-table th:last-child,.section-table td:last-child{white-space:nowrap;overflow-wrap:normal;word-break:keep-all;}",
            "th{background:#000;color:#fff;font-weight:400;}",
            "th,td{border:1px solid #777;padding:2px 3px;text-align:center;vertical-align:middle;word-wrap:break-word;overflow-wrap:anywhere;font-size:6.6pt;}",
            "td{background:#fff;color:#000;}",
            "</style></head><body><div class='page'>",
            f"<h1>{_cell(title)}</h1>",
            "<table><thead><tr><th>Campo</th><th>Valor</th></tr></thead><tbody>",
        ]

        for label, value in summary_items:
            html_parts.append(f"<tr><td>{_cell(label)}</td><td>{_cell(value)}</td></tr>")
        html_parts.append("</tbody></table>")

        for section_title, headers, rows, widths, empty_message in sections:
            headers = tuple(headers or ())
            rows = list(rows or [])
            if section_title:
                html_parts.append(f"<h2>{_cell(section_title)}</h2>")
            width_percentages = self._column_width_percentages(
                self._print_section_widths(section_title, headers, widths),
                len(headers),
            )
            html_parts.append("<table class='section-table'>")
            if width_percentages:
                html_parts.append("<colgroup>")
                for width_pct in width_percentages:
                    html_parts.append(f"<col style='width:{width_pct:.2f}%'>")
                html_parts.append("</colgroup>")
            html_parts.append("<thead><tr>")
            for header in headers:
                html_parts.append(f"<th>{_cell(header)}</th>")
            html_parts.append("</tr></thead><tbody>")
            if rows:
                for row in rows:
                    normalized_row = list(row[: len(headers)])
                    if len(normalized_row) < len(headers):
                        normalized_row.extend([""] * (len(headers) - len(normalized_row)))
                    html_parts.append("<tr>")
                    for value in normalized_row:
                        html_parts.append(f"<td>{_cell(value)}</td>")
                    html_parts.append("</tr>")
            else:
                col_span = max(1, len(headers))
                html_parts.append(f"<tr><td colspan='{col_span}'>{_cell(empty_message)}</td></tr>")
            html_parts.append("</tbody></table>")

        html_parts.append("</div></body></html>")
        return "".join(html_parts)

    def _print_html_document(self, html: str, printer: QtPrintSupport.QPrinter) -> None:
        _render_html_document_to_printer(html, printer, self.font().family() or "Lexend")

    def _print_simple_report_to_default_printer(
        self,
        title: str,
        summary_items,
        section_title: str,
        headers,
        rows,
        widths,
        empty_message: str,
    ) -> None:
        html = self._build_print_document_html(
            title=title,
            summary_items=summary_items,
            sections=[(section_title, headers, rows, widths, empty_message)],
        )
        self._print_html_document(html, self._get_default_printer())

    def _print_sectioned_report_to_default_printer(
        self,
        title: str,
        summary_items,
        sections,
    ) -> None:
        html = self._build_print_document_html(
            title=title,
            summary_items=summary_items,
            sections=sections,
        )
        self._print_html_document(html, self._get_default_printer())

    def build_automation_bundle_jobs(self) -> list[tuple[str, str]]:
        jobs: list[tuple[str, str]] = []
        if not self._fechamento:
            return jobs

        fechamento = self._fechamento
        fechamento_title = self._build_caixa_dialog_title(fechamento)
        bank_report = self._get_fechamento_bank_report(fechamento)
        if bank_report:
            report = self._enrich_eh_bank_report(fechamento, bank_report)
            html = self._build_print_document_html(
                title=fechamento_title,
                summary_items=report.get("summary_items") or (),
                sections=self._build_bank_sections(report),
            )
            jobs.append((fechamento_title, html))
            return jobs

        fechamento_rows = [
            (
                item.get("numero_exibicao", ""),
                "-" if item.get("valor") in (None, "") else f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in fechamento.get("registros_conferencia", [])
        ]
        if fechamento_rows:
            fechamento_rows.append(
                (
                    "Total faltante",
                    f"R$ {format_number_br(fechamento.get('valor_faltantes', 0.0))}",
                )
            )
        html = self._build_print_document_html(
            title=fechamento_title,
            summary_items=self._build_fechamento_summary_items(fechamento),
            sections=[
                (
                    self._build_fechamento_section_title(fechamento),
                    ("Numero", "Valor"),
                    fechamento_rows,
                    [260, 140],
                    self._build_fechamento_empty_message(fechamento),
                )
            ],
        )
        jobs.append((fechamento_title, html))
        return jobs

    def print_automation_jobs(self, jobs: list[tuple[str, str]]) -> list[str]:
        printed_titles: list[str] = []
        for title, html in jobs:
            self._print_html_document(html, self._get_default_printer())
            printed_titles.append(title)
        return printed_titles

    def print_automation_bundle(self) -> list[str]:
        return self.print_automation_jobs(self.build_automation_bundle_jobs())

    def _export_davs_pdf(self, relatorio: dict) -> None:
        summary_items = self._build_davs_summary_items(relatorio)
        rows = [
            (
                self._display_numero(item.get("pedido", "")),
                item.get("cliente", ""),
                item.get("documento", ""),
                f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in relatorio.get("itens_excluidos", [])
        ]
        title = "Relatório de Caixa - DAVs Importados"
        if relatorio.get("caixa_modelo") == "EH":
            title = "Relatório de Caixa - Pedidos Caixa"
        self._export_report_pdf(
            title=title,
            default_name="relatorio_caixa_davs.pdf",
            summary_items=summary_items,
            headers=self._build_davs_table_headers(relatorio),
            rows=rows,
            empty_message=self._build_davs_empty_message(relatorio),
        )

    def _export_fechamento_pdf(self, fechamento: dict) -> None:
        bank_report = self._get_fechamento_bank_report(fechamento)
        if bank_report:
            report = self._enrich_eh_bank_report(fechamento, bank_report)
            self._export_sectioned_report_pdf(
                title=self._build_caixa_dialog_title(fechamento),
                default_name="relatorio_caixa_fechamento_eh.pdf" if str(fechamento.get("caixa_modelo") or "").upper() == "EH" else "relatorio_caixa_fechamento_mva.pdf",
                summary_items=report.get("summary_items") or (),
                sections=self._build_bank_sections(report),
            )
            return

        summary_items = self._build_fechamento_summary_items(fechamento)
        rows = [
            (
                item.get("numero_exibicao", ""),
                "-" if item.get("valor") in (None, "") else f"R$ {format_number_br(item.get('valor', 0.0))}",
            )
            for item in fechamento.get("registros_conferencia", [])
        ]
        if rows:
            rows.append(
                (
                    "Total faltante",
                    f"R$ {format_number_br(fechamento.get('valor_faltantes', 0.0))}",
                )
            )
        self._export_report_pdf(
            title=self._build_caixa_dialog_title(fechamento),
            default_name="relatorio_caixa_fechamento.pdf",
            summary_items=summary_items,
            headers=("Número", "Valor"),
            rows=rows,
            empty_message=self._build_fechamento_empty_message(fechamento),
        )

    def _export_pix_pdf(self, relatorio_pix: dict) -> None:
        if relatorio_pix.get("categoria") == "alertas_eh":
            self._export_sectioned_report_pdf(
                title=self._build_caixa_dialog_title(relatorio_pix),
                default_name="relatorio_caixa_fechamento_eh.pdf" if str(relatorio_pix.get("caixa_modelo") or "EH").upper() == "EH" else "relatorio_caixa_fechamento_mva.pdf",
                summary_items=relatorio_pix.get("summary_items") or (),
                sections=self._build_bank_sections(relatorio_pix),
            )
            return

        summary_items = self._build_pix_summary_items(relatorio_pix)
        headers = tuple(corrigir_texto(str(value)) for value in (relatorio_pix.get("table_headers") or ("Data da venda", "Valor bruto")))
        rows = self._build_payment_table_rows(relatorio_pix)
        categoria = re.sub(r"[^a-z0-9]+", "_", str(relatorio_pix.get("categoria") or "pagamento").casefold()).strip("_")
        self._export_report_pdf(
            title=relatorio_pix.get("export_title") or f"Fechamento de Caixa - {relatorio_pix.get('tab_title') or 'Pagamentos'}",
            default_name=relatorio_pix.get("export_name") or f"relatorio_caixa_{categoria or 'pagamento'}.pdf",
            summary_items=summary_items,
            headers=headers,
            rows=rows,
            empty_message=self._build_pix_empty_message(relatorio_pix),
        )

    def _export_report_pdf(
        self,
        title: str,
        default_name: str,
        summary_items,
        headers,
        rows,
        empty_message: str,
    ) -> None:
        from reportlab.lib.pagesizes import A4
        from reportlab.pdfgen import canvas

        title = corrigir_texto(title)
        summary_items = [(corrigir_texto(str(label)), corrigir_texto(str(value))) for label, value in summary_items]
        headers = tuple(corrigir_texto(str(header)) for header in headers)
        rows = [tuple(corrigir_texto(str(value)) for value in row) for row in rows]
        empty_message = corrigir_texto(str(empty_message))

        path = filedialog.asksaveasfilename(
            defaultextension=".pdf",
            filetypes=[("PDF", "*.pdf")],
            title=title,
        )
        if not path:
            return
        if os.path.isdir(path):
            path = os.path.join(path, default_name)

        pdf = canvas.Canvas(path, pagesize=A4)
        width, height = A4
        y = height - 40
        title_font_name, body_font_name = _get_reportlab_font_names()

        def new_page():
            nonlocal y
            pdf.showPage()
            y = height - 40
            pdf.setFont(body_font_name, 9)

        pdf.setFont(title_font_name, 12)
        pdf.drawString(40, y, title)
        y -= 24

        pdf.setFont(body_font_name, 9)
        for label, value in summary_items:
            text = f"{label}: {value}"
            for part in self._split_pdf_text(text, 95):
                if y < 45:
                    new_page()
                pdf.drawString(40, y, part)
                y -= 13
        y -= 8

        if y < 60:
            new_page()

        pdf.setFont(title_font_name, 9)
        pdf.drawString(40, y, " | ".join(headers))
        y -= 14
        pdf.setFont(body_font_name, 8.5)

        if not rows:
            pdf.drawString(40, y, empty_message)
        else:
            for row in rows:
                line = " | ".join(str(value) for value in row)
                for part in self._split_pdf_text(line, 120):
                    if y < 45:
                        new_page()
                    pdf.drawString(40, y, part)
                    y -= 11

        pdf.save()
        messagebox.showinfo("Exportado", f"PDF salvo em:\n{path}")

    def _export_sectioned_report_pdf(
        self,
        title: str,
        default_name: str,
        summary_items,
        sections,
    ) -> None:
        from html import escape
        from PySide6 import QtPrintSupport

        def _print_section_widths(
            section_title: object,
            headers: tuple[str, ...],
            widths: object,
        ) -> object:
            normalized_title = corrigir_texto(str(section_title or "")).strip().casefold()
            if normalized_title == "transações bancárias sem cf/nf" and len(headers) == 3:
                return [85, 325, 170]
            return widths

        def _column_width_percentages(widths: object, column_count: int) -> list[float]:
            values: list[float] = []
            for raw in list(widths or [])[:column_count]:
                try:
                    value = float(raw)
                except (TypeError, ValueError):
                    value = 0.0
                values.append(max(0.0, value))
            if len(values) < column_count:
                values.extend([0.0] * (column_count - len(values)))
            total = sum(values)
            if total <= 0:
                return []
            return [(value / total) * 100.0 for value in values]

        printer = QtPrintSupport.QPrinter(QtPrintSupport.QPrinter.HighResolution)
        printer.setPageSize(QtGui.QPageSize(QtGui.QPageSize.A4))
        printer.setPageMargins(QtCore.QMarginsF(6, 6, 6, 6), QtGui.QPageLayout.Millimeter)
        print_dialog = QtPrintSupport.QPrintDialog(printer, self)
        print_dialog.setWindowTitle(corrigir_texto("Selecionar impressora"))
        if print_dialog.exec() != QtWidgets.QDialog.Accepted:
            return

        def _cell(value: object) -> str:
            return escape(corrigir_texto(str(value or "")))

        font_family = escape(corrigir_texto(self.font().family() or "Lexend"))

        html_parts = [
            "<html><head><meta charset='utf-8'>",
            "<style>",
            f"body{{font-family:'{font_family}',Arial,Helvetica,sans-serif;font-size:7.4pt;color:#000;margin:0;padding:0;}}",
            f".page{{{_print_document_page_style()}}}",
            "h1{font-size:9pt;text-align:center;margin:0 0 4px 0;white-space:nowrap;overflow-wrap:normal;word-break:normal;}",
            "h2{font-size:7pt;text-align:center;margin:3px 0 2px 0;font-weight:400;}",
            "table{width:100%;border-collapse:collapse;table-layout:fixed;margin:0 0 6px 0;}",
            ".section-table th:last-child,.section-table td:last-child{white-space:nowrap;overflow-wrap:normal;word-break:keep-all;}",
            "th{background:#000;color:#fff;font-weight:400;}",
            "th,td{border:1px solid #777;padding:2px 3px;text-align:center;vertical-align:middle;word-wrap:break-word;overflow-wrap:anywhere;font-size:6.6pt;}",
            "td{background:#fff;color:#000;}",
            "</style></head><body><div class='page'>",
            f"<h1>{_cell(title)}</h1>",
            "<table><thead><tr><th>Campo</th><th>Valor</th></tr></thead><tbody>",
        ]

        for label, value in summary_items:
            html_parts.append(f"<tr><td>{_cell(label)}</td><td>{_cell(value)}</td></tr>")
        html_parts.append("</tbody></table>")

        for section_title, headers, rows, _widths, empty_message in sections:
            headers = tuple(headers or ())
            rows = list(rows or [])
            html_parts.append(f"<h2>{_cell(section_title)}</h2>")
            width_percentages = _column_width_percentages(
                _print_section_widths(section_title, headers, _widths),
                len(headers),
            )
            html_parts.append("<table class='section-table'>")
            if width_percentages:
                html_parts.append("<colgroup>")
                for width_pct in width_percentages:
                    html_parts.append(f"<col style='width:{width_pct:.2f}%'>")
                html_parts.append("</colgroup>")
            html_parts.append("<thead><tr>")
            for header in headers:
                html_parts.append(f"<th>{_cell(header)}</th>")
            html_parts.append("</tr></thead><tbody>")
            if rows:
                for row in rows:
                    normalized_row = list(row[: len(headers)])
                    if len(normalized_row) < len(headers):
                        normalized_row.extend([""] * (len(headers) - len(normalized_row)))
                    html_parts.append("<tr>")
                    for value in normalized_row:
                        html_parts.append(f"<td>{_cell(value)}</td>")
                    html_parts.append("</tr>")
            else:
                col_span = max(1, len(headers))
                html_parts.append(f"<tr><td colspan='{col_span}'>{_cell(empty_message)}</td></tr>")
            html_parts.append("</tbody></table>")

        html_parts.append("</div></body></html>")

        document = QtGui.QTextDocument()
        document.setDefaultFont(QtGui.QFont(self.font().family() or "Lexend", 8))
        page_rect = printer.pageRect(QtPrintSupport.QPrinter.Point)
        document.setPageSize(page_rect.size())
        document.setHtml("".join(html_parts))
        document.print_(printer)
        messagebox.showinfo(corrigir_texto("Impress\u00e3o"), corrigir_texto("Relat\u00f3rio enviado para impress\u00e3o."))

    def _split_pdf_text(self, text: str, max_chars: int) -> list[str]:
        text = str(text or "")
        if len(text) <= max_chars:
            return [text]
        parts = []
        current = []
        current_len = 0
        for word in text.split():
            projected = current_len + len(word) + (1 if current else 0)
            if projected > max_chars and current:
                parts.append(" ".join(current))
                current = [word]
                current_len = len(word)
            else:
                current.append(word)
                current_len = projected
        if current:
            parts.append(" ".join(current))
        return parts or [text]

    def _display_numero(self, numero: str) -> str:
        digits = re.sub(r"\D", "", str(numero or ""))
        if not digits:
            return ""
        return str(int(digits))


class BarChartWidget(QtWidgets.QWidget):
    def __init__(self) -> None:
        super().__init__()
        self._data = []
        self._bar_color = QtGui.QColor("#59C734")
        self._bar_gradient = None
        self._dual_mode = False
        self._dual_colors = (QtGui.QColor("#FF8A00"), QtGui.QColor("#2F6BFF"))
        self._label_color = QtGui.QColor("#f2f2f2")
        self._row_height = 28
        self._label_width = 190
        self._value_padding = 120
        self._padding = 16

    def set_data(
        self,
        data,
        color: QtGui.QColor,
        show_decimals: bool = False,
        gradient_colors: tuple[QtGui.QColor, QtGui.QColor] | None = None,
    ) -> None:
        self._data = data
        self._bar_color = color
        self._show_decimals = show_decimals
        self._bar_gradient = gradient_colors
        self._dual_mode = False
        self._update_size()
        self.update()

    def set_data_dual(
        self,
        data,
        colors: tuple[QtGui.QColor, QtGui.QColor],
        show_decimals: bool = False,
    ) -> None:
        self._data = data
        self._dual_colors = colors
        self._show_decimals = show_decimals
        self._bar_gradient = None
        self._dual_mode = True
        self._update_size()
        self.update()

    def _update_size(self) -> None:
        height = max(1, len(self._data)) * self._row_height + self._padding * 2
        self.setMinimumHeight(height)

    def paintEvent(self, event: QtGui.QPaintEvent) -> None:
        painter = QtGui.QPainter(self)
        painter.setRenderHint(QtGui.QPainter.Antialiasing)
        rect = self.rect()
        painter.fillRect(rect, QtGui.QColor("#1e1e1e"))

        if not self._data:
            painter.setPen(self._label_color)
            painter.drawText(rect, QtCore.Qt.AlignCenter, "Sem dados para exibir.")
            return

        if self._dual_mode:
            max_value = max(max(v1, v2) for _, v1, v2 in self._data) if self._data else 1.0
        else:
            max_value = max(v for _, v in self._data) if self._data else 1.0
        max_value = max(max_value, 1.0)

        bar_area_width = rect.width() - self._label_width - self._padding * 2 - self._value_padding
        y = self._padding
        for entry in self._data:
            if self._dual_mode:
                label, value_a, value_b = entry
            else:
                label, value_a = entry
                value_b = 0.0
            label_rect = QtCore.QRect(
                self._padding,
                y,
                self._label_width - self._padding,
                self._row_height,
            )
            painter.setPen(self._label_color)
            painter.drawText(label_rect, QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft, str(label))

            if self._dual_mode:
                bar_width_a = int((value_a / max_value) * bar_area_width)
                bar_width_b = int((value_b / max_value) * bar_area_width)
                bar_height = (self._row_height - 12) // 2
                bar_rect_a = QtCore.QRect(
                    self._label_width + self._padding,
                    y + 4,
                    max(2, bar_width_a) if value_a > 0 else 0,
                    bar_height,
                )
                bar_rect_b = QtCore.QRect(
                    self._label_width + self._padding,
                    y + 6 + bar_height,
                    max(2, bar_width_b) if value_b > 0 else 0,
                    bar_height,
                )
                painter.setPen(QtCore.Qt.NoPen)
                painter.setBrush(self._dual_colors[0])
                if bar_rect_a.width() > 0:
                    painter.drawRoundedRect(bar_rect_a, 4, 4)
                painter.setBrush(self._dual_colors[1])
                if bar_rect_b.width() > 0:
                    painter.drawRoundedRect(bar_rect_b, 4, 4)
            else:
                bar_width = int((value_a / max_value) * bar_area_width)
                bar_rect = QtCore.QRect(
                    self._label_width + self._padding,
                    y + 6,
                    max(2, bar_width),
                    self._row_height - 12,
                )
                if self._bar_gradient:
                    grad = QtGui.QLinearGradient(bar_rect.topLeft(), bar_rect.topRight())
                    grad.setColorAt(0.0, self._bar_gradient[0])
                    grad.setColorAt(1.0, self._bar_gradient[1])
                    painter.setBrush(grad)
                else:
                    painter.setBrush(self._bar_color)
                painter.setPen(QtCore.Qt.NoPen)
                painter.drawRoundedRect(bar_rect, 4, 4)
            painter.setPen(self._label_color)
            if self._dual_mode:
                if getattr(self, "_show_decimals", False):
                    text_a = f"R$ {value_a:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
                    text_b = f"R$ {value_b:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
                else:
                    text_a = f"{int(round(value_a))}"
                    text_b = f"{int(round(value_b))}"

                if bar_rect_a.width() > 0:
                    text_rect_a = QtCore.QRect(
                        bar_rect_a.right() + 6,
                        bar_rect_a.top() - 2,
                        self._value_padding - self._padding,
                        bar_rect_a.height() + 4,
                    )
                    painter.drawText(text_rect_a, QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft, text_a)
                if bar_rect_b.width() > 0:
                    text_rect_b = QtCore.QRect(
                        bar_rect_b.right() + 6,
                        bar_rect_b.top() - 2,
                        self._value_padding - self._padding,
                        bar_rect_b.height() + 4,
                    )
                    painter.drawText(text_rect_b, QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft, text_b)
            else:
                value_rect = QtCore.QRect(
                    rect.width() - self._value_padding,
                    y,
                    self._value_padding - self._padding,
                    self._row_height,
                )
                if getattr(self, "_show_decimals", False):
                    text = f"R$ {value_a:,.2f}".replace(",", "X").replace(".", ",").replace("X", ".")
                else:
                    text = f"{int(round(value_a))}"
                painter.drawText(value_rect, QtCore.Qt.AlignVCenter | QtCore.Qt.AlignLeft, text)

            y += self._row_height


def exportar_planilha_pdf(tree: QtTreeAdapter, titulo: str) -> None:
    from reportlab.lib.pagesizes import A4
    from reportlab.pdfgen import canvas

    rows = [tree.item(i)["values"] for i in tree.get_children()]
    cols = [tree.heading(col)["text"] for col in tree["columns"]]

    if not rows:
        messagebox.showwarning("Aviso", "Não há dados para exportar.")
        return

    caminho = filedialog.asksaveasfilename(
        defaultextension=".pdf",
        filetypes=[("PDF", "*.pdf")],
        title=f"Exportar {titulo}",
    )
    if not caminho:
        return

    c = canvas.Canvas(caminho, pagesize=A4)
    largura, altura = A4
    y = altura - 40
    title_font_name, body_font_name = _get_reportlab_font_names()

    c.setFont(title_font_name, 12)
    c.drawString(50, y, titulo)
    y -= 24

    c.setFont(title_font_name, 9)
    for i, col in enumerate(cols):
        c.drawString(50 + i * 150, y, col)
    y -= 16

    c.setFont(body_font_name, 8.5)
    for row in rows:
        for i, val in enumerate(row):
            c.drawString(50 + i * 150, y, str(val))
        y -= 18
        if y < 40:
            c.showPage()
            y = altura - 40
            c.setFont(body_font_name, 8.5)

    c.save()
    messagebox.showinfo("Sucesso", f"PDF salvo em:\n{caminho}")


class MainWindow(QtWidgets.QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle("Relatório de Vendedor")
        self.setMinimumSize(1050, 800)
        self.resize(1200, 860)
        self._ui_font_family = "Lexend"
        self._setup_icon()
        self._load_app_font()
        self._sort_state = {}
        self._edit_mode = False
        self._table_dirty = False
        self._neon_on = False
        self._neon_hue = 0
        self._showing_graphs = False
        self._automation_enabled = True
        self._automation_schedule = {
            "afternoon": QtCore.QTime(8, 0),
            "morning": QtCore.QTime(13, 30),
        }
        self._automation_running = False
        self._automation_next_run: dt.datetime | None = None
        self._automation_next_scope: str | None = None
        self._automation_test_run_at: dt.datetime | None = None
        self._automation_test_scope = "morning"
        self._automation_last_status = "Automacao pronta: tarde do dia anterior às 08:00 e manhã do dia atual às 13:30."
        self._eh_pending_runs: dict[str, dict] = {"morning": {}, "afternoon": {}}
        self._mva_pending_runs: dict[str, dict] = {"morning": {}, "afternoon": {}}
        self._pending_print_jobs: dict[str, list[dict[str, str]]] = {"EH": [], "MVA": []}
        self._eh_special_closing_enabled = False
        self._mva_special_scope_enabled = False
        self._gmail_status_cache: dict[str, object] | None = None
        self._gmail_status_checked_at = 0.0

        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        main_layout = QtWidgets.QHBoxLayout(central)
        main_layout.setContentsMargins(10, 10, 10, 10)

        self._setup_styles()

        self.btn_select_pdf = QtWidgets.QPushButton("Importar")
        self.btn_select_pdf.setObjectName("btn_import")
        btn_policy = QtWidgets.QSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Fixed)
        self.btn_caixa = QtWidgets.QPushButton("Caixa")
        self.btn_spreadsheet = QtWidgets.QPushButton("Planilha online")
        self.btn_export = QtWidgets.QPushButton("Exportar")
        self.btn_edit_table = QtWidgets.QPushButton("Editar")
        self.btn_graphs = QtWidgets.QPushButton("Gráficos")
        self.btn_clear = QtWidgets.QPushButton("Limpar")
        self.btn_merge = QtWidgets.QPushButton("Mesclar Planilhas")
        self.btn_tag = QtWidgets.QPushButton("Criar Etiquetas")
        self.btn_settings = QtWidgets.QPushButton()
        self.btn_settings.setText("⚙")
        self.btn_settings.setObjectName("settingsActionButton")
        self.btn_settings.setFixedSize(36, 36)
        self.btn_settings.setCursor(QtGui.QCursor(QtCore.Qt.PointingHandCursor))
        self.btn_settings.setToolTip("Configurações de relatórios")
        self.btn_automation_test = QtWidgets.QPushButton("Teste automacao (5s)")
        self.btn_eh_pending_print = QtWidgets.QPushButton("EH impressao pendente")
        self.btn_eh_pending_morning = QtWidgets.QPushButton("EH manhÃ£ pendente")
        self.btn_eh_pending_afternoon = QtWidgets.QPushButton("EH tarde pendente")
        self.btn_mva_pending_print = QtWidgets.QPushButton("MVA impressao pendente")
        self.btn_mva_pending_morning = QtWidgets.QPushButton("MVA manhã pendente")
        self.btn_mva_pending_afternoon = QtWidgets.QPushButton("MVA tarde pendente")
        for btn in (
            self.btn_select_pdf,
            self.btn_caixa,
            self.btn_spreadsheet,
            self.btn_export,
            self.btn_edit_table,
            self.btn_graphs,
            self.btn_clear,
            self.btn_merge,
            self.btn_tag,
            self.btn_automation_test,
            self.btn_eh_pending_print,
            self.btn_eh_pending_morning,
            self.btn_eh_pending_afternoon,
            self.btn_mva_pending_print,
            self.btn_mva_pending_morning,
            self.btn_mva_pending_afternoon,
        ):
            btn.setSizePolicy(btn_policy)
            btn.setMinimumHeight(36)

        self.btn_eh_pending_print.setVisible(False)
        self.btn_eh_pending_print.setEnabled(False)
        self.btn_eh_pending_morning.setVisible(False)
        self.btn_eh_pending_afternoon.setVisible(False)
        self.btn_eh_pending_morning.setEnabled(False)
        self.btn_eh_pending_afternoon.setEnabled(False)
        self.btn_mva_pending_print.setVisible(False)
        self.btn_mva_pending_print.setEnabled(False)
        self.btn_mva_pending_morning.setVisible(False)
        self.btn_mva_pending_afternoon.setVisible(False)
        self.btn_mva_pending_morning.setEnabled(False)
        self.btn_mva_pending_afternoon.setEnabled(False)

        sidebar = QtWidgets.QFrame()
        sidebar.setObjectName("sidebarPanel")
        sidebar.setFixedWidth(250)
        sidebar_layout = QtWidgets.QVBoxLayout(sidebar)
        sidebar_layout.setContentsMargins(16, 18, 16, 18)
        sidebar_layout.setSpacing(14)

        app_title = QtWidgets.QLabel("Relatórios")
        app_title.setObjectName("appTitleLabel")
        app_title.setAlignment(QtCore.Qt.AlignCenter)
        app_subtitle = QtWidgets.QLabel("Fluxo diário de caixa e vendedores")
        app_subtitle.setObjectName("appSubtitleLabel")
        app_subtitle.setWordWrap(True)
        app_subtitle.setAlignment(QtCore.Qt.AlignCenter)
        sidebar_layout.addWidget(app_title)
        sidebar_layout.addWidget(app_subtitle)
        sidebar_layout.addWidget(
            self._build_sidebar_section(
                "Operação",
                (
                    self.btn_select_pdf,
                    self.btn_caixa,
                    self.btn_spreadsheet,
                    self.btn_merge,
                    self.btn_tag,
                    self.btn_clear,
                ),
            )
        )
        sidebar_layout.addWidget(
            self._build_sidebar_section(
                "Saída e análise",
                (
                    self.btn_export,
                    self.btn_edit_table,
                    self.btn_graphs,
                ),
            )
        )
        sidebar_layout.addWidget(
            self._build_sidebar_section(
                "Automação",
                (
                    self.btn_automation_test,
                    self.btn_eh_pending_print,
                    self.btn_eh_pending_morning,
                    self.btn_eh_pending_afternoon,
                    self.btn_mva_pending_print,
                    self.btn_mva_pending_morning,
                    self.btn_mva_pending_afternoon,
                ),
            )
        )
        sidebar_layout.addStretch(1)
        self._apply_soft_shadow(sidebar, blur=34.0, offset_y=10.0, color=QtGui.QColor(7, 12, 20, 140))

        main_layout.addWidget(sidebar, 0)

        right_scroll = QtWidgets.QScrollArea()
        right_scroll.setObjectName("mainScrollArea")
        right_scroll.setWidgetResizable(True)
        right_scroll.setFrameShape(QtWidgets.QFrame.NoFrame)
        right_scroll.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarAlwaysOff)
        right_scroll.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarAsNeeded)
        right_scroll.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Expanding)

        right_page = QtWidgets.QWidget()
        right_page.setObjectName("mainScrollPage")
        right_panel = QtWidgets.QVBoxLayout(right_page)
        right_panel.setContentsMargins(0, 0, 4, 0)
        right_panel.setSpacing(14)

        header_frame = QtWidgets.QFrame()
        header_frame.setObjectName("heroCard")
        header_layout = QtWidgets.QVBoxLayout(header_frame)
        header_layout.setContentsMargins(18, 16, 18, 16)
        header_layout.setSpacing(6)
        header_title = QtWidgets.QLabel("Hub operacional")
        header_title.setObjectName("heroTitleLabel")
        header_title.setAlignment(QtCore.Qt.AlignCenter)
        self.label_files = QtWidgets.QLabel("Nenhum arquivo carregado")
        self.label_files.setObjectName("heroSubtitleLabel")
        self.label_files.setAlignment(QtCore.Qt.AlignCenter)
        self.label_files.setWordWrap(True)
        header_layout.addWidget(header_title)
        header_layout.addWidget(self.label_files)
        self._apply_soft_shadow(header_frame, blur=30.0, offset_y=8.0, color=QtGui.QColor(10, 16, 28, 130))
        right_panel.addWidget(header_frame)

        status_row = QtWidgets.QHBoxLayout()
        status_row.setSpacing(12)
        status_row.addStretch(1)
        self._status_cards: dict[str, dict[str, QtWidgets.QLabel]] = {}
        for key, title in (
            ("automation", "Automação"),
            ("pending", "Pendências"),
            ("gmail", "Gmail"),
            ("workspace", "Workspace"),
        ):
            frame, value_label, note_label = self._create_status_card(title, key)
            self._status_cards[key] = {"frame": frame, "value": value_label, "note": note_label}
            status_row.addWidget(frame, 0)
        status_row.addStretch(1)
        right_panel.addLayout(status_row)

        controls_frame = QtWidgets.QFrame()
        controls_frame.setObjectName("controlsCard")
        controls_layout = QtWidgets.QVBoxLayout(controls_frame)
        controls_layout.setContentsMargins(16, 14, 16, 14)
        controls_layout.setSpacing(10)

        self.btn_cancel = QtWidgets.QPushButton("Cancelar")
        self.btn_cancel.setSizePolicy(btn_policy)
        self.btn_cancel.setEnabled(False)
        self.btn_cancel.setObjectName("secondaryActionButton")
        self.btn_automation_power = QtWidgets.QPushButton()
        self.btn_automation_power.setFixedSize(36, 36)
        self.btn_automation_power.setObjectName("powerActionButton")
        self.btn_automation_power.setCursor(QtGui.QCursor(QtCore.Qt.PointingHandCursor))

        self.progress_bar = QtWidgets.QProgressBar()
        self.progress_bar.setMinimumHeight(20)
        self.progress_var = QtVar(self.progress_bar.setValue, 0)
        self.progress_bar_adapter = QtProgressBarAdapter(self.progress_bar)
        progress_row = QtWidgets.QHBoxLayout()
        progress_row.setSpacing(10)
        progress_row.addWidget(self.progress_bar, 1)
        progress_row.addWidget(self.btn_cancel, 0)
        progress_row.addWidget(self.btn_settings, 0)
        progress_row.addWidget(self.btn_automation_power, 0)
        controls_layout.addLayout(progress_row)

        self.progress_bar_online = QtWidgets.QProgressBar()
        self.progress_bar_online.setMinimumHeight(14)
        self.progress_var_online = QtVar(self.progress_bar_online.setValue, 0)
        self.progress_bar_online_adapter = QtProgressBarAdapter(self.progress_bar_online)
        self.progress_bar_online.setVisible(False)
        controls_layout.addWidget(self.progress_bar_online)
        self._apply_soft_shadow(controls_frame, blur=24.0, offset_y=8.0, color=QtGui.QColor(8, 14, 22, 115))
        right_panel.addWidget(controls_frame)

        self.cols_main = ("Vendedor", "Atendidos", "Devoluções", "Total Final", "Total Vendas")
        self.cols_online = ("Vendedor", "Clientes", "Valor Total")
        self.table_main = EmptyStateTableWidget()
        self.table_main.setProperty("editModeActive", False)
        self.table_main.setSortingEnabled(False)
        self.table_main.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        self.table_main.setSelectionMode(QtWidgets.QAbstractItemView.SingleSelection)
        self.table_main.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectItems)
        self.table_main.setMouseTracking(True)
        self.table_main.horizontalHeader().setDefaultAlignment(QtCore.Qt.AlignCenter)
        self.table_main.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Expanding)
        self.table_main.setMinimumHeight(430)
        self.table_main.set_empty_state(_build_empty_table_icon(96))

        self.tree_main = QtTreeAdapter(self.table_main, self.cols_main)
        self.table_main.horizontalHeader().setSectionResizeMode(0, QtWidgets.QHeaderView.Stretch)
        for index in range(1, len(self.cols_main)):
            self.table_main.horizontalHeader().setSectionResizeMode(index, QtWidgets.QHeaderView.ResizeToContents)
        self.table_main.horizontalHeader().setMinimumSectionSize(84)
        self.table_main.verticalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)
        self.table_main.horizontalHeader().sectionClicked.connect(
            lambda idx: self._sort_table(self.tree_main, self.cols_main, idx)
        )
        self.table_main.itemChanged.connect(self._on_table_item_changed)
        self.table_main.cellEntered.connect(self._sync_table_hover_selection)
        self.table_main.cellPressed.connect(lambda row, column: self._sync_table_hover_selection(row, column, force=True))

        self.online_container = QtWidgets.QWidget()
        self.online_container.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Expanding)
        self.online_container.setMinimumHeight(600)
        online_frame = QtWidgets.QHBoxLayout(self.online_container)

        self._setup_planilha_section(
            online_frame,
            "Planilha Online - MVA",
            self._export_planilha_mva,
            is_left=True,
        )
        self._setup_planilha_section(
            online_frame,
            "Planilha Online - EH",
            self._export_planilha_eh,
            is_left=False,
        )

        dashboard_page = QtWidgets.QWidget()
        dashboard_layout = QtWidgets.QVBoxLayout(dashboard_page)
        dashboard_layout.setContentsMargins(0, 0, 0, 0)
        dashboard_layout.setSpacing(14)
        dashboard_layout.addWidget(self._create_content_card("", self.table_main))
        dashboard_layout.addWidget(self._create_content_card("", self.online_container))
        dashboard_layout.addStretch(1)

        self.graphs_view = self._build_graphs_view()
        self.content_stack = QtWidgets.QStackedWidget()
        self.content_stack.addWidget(dashboard_page)
        self.content_stack.addWidget(self._create_content_card("Gráficos", self.graphs_view))
        self.content_stack.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Preferred)
        right_panel.addWidget(self.content_stack)
        right_panel.addStretch(1)

        self.label_files_var = QtVar(self._set_loaded_files_text, "Nenhum arquivo carregado")
        self.root_adapter = QtRootAdapter(self)
        self._bind_actions()
        self._setup_import_neon()
        self._setup_progress_visibility_timer()
        self._setup_graphs_refresh_timer()
        self._load_pending_print_jobs()
        self._setup_daily_automation_timer()
        self._refresh_dashboard_status_cards()

        set_ui_refs(
            btn_cancel=QtButtonAdapter(self.btn_cancel),
            progress_var=self.progress_var,
            progress_bar=self.progress_bar_adapter,
            progress_var_online=self.progress_var_online,
            progress_bar_online=self.progress_bar_online_adapter,
            btn_tag=QtButtonAdapter(self.btn_tag),
            btn_add_mais=QtButtonAdapter(self.btn_select_pdf),
            btn_merge_spreadsheet=QtButtonAdapter(self.btn_merge),
            btn_select_pdf=QtButtonAdapter(self.btn_select_pdf),
        )
        set_parent(self)
        check_for_updates(self.root_adapter)

        right_scroll.setWidget(right_page)
        main_layout.addWidget(right_scroll, 1)

    def _build_sidebar_section(
        self,
        title: str,
        buttons: tuple[QtWidgets.QPushButton, ...],
    ) -> QtWidgets.QFrame:
        frame = QtWidgets.QFrame()
        frame.setObjectName("sidebarSection")
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(8)
        label = QtWidgets.QLabel(corrigir_texto(title))
        label.setObjectName("sidebarSectionTitle")
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        for button in buttons:
            layout.addWidget(button)
        self._apply_soft_shadow(frame, blur=18.0, offset_y=5.0, color=QtGui.QColor(10, 14, 24, 90))
        return frame

    def _create_status_card(
        self,
        title: str,
        card_type: str = "default",
    ) -> tuple[QtWidgets.QFrame, QtWidgets.QLabel, QtWidgets.QLabel]:
        frame = QtWidgets.QFrame()
        frame.setObjectName("statusCard")
        frame.setProperty("cardType", card_type)
        frame.setProperty("cardState", "default")
        frame.setFixedWidth(184)
        frame.setSizePolicy(QtWidgets.QSizePolicy.Fixed, QtWidgets.QSizePolicy.Preferred)
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(14, 12, 14, 12)
        layout.setSpacing(4)
        label = QtWidgets.QLabel(corrigir_texto(title))
        label.setObjectName("statusCardTitle")
        value = QtWidgets.QLabel("--")
        value.setObjectName("statusCardValue")
        note = QtWidgets.QLabel("")
        note.setObjectName("statusCardNote")
        note.setWordWrap(True)
        label.setAlignment(QtCore.Qt.AlignCenter)
        value.setAlignment(QtCore.Qt.AlignCenter)
        note.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        layout.addWidget(value)
        layout.addWidget(note)
        self._apply_soft_shadow(frame, blur=20.0, offset_y=6.0, color=QtGui.QColor(9, 14, 22, 88))
        return frame, value, note

    def _create_content_card(self, title: str, widget: QtWidgets.QWidget) -> QtWidgets.QFrame:
        frame = QtWidgets.QFrame()
        frame.setObjectName("contentCard")
        layout = QtWidgets.QVBoxLayout(frame)
        layout.setContentsMargins(16, 14, 16, 16)
        layout.setSpacing(10)
        if str(title or "").strip():
            label = QtWidgets.QLabel(corrigir_texto(title))
            label.setObjectName("contentCardTitle")
            layout.addWidget(label)
        layout.addWidget(widget, 1)
        self._apply_soft_shadow(frame, blur=24.0, offset_y=7.0, color=QtGui.QColor(8, 14, 22, 100))
        return frame

    def _apply_soft_shadow(
        self,
        widget: QtWidgets.QWidget,
        *,
        blur: float = 26.0,
        offset_y: float = 8.0,
        color: QtGui.QColor | None = None,
    ) -> None:
        _apply_soft_shadow(widget, blur=blur, offset_y=offset_y, color=color)

    def _set_loaded_files_text(self, value: object) -> None:
        text = corrigir_texto(str(value or "Nenhum arquivo carregado"))
        self.label_files.setText(text)
        self._refresh_dashboard_status_cards()

    def _set_status_card(self, key: str, value: str, note: str) -> None:
        card = self._status_cards.get(key) or {}
        frame = card.get("frame")
        value_label = card.get("value")
        note_label = card.get("note")
        if value_label:
            value_label.setText(corrigir_texto(value))
        if note_label:
            note_label.setText(corrigir_texto(note))
        if frame is not None:
            next_state = "default"
            if key == "workspace":
                next_state = "ready" if corrigir_texto(value).strip().casefold() == "pronto" else "waiting"
            if frame.property("cardState") != next_state:
                frame.setProperty("cardState", next_state)
                style = frame.style()
                if style is not None:
                    style.unpolish(frame)
                    style.polish(frame)
                frame.update()

    def _get_cached_gmail_status(self, *, force: bool = False) -> dict[str, object]:
        now = time.time()
        if (
            not force
            and self._gmail_status_cache is not None
            and now - self._gmail_status_checked_at < 20.0
        ):
            return self._gmail_status_cache
        try:
            status = get_gmail_oauth_status()
        except Exception as exc:
            status = {
                "ok": False,
                "needs_auth": True,
                "status": "error",
                "title": "Gmail não verificado",
                "message": f"Não foi possível verificar a autenticação do Gmail: {exc}",
            }
        self._gmail_status_cache = status
        self._gmail_status_checked_at = now
        return status

    def _ensure_gmail_authenticated_for_caixa(self) -> bool:
        status = self._get_cached_gmail_status(force=True)
        if not bool(status.get("needs_auth")):
            return True

        title = corrigir_texto(str(status.get("title") or "Gmail não autenticado"))
        message = corrigir_texto(str(status.get("message") or "O Gmail precisa ser autenticado."))
        proceed = messagebox.askyesno(
            title,
            (
                f"{message}\n\n"
                "O Caixa usa o Gmail para ler os códigos enviados pela Caixa/Azulzinha e pela Cielo.\n\n"
                "Deseja autenticar o Gmail agora, antes de continuar?"
            ),
        )
        if not proceed:
            return False

        cancel_loading = threading.Event()

        def worker(push_status: Callable[[str], None], result: dict) -> None:
            push_status("Abrindo autorização do Gmail no navegador...")
            creds = _get_gmail_api_credentials(on_status=push_status, cancel_event=cancel_loading)
            result["ok"] = bool(creds and getattr(creds, "valid", False))

        result, was_cancelled = self._run_loading_worker(
            "Autenticação do Gmail",
            "Autorize o Gmail no navegador para continuar.",
            worker,
            cancel_event=cancel_loading,
        )
        self._gmail_status_cache = None
        self._gmail_status_checked_at = 0.0
        self._refresh_dashboard_status_cards()

        if was_cancelled:
            messagebox.showwarning("Gmail", "Autenticação do Gmail cancelada.")
            return False
        if result.get("error"):
            messagebox.showerror("Gmail", f"Não foi possível autenticar o Gmail:\n{result['error']}")
            return False
        status_after = self._get_cached_gmail_status(force=True)
        if bool(status_after.get("needs_auth")):
            messagebox.showwarning(
                "Gmail",
                corrigir_texto(str(status_after.get("message") or "O Gmail ainda não está autenticado.")),
            )
            return False
        return True

    def _refresh_dashboard_status_cards(self) -> None:
        if not hasattr(self, "_status_cards"):
            return
        self._refresh_import_button_state()
        next_run = self._automation_next_run
        next_scope = self._automation_next_scope or "morning"
        if self._automation_enabled and next_run is not None:
            value = "Ligada"
            note = f"{self._scope_label_text(next_scope).capitalize()} às {next_run.strftime('%H:%M')}"
        elif self._automation_running:
            value = "Executando"
            note = corrigir_texto(self._automation_last_status or "Processando automação.")
        else:
            value = "Pausada"
            note = corrigir_texto(self._automation_last_status or "Automação desligada.")
        self._set_status_card("automation", value, note)

        pending_eh = (
            bool(self._pending_print_jobs_for_company("EH"))
            or bool(self._eh_pending_runs.get("morning"))
            or bool(self._eh_pending_runs.get("afternoon"))
        )
        pending_mva = (
            bool(self._pending_print_jobs_for_company("MVA"))
            or bool(self._mva_pending_runs.get("morning"))
            or bool(self._mva_pending_runs.get("afternoon"))
        )
        pending_labels = [label for label, enabled in (("EH", pending_eh), ("MVA", pending_mva)) if enabled]
        pending_total = len(pending_labels)
        self._set_status_card(
            "pending",
            str(pending_total),
            " | ".join(pending_labels),
        )

        gmail_status = self._get_cached_gmail_status()
        gmail_status_key = str(gmail_status.get("status") or "")
        if bool(gmail_status.get("needs_auth")):
            gmail_value = "Atenção"
            gmail_note = "Autenticar antes do Caixa"
        elif gmail_status_key == "refreshable":
            gmail_value = "OK"
            gmail_note = "Renova automático"
        else:
            gmail_value = "OK"
            gmail_note = "Autenticado"
        self._set_status_card("gmail", gmail_value, gmail_note)

        file_text = corrigir_texto(self.label_files.text() or "Nenhum arquivo carregado")
        file_summary = file_text if len(file_text) <= 70 else f"{file_text[:67]}..."
        self._set_status_card(
            "workspace",
            "Pronto" if self._has_table_data() else "Aguardando",
            file_summary,
        )

    def _setup_icon(self) -> None:
        icon_path = resource_path("icone.ico")
        if os.path.exists(icon_path):
            self.setWindowIcon(QtGui.QIcon(icon_path))

    def _load_app_font(self) -> None:
        def _apply_ui_font(font: QtGui.QFont) -> None:
            font.setPointSize(10)
            font.setStyleStrategy(QtGui.QFont.PreferAntialias)
            app = QtWidgets.QApplication.instance()
            if app is not None:
                app.setFont(font)
            self.setFont(font)

        font_path = resource_path(os.path.join("data", "Lexend-Regular.ttf"))
        if not os.path.exists(font_path):
            self._ui_font_family = QtWidgets.QApplication.font().family() or "Sans Serif"
            _apply_ui_font(QtGui.QFont(self._ui_font_family))
            return
        font_id = QtGui.QFontDatabase.addApplicationFont(font_path)
        if font_id == -1:
            self._ui_font_family = QtWidgets.QApplication.font().family() or "Sans Serif"
            _apply_ui_font(QtGui.QFont(self._ui_font_family))
            return
        families = QtGui.QFontDatabase.applicationFontFamilies(font_id)
        if families:
            self._ui_font_family = families[0]
            app_font = QtGui.QFont(families[0])
            _apply_ui_font(app_font)

    def _setup_styles(self) -> None:
        font_family = corrigir_texto(
            getattr(self, "_ui_font_family", "") or QtWidgets.QApplication.font().family() or "Lexend"
        )
        bg_main = "#1F232C"
        text_main = "#F2F4F5"
        text_soft = "#D1D5D9"
        text_muted = "#A5AAB0"
        border_main = "#46505D"
        border_soft = "#37414D"
        slate_a = "#2B313B"
        slate_b = "#242934"
        slate_c = "#2A313A"
        blue_a = "#24384A"
        blue_b = "#223041"
        teal_a = "#24D4E6"
        teal_b = "#1395A7"
        bronze_a = "#B8913E"
        bronze_b = "#7C6731"
        rust_a = "#E06A6A"
        rust_b = "#7C424B"
        self.setStyleSheet(
            f"QWidget{{background-color:{bg_main};color:{text_main};font-family:'{font_family}';font-weight:400;}}"
            "QLabel,QCheckBox,QRadioButton{background:transparent;}"
            f"QPushButton,QLabel,QTableWidget,QTableView,QHeaderView::section,QTabBar::tab,QMenu,QComboBox,QToolTip,QProgressBar{{font-family:'{font_family}';}}"
            f"QFrame#sidebarPanel{{background:qlineargradient(x1:0,y1:0,x2:0,y2:1,stop:0 #202938,stop:0.45 {blue_a},stop:1 #1E2430);border:1px solid #3B4F66;border-radius:22px;}}"
            f"QFrame#heroCard{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2A3340,stop:0.55 #24303D,stop:1 #28313B);border:1px solid #4D5865;border-bottom:4px solid {teal_a};border-radius:22px;}}"
            f"QFrame#controlsCard,QFrame#contentCard,QFrame#summaryCard,QFrame#dialogHeaderCard,QFrame#inlineTotalCard{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2B313B,stop:0.65 {slate_c},stop:1 {slate_b});border:1px solid {border_main};border-radius:18px;}}"
            f"QFrame#contentSubCard{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2A313B,stop:1 #242A34);border:1px solid {border_main};border-radius:18px;}}"
            f"QFrame#contentSubCard[accent=\"cyan\"]{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #29313B,stop:1 #222A34);border:2px solid {teal_a};border-radius:18px;}}"
            f"QFrame#statusCard{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2B313B,stop:1 #242A34);border:1px solid {border_main};border-radius:18px;}}"
            f"QFrame#statusCard[cardType=\"automation\"]{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #25323F,stop:1 #222B36);border:2px solid {teal_a};border-radius:18px;}}"
            f"QFrame#statusCard[cardType=\"workspace\"][cardState=\"waiting\"]{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #8D6E2B,stop:1 #A8832F);border:1px solid #D1B46D;border-radius:18px;}}"
            f"QFrame#statusCard[cardType=\"workspace\"][cardState=\"ready\"]{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2F6C44,stop:1 #4AA164);border:1px solid #7FD39B;border-radius:18px;}}"
            f"QFrame#statusCard[cardType=\"workspace\"][cardState=\"waiting\"] QLabel#statusCardTitle{{color:#F4E2AF;}}"
            f"QFrame#statusCard[cardType=\"workspace\"][cardState=\"waiting\"] QLabel#statusCardValue{{color:#FFD36A;}}"
            f"QFrame#statusCard[cardType=\"workspace\"][cardState=\"waiting\"] QLabel#statusCardNote{{color:#F6E5B2;}}"
            "QFrame#statusCard[cardType=\"workspace\"][cardState=\"ready\"] QLabel#statusCardTitle{color:#D8F4E1;}"
            "QFrame#statusCard[cardType=\"workspace\"][cardState=\"ready\"] QLabel#statusCardValue{color:#F3FFF7;}"
            "QFrame#statusCard[cardType=\"workspace\"][cardState=\"ready\"] QLabel#statusCardNote{color:#D8F6E2;}"
            f"QFrame#sidebarSection{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2A303A,stop:1 #242A34);border:1px solid {border_soft};border-radius:18px;}}"
            f"QFrame#reportSectionCard{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #26303D,stop:0.68 {slate_c},stop:1 {slate_b});border:1px solid {border_main};border-radius:16px;}}"
            f"QFrame#reportSectionCard[tone=\"warning\"]{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {rust_b},stop:0.42 {slate_c},stop:1 {slate_b});border:1px solid {rust_a};}}"
            f"QFrame#metaChip{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #253441,stop:1 #222B36);border:1px solid #5B6A74;border-radius:12px;}}"
            f"QLabel#appTitleLabel{{font-size:20px;font-weight:400;color:{text_main};}}"
            f"QLabel#appSubtitleLabel{{font-size:11px;color:{text_soft};}}"
            f"QLabel#sidebarSectionTitle,QLabel#contentCardTitle,QLabel#sectionTitleLabel{{font-size:11px;font-weight:400;color:#E5E8EA;letter-spacing:0.5px;}}"
            f"QLabel#heroTitleLabel,QLabel#dialogTitleLabel{{font-size:22px;font-weight:400;color:#FAFBFB;}}"
            f"QLabel#heroSubtitleLabel,QLabel#sectionHintLabel,QLabel#statusCardNote,QLabel#metaChipLabel{{font-size:11px;color:{text_muted};}}"
            f"QLabel#statusCardTitle{{font-size:11px;font-weight:400;color:{text_muted};letter-spacing:0.4px;}}"
            f"QLabel#statusCardValue,QLabel#metaChipValue{{font-size:18px;font-weight:400;color:{text_main};}}"
            f"QLabel#reportBadge{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {bronze_a},stop:1 {bronze_b});color:#1F232A;border:1px solid #D1B46D;border-radius:12px;font-weight:400;padding:6px 10px;}}"
            f"QLabel#statusChipSuccess{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {teal_b},stop:1 {teal_a});color:#F4FCFD;border:1px solid #6CB6BE;border-radius:12px;padding:6px 12px;font-weight:400;}}"
            f"QLabel#statusChipWarning{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {rust_a},stop:1 #D35656);color:#FFF7F4;border:1px solid #E49595;border-radius:12px;padding:6px 12px;font-weight:400;}}"
            f"QPushButton{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2A313C,stop:1 #212833);border:1px solid #404A56;border-radius:14px;padding:8px 12px;text-align:center;color:{text_main};}}"
            f"QPushButton:hover{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #313A46,stop:1 #26303B);border-color:#6A7684;}}"
            f"QPushButton:pressed{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #284754,stop:1 #25343F);}}"
            f"QPushButton:disabled{{color:#7F868C;background:{slate_a};border-color:{border_soft};}}"
            f"QPushButton#primaryActionButton{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {bronze_a},stop:1 {bronze_b});color:#1D2229;border:1px solid #D1B46D;font-weight:400;}}"
            f"QPushButton#btn_import{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #F07B7E,stop:1 #D85F68);color:#2A1014;border:1px solid #F1A1A5;font-weight:400;}}"
            f"QPushButton#btn_import:disabled{{color:#7F868C;background:{slate_a};border:1px solid {border_soft};font-weight:400;}}"
            f"QPushButton#primaryActionButton:hover{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #C89A4E,stop:1 #8F7337);}}"
            f"QPushButton#btn_import:hover{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #F58B8D,stop:1 #DF6A72);}}"
            f"QPushButton#secondaryActionButton,QPushButton#powerActionButton,QPushButton#settingsActionButton{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #2B313B,stop:1 #232A34);border-color:#505A67;}}"
            "QPushButton#settingsActionButton{font-size:18px;padding:0px;}"
            f"QTableWidget,QTableView{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {slate_c},stop:1 {slate_b});alternate-background-color:#2B3138;gridline-color:{border_soft};border:1px solid {border_main};border-radius:10px;selection-background-color:{teal_b};selection-color:#F7FCFC;}}"
            "QTableWidget[editModeActive=\"true\"]{gridline-color:#8F575D;border:1px solid #9A5D64;}"
            "QTableWidget[editModeActive=\"true\"]::item:hover,QTableWidget[editModeActive=\"true\"]::item:selected{background-color:#5A4148;color:#F7FCFC;}"
            f"QTextEdit,QPlainTextEdit,QLineEdit,QDateEdit,QComboBox,QAbstractSpinBox{{background:{slate_c};color:{text_main};border:1px solid {border_main};border-radius:10px;padding:6px 8px;selection-background-color:{teal_b};selection-color:#F7FCFC;}}"
            "QTableWidget::item{text-align:center;}"
            f"QHeaderView::section{{background:qlineargradient(x1:0,y1:0,x2:1,y2:0,stop:0 #35485D,stop:0.55 #304457,stop:1 #3E5267);color:{teal_a};font-weight:400;text-align:center;border:none;border-right:1px solid {border_main};padding:8px;}}"
            "QScrollArea{border:none;background:transparent;}"
            "QWidget#tableEmptyState{background:transparent;}"
            f"QLabel#tableEmptyStateHint{{color:{text_muted};font-size:9px;font-weight:400;background:transparent;}}"
            f"QProgressBar{{background:#20252C;color:{text_main};border:1px solid {border_soft};border-radius:14px;text-align:center;padding:2px;}}"
            f"QProgressBar::chunk{{background:qlineargradient(x1:0,y1:0,x2:1,y2:0,stop:0 {teal_b},stop:1 {teal_a});border-radius:12px;}}"
            f"QTabWidget::pane{{border:1px solid {border_soft};border-radius:14px;top:-1px;background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 {slate_a},stop:1 {slate_b});}}"
            f"QTabBar::tab{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #313740,stop:1 {slate_b});color:{text_soft};padding:10px 14px;border-top-left-radius:10px;border-top-right-radius:10px;margin-right:4px;font-weight:400;}}"
            f"QTabBar::tab:selected{{background:qlineargradient(x1:0,y1:0,x2:1,y2:1,stop:0 #334A60,stop:1 #2A3A4A);color:{teal_a};}}"
            "QToolButton{background:transparent;}"
        )

    def _setup_planilha_section(self, parent_layout, title, export_fn, is_left: bool) -> None:
        frame = QtWidgets.QFrame()
        frame.setObjectName("contentSubCard")
        frame.setProperty("accent", "cyan")
        frame_layout = QtWidgets.QVBoxLayout(frame)
        header = QtWidgets.QHBoxLayout()

        label = QtWidgets.QLabel(title)
        label.setObjectName("contentCardTitle")
        label.setAlignment(QtCore.Qt.AlignCenter)
        btn_export = QtWidgets.QPushButton()
        btn_export.setObjectName("primaryActionButton")
        btn_export.setFixedSize(30, 30)
        pdf_icon_path = resource_path("pdf_icon.png")
        if os.path.exists(pdf_icon_path):
            btn_export.setIcon(QtGui.QIcon(pdf_icon_path))
        btn_export.clicked.connect(export_fn)
        header.addStretch()
        header.addWidget(label)
        header.addWidget(btn_export)
        header.addStretch()
        frame_layout.addLayout(header)

        cols = self.cols_online
        table = EmptyStateTableWidget()
        table.setColumnCount(len(cols))
        table.setHorizontalHeaderLabels(list(cols))
        table.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        table.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Expanding)
        table.setMinimumHeight(400)
        table.setWordWrap(False)
        table.setTextElideMode(QtCore.Qt.ElideRight)
        table.setAlternatingRowColors(True)
        table.verticalHeader().setVisible(False)
        table.verticalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeToContents)
        table.horizontalHeader().setSectionResizeMode(0, QtWidgets.QHeaderView.Stretch)
        table.horizontalHeader().setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeToContents)
        table.horizontalHeader().setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeToContents)
        table.horizontalHeader().setMinimumSectionSize(80)
        online_font = QtGui.QFont(self._ui_font_family or self.font().family() or "Lexend")
        online_font.setPointSize(max(8, self.font().pointSize() - 2))
        table.setFont(online_font)
        header_font = QtGui.QFont(online_font)
        header_font.setPointSize(max(8, online_font.pointSize()))
        header_font.setWeight(QtGui.QFont.Normal)
        table.horizontalHeader().setFont(header_font)
        table.set_empty_state(_build_empty_table_icon(84))
        frame_layout.addWidget(table)

        adapter = QtTreeAdapter(table, cols, hide_header_when_empty=True)
        table.horizontalHeader().sectionClicked.connect(
            lambda idx: self._sort_table(adapter, cols, idx)
        )

        if is_left:
            self.tree_mva = adapter
            self.table_mva = table
        else:
            self.tree_eh = adapter
            self.table_eh = table

        self._apply_soft_shadow(frame, blur=18.0, offset_y=5.0, color=QtGui.QColor(10, 16, 24, 90))
        parent_layout.addWidget(frame)

    def _export_planilha_mva(self) -> None:
        exportar_planilha_pdf(self.tree_mva, "Planilha MVA")

    def _export_planilha_eh(self) -> None:
        exportar_planilha_pdf(self.tree_eh, "Planilha EH")

    def _bind_actions(self) -> None:
        self.btn_cancel.clicked.connect(process_cancel)
        self.btn_select_pdf.clicked.connect(self._handle_pdf_button)
        self.btn_caixa.clicked.connect(self._handle_caixa_report)
        self.btn_spreadsheet.clicked.connect(self._handle_load_planilhas)
        self.btn_export.clicked.connect(lambda: self._export_dialog())
        self.btn_edit_table.clicked.connect(self._toggle_table_edit)
        self.btn_graphs.clicked.connect(self._toggle_graphs_view)
        self.btn_clear.clicked.connect(self._handle_clear_tables)
        self.btn_merge.clicked.connect(self._handle_merge_tables)
        self.btn_tag.clicked.connect(lambda: criar_etiquetas(self.tree_main))
        self.btn_tag.setEnabled(False)
        self.btn_settings.clicked.connect(self._open_caixa_settings)
        self.btn_automation_power.clicked.connect(self._toggle_automation_power)
        self.btn_automation_test.clicked.connect(self._schedule_automation_test_run)
        self.btn_eh_pending_print.clicked.connect(
            lambda: self._run_pending_print_jobs_for_company("EH", notify_user=True)
        )
        self.btn_eh_pending_morning.clicked.connect(lambda: self._run_pending_eh_scope("morning"))
        self.btn_eh_pending_afternoon.clicked.connect(lambda: self._run_pending_eh_scope("afternoon"))
        self.btn_mva_pending_print.clicked.connect(
            lambda: self._run_pending_print_jobs_for_company("MVA", notify_user=True)
        )
        self.btn_mva_pending_morning.clicked.connect(lambda: self._run_pending_mva_scope("morning"))
        self.btn_mva_pending_afternoon.clicked.connect(lambda: self._run_pending_mva_scope("afternoon"))

    def _open_caixa_settings(self) -> None:
        values = CaixaSettingsDialog(
            self,
            eh_special_enabled=self._eh_special_closing_enabled,
            mva_special_enabled=self._mva_special_scope_enabled,
        ).values()
        if values is None:
            return
        self._eh_special_closing_enabled, self._mva_special_scope_enabled = values

    def _setup_daily_automation_timer(self) -> None:
        self._automation_next_run, self._automation_next_scope = self._compute_next_automation_run()
        self._automation_timer = QtCore.QTimer(self)
        self._automation_timer.timeout.connect(self._on_automation_timer_tick)
        self._automation_timer.start(1000)
        self._refresh_automation_controls_ui()

    def _compute_next_automation_run(self, now: dt.datetime | None = None) -> tuple[dt.datetime | None, str | None]:
        now = now or dt.datetime.now()
        candidates: list[tuple[dt.datetime, str]] = []
        current_weekday = now.weekday()
        for scope_mode, target_time in self._automation_schedule.items():
            if current_weekday == 5 and scope_mode != "morning":
                continue
            if not target_time.isValid():
                continue
            target_hour = target_time.hour()
            target_minute = target_time.minute()
            if current_weekday == 5 and scope_mode == "morning":
                target_hour, target_minute = 13, 0
            target = now.replace(
                hour=target_hour,
                minute=target_minute,
                second=0,
                microsecond=0,
            )
            if now >= target:
                target += dt.timedelta(days=1)
            while target.weekday() == 6 or (target.weekday() == 5 and scope_mode != "morning"):
                target += dt.timedelta(days=1)
            candidates.append((target, scope_mode))
        if not candidates:
            return None, None
        candidates.sort(key=lambda item: item[0])
        return candidates[0]

    def _automation_target_date_br(self, scope_mode: str | None = None) -> str:
        target_date = QtCore.QDate.currentDate()
        if str(scope_mode or "").strip() == "afternoon":
            target_date = target_date.addDays(-1)
        return target_date.toString("dd/MM/yyyy")

    def _automation_time_text(self, scope_mode: str | None = None) -> str:
        if scope_mode:
            target_time = self._automation_schedule.get(scope_mode)
            if scope_mode == "morning" and QtCore.QDate.currentDate().dayOfWeek() == 6:
                return "13:00"
            return target_time.toString("HH:mm") if target_time and target_time.isValid() else "--:--"
        partes = []
        for current_scope in ("afternoon", "morning"):
            partes.append(f"{self._scope_label_text(current_scope)} {self._automation_time_text(current_scope)}")
        return " / ".join(partes)

    def _scope_label_text(self, scope_mode: str | None) -> str:
        return "manhã" if str(scope_mode or "").strip() == "morning" else "tarde"

    def _normalize_pending_print_company(self, company: str | None) -> str | None:
        company_text = str(company or "").strip().upper()
        if company_text in {"EH", "MVA"}:
            return company_text
        return None

    def _load_pending_print_jobs(self) -> None:
        self._pending_print_jobs = {"EH": [], "MVA": []}
        path = _pending_print_jobs_path()
        if not path.exists():
            return
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return

        for raw_job in list((payload or {}).get("jobs") or []):
            if not isinstance(raw_job, dict):
                continue
            company = self._normalize_pending_print_company(raw_job.get("company"))
            title = str(raw_job.get("title") or "").strip()
            html = str(raw_job.get("html") or "")
            if not company or not title or not html:
                continue
            created_at = _parse_pending_print_datetime(raw_job.get("created_at")) or dt.datetime.now()
            retry_at = _parse_pending_print_datetime(raw_job.get("retry_at")) or _next_pending_print_retry_dt(created_at)
            self._pending_print_jobs[company].append(
                {
                    "id": str(raw_job.get("id") or f"{company}-{time.time_ns()}").strip(),
                    "company": company,
                    "title": title,
                    "html": html,
                    "created_at": created_at.replace(microsecond=0).isoformat(),
                    "retry_at": retry_at.replace(microsecond=0).isoformat(),
                    "last_error": str(raw_job.get("last_error") or "").strip(),
                }
            )

        for company in ("EH", "MVA"):
            self._pending_print_jobs[company].sort(
                key=lambda item: (
                    str(item.get("retry_at") or ""),
                    str(item.get("created_at") or ""),
                    str(item.get("title") or ""),
                )
            )

    def _save_pending_print_jobs(self) -> None:
        path = _pending_print_jobs_path()
        jobs_to_save: list[dict[str, str]] = []
        for company in ("EH", "MVA"):
            for raw_job in self._pending_print_jobs.get(company) or []:
                title = str(raw_job.get("title") or "").strip()
                html = str(raw_job.get("html") or "")
                if not title or not html:
                    continue
                created_at = _parse_pending_print_datetime(raw_job.get("created_at")) or dt.datetime.now()
                retry_at = _parse_pending_print_datetime(raw_job.get("retry_at")) or _next_pending_print_retry_dt(created_at)
                jobs_to_save.append(
                    {
                        "id": str(raw_job.get("id") or f"{company}-{time.time_ns()}").strip(),
                        "company": company,
                        "title": title,
                        "html": html,
                        "created_at": created_at.replace(microsecond=0).isoformat(),
                        "retry_at": retry_at.replace(microsecond=0).isoformat(),
                        "last_error": str(raw_job.get("last_error") or "").strip(),
                    }
                )

        if not jobs_to_save:
            try:
                path.unlink()
            except FileNotFoundError:
                pass
            except Exception:
                pass
            return

        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps({"jobs": jobs_to_save}, ensure_ascii=False, indent=2),
                encoding="utf-8",
            )
        except Exception:
            pass

    def _pending_print_jobs_for_company(self, company: str | None) -> list[dict[str, str]]:
        company_key = self._normalize_pending_print_company(company)
        if not company_key:
            return []
        return [dict(job) for job in self._pending_print_jobs.get(company_key) or []]

    def _format_pending_print_retry_text(self, jobs: list[dict[str, str]]) -> str:
        retry_targets = [
            retry_at
            for retry_at in (
                _parse_pending_print_datetime(job.get("retry_at"))
                for job in jobs
            )
            if retry_at is not None
        ]
        if not retry_targets:
            return "08:00 do dia seguinte"
        retry_at = min(retry_targets)
        return retry_at.strftime("%d/%m/%Y %H:%M")

    def _prepare_pending_print_jobs(
        self,
        jobs: list[dict[str, str]],
        *,
        retry_at: dt.datetime,
        error_message: str | None,
        company_override: str | None = None,
    ) -> list[dict[str, str]]:
        prepared: list[dict[str, str]] = []
        retry_at_text = retry_at.replace(microsecond=0).isoformat()
        now_text = dt.datetime.now().replace(microsecond=0).isoformat()
        for index, raw_job in enumerate(jobs):
            company = company_override or self._normalize_pending_print_company(raw_job.get("company"))
            title = str(raw_job.get("title") or "").strip()
            html = str(raw_job.get("html") or "")
            if not company or not title or not html:
                continue
            prepared.append(
                {
                    "id": str(raw_job.get("id") or f"{company}-{time.time_ns()}-{index}").strip(),
                    "company": company,
                    "title": title,
                    "html": html,
                    "created_at": str(raw_job.get("created_at") or now_text).strip() or now_text,
                    "retry_at": retry_at_text,
                    "last_error": str(error_message or raw_job.get("last_error") or "").strip(),
                }
            )
        return prepared

    def _replace_pending_print_jobs(
        self,
        company: str,
        jobs: list[dict[str, str]],
        *,
        error_message: str | None = None,
        now: dt.datetime | None = None,
    ) -> None:
        company_key = self._normalize_pending_print_company(company)
        if not company_key:
            return
        now = now or dt.datetime.now()
        retry_at = _next_pending_print_retry_dt(now)
        self._pending_print_jobs[company_key] = self._prepare_pending_print_jobs(
            jobs,
            retry_at=retry_at,
            error_message=error_message,
            company_override=company_key,
        )
        self._save_pending_print_jobs()

    def _merge_pending_print_jobs(
        self,
        jobs: list[dict[str, str]],
        *,
        error_message: str | None = None,
        now: dt.datetime | None = None,
    ) -> str:
        now = now or dt.datetime.now()
        retry_at = _next_pending_print_retry_dt(now)
        retry_text = retry_at.strftime("%d/%m/%Y %H:%M")
        grouped_jobs: dict[str, list[dict[str, str]]] = {"EH": [], "MVA": []}
        for job in self._prepare_pending_print_jobs(
            jobs,
            retry_at=retry_at,
            error_message=error_message,
        ):
            grouped_jobs[job["company"]].append(job)

        merged_companies: list[str] = []
        for company, company_jobs in grouped_jobs.items():
            if not company_jobs:
                continue
            existing_by_id = {
                str(item.get("id") or "").strip(): dict(item)
                for item in self._pending_print_jobs.get(company) or []
                if str(item.get("id") or "").strip()
            }
            for company_job in company_jobs:
                existing_by_id[company_job["id"]] = company_job
            merged_jobs = list(existing_by_id.values())
            merged_jobs.sort(
                key=lambda item: (
                    str(item.get("retry_at") or ""),
                    str(item.get("created_at") or ""),
                    str(item.get("title") or ""),
                )
            )
            self._pending_print_jobs[company] = merged_jobs
            merged_companies.append(f"{company} ({len(company_jobs)})")

        self._save_pending_print_jobs()
        if not merged_companies:
            return ""
        return (
            "Impressao pendente salva para "
            + ", ".join(merged_companies)
            + f". Nova tentativa automatica em {retry_text} se a automacao estiver ligada; "
            + "tambem pode ser disparada pelos botoes pendentes."
        )

    def _format_pending_print_button_text(self, company: str) -> str:
        count = len(self._pending_print_jobs_for_company(company))
        base_label = "EH impressao pendente" if company == "EH" else "MVA impressao pendente"
        return f"{base_label} ({count})" if count > 1 else base_label

    def _format_countdown(self, total_seconds: int) -> str:
        total_seconds = max(0, int(total_seconds))
        hours, remainder = divmod(total_seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    def _refresh_automation_controls_ui(self) -> None:
        play_icon = self.style().standardIcon(QtWidgets.QStyle.SP_MediaPlay)
        stop_icon = self.style().standardIcon(QtWidgets.QStyle.SP_MediaStop)
        if self._automation_enabled:
            next_run = self._automation_next_run
            next_scope = self._automation_next_scope or "morning"
            if next_run is None:
                next_run, next_scope = self._compute_next_automation_run()
            remaining = self._format_countdown(int((next_run - dt.datetime.now()).total_seconds())) if next_run else "--:--:--"
            tooltip = (
                f"Automacao ativa para manhã {self._automation_time_text('morning')} e tarde {self._automation_time_text('afternoon')}.\n"
                f"Próxima execução: {self._scope_label_text(next_scope)} em {next_run.strftime('%d/%m/%Y %H:%M:%S') if next_run else '--'} (em {remaining}).\n"
                "Clique para pausar."
            )
            self.btn_automation_power.setIcon(stop_icon)
            self.btn_automation_power.setToolTip(corrigir_texto(tooltip))
        else:
            tooltip = (
                f"Automacao pausada. Horarios fixos: manhã {self._automation_time_text('morning')} e tarde {self._automation_time_text('afternoon')}.\n"
                "Clique para ligar novamente."
            )
            self.btn_automation_power.setIcon(play_icon)
            self.btn_automation_power.setToolTip(corrigir_texto(tooltip))
        self.btn_automation_power.setEnabled(not self._automation_running)

        if self._automation_test_run_at:
            test_remaining = self._format_countdown(
                int((self._automation_test_run_at - dt.datetime.now()).total_seconds())
            )
            self.btn_automation_test.setText(f"Teste em {test_remaining}")
            self.btn_automation_test.setToolTip(
                corrigir_texto(
                    f"Teste manual de {self._scope_label_text(self._automation_test_scope)} agendado para iniciar em {test_remaining}."
                )
            )
        else:
            self.btn_automation_test.setText("Teste automacao (5s)")
            self.btn_automation_test.setToolTip(
                corrigir_texto("Dispara uma simulacao de manha ou tarde em 5 segundos.")
            )

        pending_eh_print = len(self._pending_print_jobs_for_company("EH"))
        pending_mva_print = len(self._pending_print_jobs_for_company("MVA"))
        self.btn_eh_pending_print.setText(self._format_pending_print_button_text("EH"))
        self.btn_eh_pending_print.setVisible(pending_eh_print > 0)
        self.btn_eh_pending_print.setEnabled(pending_eh_print > 0 and not self._automation_running)
        if pending_eh_print:
            self.btn_eh_pending_print.setToolTip(
                corrigir_texto(
                    "Reenvia para impressao o fechamento da EH ja montado que ficou pendente."
                )
            )

        pending_eh_morning = bool(self._eh_pending_runs.get("morning"))
        pending_eh_afternoon = bool(self._eh_pending_runs.get("afternoon"))
        self.btn_eh_pending_morning.setVisible(pending_eh_morning)
        self.btn_eh_pending_morning.setEnabled(pending_eh_morning and not self._automation_running)
        self.btn_eh_pending_afternoon.setVisible(pending_eh_afternoon)
        self.btn_eh_pending_afternoon.setEnabled(pending_eh_afternoon and not self._automation_running)

        self.btn_mva_pending_print.setText(self._format_pending_print_button_text("MVA"))
        self.btn_mva_pending_print.setVisible(pending_mva_print > 0)
        self.btn_mva_pending_print.setEnabled(pending_mva_print > 0 and not self._automation_running)
        if pending_mva_print:
            self.btn_mva_pending_print.setToolTip(
                corrigir_texto(
                    "Reenvia para impressao o fechamento da MVA ja montado que ficou pendente."
                )
            )

        pending_morning = bool(self._mva_pending_runs.get("morning"))
        pending_afternoon = bool(self._mva_pending_runs.get("afternoon"))
        self.btn_mva_pending_morning.setVisible(pending_morning)
        self.btn_mva_pending_morning.setEnabled(pending_morning and not self._automation_running)
        self.btn_mva_pending_afternoon.setVisible(pending_afternoon)
        self.btn_mva_pending_afternoon.setEnabled(pending_afternoon and not self._automation_running)
        self._refresh_dashboard_status_cards()

    def _choose_automation_scope_for_test(self) -> str | None:
        box = QtWidgets.QMessageBox(self)
        box.setWindowTitle("Teste da automacao")
        box.setText("Qual fechamento automático deseja simular?")
        btn_morning = box.addButton("Manhã", QtWidgets.QMessageBox.AcceptRole)
        btn_afternoon = box.addButton("Tarde", QtWidgets.QMessageBox.ActionRole)
        btn_cancel = box.addButton("Cancelar", QtWidgets.QMessageBox.RejectRole)
        _center_message_box_buttons(box)
        box.exec()
        clicked = box.clickedButton()
        if clicked == btn_morning:
            return "morning"
        if clicked == btn_afternoon:
            return "afternoon"
        if clicked == btn_cancel:
            return None
        return None

    def _toggle_automation_power(self) -> None:
        if self._automation_running:
            return
        if self._automation_enabled:
            self._automation_enabled = False
            self._automation_next_run = None
            self._automation_next_scope = None
            self._automation_last_status = "Automacao pausada pelo usuario."
            self._refresh_automation_controls_ui()
            return

        self._automation_enabled = True
        self._automation_next_run, self._automation_next_scope = self._compute_next_automation_run()
        self._automation_last_status = (
            "Automacao retomada para tarde do dia anterior às 08:00 e manhã do dia atual às 13:30."
        )
        self._refresh_automation_controls_ui()

    def _schedule_automation_test_run(self) -> None:
        if self._automation_running:
            return
        scope_mode = self._choose_automation_scope_for_test()
        if not scope_mode:
            return
        self._automation_test_scope = scope_mode
        self._automation_test_run_at = dt.datetime.now() + dt.timedelta(seconds=5)
        self._automation_last_status = (
            f"Teste de automacao da {self._scope_label_text(scope_mode)} armado para {self._automation_target_date_br(scope_mode)}."
        )
        self._refresh_automation_controls_ui()

    def _on_automation_timer_tick(self) -> None:
        now = dt.datetime.now()
        if (
            self._automation_test_run_at is not None
            and now >= self._automation_test_run_at
            and not self._automation_running
        ):
            self._automation_test_run_at = None
            self._run_scheduled_automation(
                f"teste manual ({self._scope_label_text(self._automation_test_scope)})",
                notify_user=True,
                scope_mode=self._automation_test_scope,
            )
            return

        if (
            self._automation_enabled
            and not self._automation_running
            and self._retry_due_pending_print_jobs(now)
        ):
            return

        if (
            self._automation_enabled
            and self._automation_next_run is not None
            and now >= self._automation_next_run
            and not self._automation_running
        ):
            current_scope = self._automation_next_scope or "morning"
            self._automation_next_run, self._automation_next_scope = self._compute_next_automation_run(now + dt.timedelta(seconds=1))
            self._run_scheduled_automation(
                f"agenda {self._automation_time_text(current_scope)}",
                notify_user=False,
                scope_mode=current_scope,
            )
            return

        self._refresh_automation_controls_ui()

    def _handle_pdf_button(self) -> None:
        if not self._confirm_discard_edits("importar PDF"):
            return
        self._reset_edit_state()
        from global_vars import list_results
        if list_results:
            self._handle_add_more()
            return
        self._select_pdf_flow()

    def _select_pdf_flow(self) -> None:
        if not self._confirm_discard_edits("importar PDF"):
            return
        self._reset_edit_state()
        path = filedialog.askopenfilename(filetypes=[("Arquivos PDF", "*.pdf")])
        if not path:
            return
        origem = self._infer_origem_from_filename(path)
        if not origem:
            dlg = SourceDialog(self)
            origem = dlg.choice()
        if not origem:
            return
        source_pdf_async(
            self.tree_main,
            self.progress_var,
            self.progress_bar_adapter,
            self.root_adapter,
            self.label_files_var,
            QtButtonAdapter(self.btn_cancel),
            path,
            origem,
        )

    def _handle_add_more(self) -> None:
        if not self._confirm_discard_edits("adicionar PDF"):
            return
        adicionar_pdf(
            self.tree_main,
            self.progress_var,
            self.progress_bar_adapter,
            self.root_adapter,
            self.label_files_var,
        )

    def _run_loading_worker(
        self,
        title: str,
        message: str,
        worker: Callable[[Callable[[str], None], dict], None],
        *,
        cancel_event: threading.Event | None = None,
    ) -> tuple[dict, bool]:
        status_queue: queue.Queue[str] = queue.Queue()
        result: dict = {}

        def push_status(raw_message: str) -> None:
            texto = str(raw_message or "").strip()
            if texto:
                status_queue.put(texto)

        def wrapped_worker() -> None:
            try:
                worker(push_status, result)
            except Exception as exc:
                if str(exc).strip() == "__cancelled__":
                    result["cancelled"] = True
                else:
                    result["error"] = _format_exception_message(exc, "Falha ao processar a etapa em segundo plano.")

        dialog = LoadingStatusDialog(self, title, message)
        if cancel_event is not None:
            dialog.cancel_requested.connect(cancel_event.set)

        def drain_status_queue(limit: int = 80) -> None:
            drained = 0
            while drained < limit:
                try:
                    dialog.set_status(status_queue.get_nowait())
                except queue.Empty:
                    break
                drained += 1

        thread = threading.Thread(target=wrapped_worker, daemon=True)
        thread.start()

        timer = QtCore.QTimer(dialog)
        timer.setInterval(75)

        def poll_worker() -> None:
            drain_status_queue()
            if dialog.was_cancelled() and cancel_event is not None and not cancel_event.is_set():
                cancel_event.set()
            if not thread.is_alive():
                timer.stop()
                drain_status_queue(limit=1000)
                dialog.close_gracefully()

        timer.timeout.connect(poll_worker)
        timer.start()
        dialog.show()
        dialog.raise_()
        dialog.activateWindow()
        dialog.exec()
        thread.join(timeout=0)
        drain_status_queue(limit=1000)
        return result, bool(result.get("cancelled") or dialog.was_cancelled())

    def _load_eh_caixa_reports_with_loading(
        self,
        data_br: str,
        *,
        force_refresh_payments: bool = False,
        fechamento_data_inicio_br: str | None = None,
        fechamento_data_fim_br: str | None = None,
        filtrar_fechamento_por_data_venda: bool = False,
        scope_mode: str | None = None,
    ) -> tuple[dict | None, dict | None, dict | None, str | None]:
        cancel_loading = threading.Event()

        def worker(push_status: Callable[[str], None], result: dict) -> None:
            relatorio, relatorio_fechamento, relatorio_pix = gerar_relatorios_caixa_eh_zweb(
                data_br,
                on_status=push_status,
                cancel_event=cancel_loading,
                force_refresh_payments=force_refresh_payments,
                fechamento_data_inicio_br=fechamento_data_inicio_br,
                fechamento_data_fim_br=fechamento_data_fim_br,
                filtrar_fechamento_por_data_venda=filtrar_fechamento_por_data_venda,
                scope_mode=scope_mode,
            )
            result["relatorio"] = relatorio
            result["relatorio_fechamento"] = relatorio_fechamento
            result["relatorio_pix"] = relatorio_pix

        result, was_cancelled = self._run_loading_worker(
            "Caixa EH",
            "Acessando Zweb...",
            worker,
            cancel_event=cancel_loading,
        )

        if was_cancelled:
            return None, None, None, "__cancelled__"
        if result.get("error"):
            return None, None, None, str(result.get("error")).strip() or "Falha ao gerar os relatórios da EH no Zweb."
        return result.get("relatorio"), result.get("relatorio_fechamento"), result.get("relatorio_pix"), None

    def _load_mva_reports_with_loading(
        self,
        path_davs: str,
        path_orcamentos: str,
        path_cupons: str,
        *,
        force_refresh_payments: bool = False,
        allow_cielo_fallback: bool = True,
        scope_mode: str | None = None,
        filter_opening_date_br: str | None = None,
    ) -> tuple[dict | None, dict | None, dict | None, str | None]:
        cancel_loading = threading.Event()

        def _check_cancelled() -> None:
            if cancel_loading.is_set():
                raise RuntimeError("__cancelled__")

        def worker(push_status: Callable[[str], None], result: dict) -> None:
            push_status("Lendo DAV MVA...")
            result["relatorio_davs"] = analisar_pdf_caixa(path_davs)
            _check_cancelled()
            if path_orcamentos:
                push_status("Lendo Orcamento...")
                result["relatorio_orcamentos"] = analisar_pdf_caixa(path_orcamentos)
            else:
                push_status("Orcamento ignorado; seguindo apenas com DAV MVA...")
                periodo_dav = (result.get("relatorio_davs") or {}).get("periodo")
                result["relatorio_orcamentos"] = criar_relatorio_orcamentos_mva_vazio(periodo_dav)
            _check_cancelled()
            if path_orcamentos and result["relatorio_davs"].get("periodo") and result["relatorio_orcamentos"].get("periodo"):
                if result["relatorio_davs"].get("periodo") != result["relatorio_orcamentos"].get("periodo"):
                    raise RuntimeError(
                        "A Exportacao de dados e o relatorio de Orcamento da MVA precisam ser do mesmo periodo."
                    )

            result["relatorio_cupons"] = None
            if path_cupons:
                def _read_mva_closing(*, auto_download_missing: bool) -> dict:
                    relatorio_lido = analisar_pdf_fechamento_caixa_mva_clipp(
                        path_cupons,
                        auto_download_missing=auto_download_missing,
                        force_refresh_payments=force_refresh_payments,
                        allow_cielo_fallback=allow_cielo_fallback,
                        scope_mode=scope_mode,
                        filter_opening_date_br=filter_opening_date_br,
                        on_status=push_status if auto_download_missing else None,
                        cancel_event=cancel_loading,
                    )
                    avisos_lidos = list(relatorio_lido.get("avisos_usuario") or [])
                    if relatorio_lido.get("quantidade_nfce", 0) <= 0:
                        relatorio_lido = analisar_pdf_resumo_nfce(path_cupons)
                        if avisos_lidos:
                            relatorio_lido["avisos_usuario"] = list(
                                dict.fromkeys(
                                    list(relatorio_lido.get("avisos_usuario") or [])
                                    + avisos_lidos
                                )
                            )
                    return relatorio_lido

                push_status("Lendo Fechamento de Caixa...")
                relatorio_cupons_previo = _read_mva_closing(auto_download_missing=False)
                _check_cancelled()
                periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
                    result["relatorio_davs"],
                    relatorio_cupons_previo,
                    titulo_secundario="relatorio de Cupons",
                )
                if not periodo_ok:
                    raise RuntimeError(periodo_msg)

                push_status("Validando pagamentos da MVA...")
                relatorio_cupons = _read_mva_closing(auto_download_missing=True)
                _check_cancelled()
                periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
                    result["relatorio_davs"],
                    relatorio_cupons,
                    titulo_secundario="relatorio de Cupons",
                )
                if not periodo_ok:
                    raise RuntimeError(periodo_msg)
                result["relatorio_cupons"] = relatorio_cupons

        result, was_cancelled = self._run_loading_worker(
            "Caixa MVA",
            "Processando arquivos da MVA...",
            worker,
            cancel_event=cancel_loading,
        )

        if was_cancelled:
            return None, None, None, "__cancelled__"
        if result.get("error"):
            return None, None, None, str(result.get("error")).strip() or "Falha ao processar os arquivos da MVA."
        return result.get("relatorio_davs"), result.get("relatorio_orcamentos"), result.get("relatorio_cupons"), None

    def _auto_find_mva_caixa_files(self) -> dict[str, str]:
        terms_by_key = {
            "davs": ["dav mva", "dav"],
            "orcamentos": ["orcamento", "orçamento"],
            "cupons": ["fechamento de caixa"],
        }
        base_dirs: list[str] = []
        for raw in [_active_report_dir()]:
            if raw and os.path.isdir(raw) and raw not in base_dirs:
                base_dirs.append(raw)

        found: dict[str, str] = {}
        for base_dir in base_dirs:
            try:
                pdfs = [
                    os.path.join(base_dir, name)
                    for name in os.listdir(base_dir)
                    if name.lower().endswith(".pdf")
                ]
            except OSError:
                continue
            pdfs.sort(key=lambda item: os.path.getmtime(item), reverse=True)
            for key, terms in terms_by_key.items():
                if key in found:
                    continue
                for path in pdfs:
                    nome = corrigir_texto(os.path.basename(path)).casefold()
                    if any(term in nome for term in terms):
                        found[key] = path
                        break
        return found

    def _choose_daily_or_afternoon_scope(self, company_label: str, relatorio_fechamento: dict | None) -> str | None:
        return CaixaScopeDialog(
            self,
            company_label=company_label,
        ).choice()

    def _resolve_manual_closing_scope(self, relatorio_fechamento: dict | None, company_label: str) -> str | None:
        info = describe_closing_scope(relatorio_fechamento)
        if info.get("has_full_day"):
            return self._choose_daily_or_afternoon_scope(company_label, relatorio_fechamento)
        if info.get("has_morning_only"):
            return "morning"
        if info.get("has_afternoon_only"):
            return "afternoon"
        return "daily"

    def _apply_scope_to_reports(
        self,
        relatorio: dict,
        relatorio_fechamento: dict | None,
        relatorio_pix: dict | None = None,
        *,
        scope_mode: str | None,
    ) -> tuple[dict, dict | None, dict | None]:
        if not relatorio_fechamento or not scope_mode:
            return relatorio, relatorio_fechamento, relatorio_pix
        return aplicar_escopo_relatorio_caixa(
            relatorio,
            relatorio_fechamento,
            relatorio_pix,
            scope_mode=scope_mode,
        )

    def _scope_unavailable_message(self, scope_mode: str | None, company_label: str) -> str | None:
        scope_norm = str(scope_mode or "").strip()
        if scope_norm == "morning":
            return f"O fechamento completo da {company_label} ainda não está disponível para separar a manhã."
        if scope_norm == "afternoon":
            return f"O fechamento completo da {company_label} ainda não está disponível para separar a tarde."
        return None

    def _closing_scope_available(self, scope_mode: str | None, relatorio_fechamento: dict | None) -> bool:
        scope_norm = str(scope_mode or "").strip()
        if scope_norm in {"", "daily"}:
            return True
        scope_info = describe_closing_scope(relatorio_fechamento)
        if scope_norm == "morning":
            return bool(scope_info.get("has_full_day") or scope_info.get("has_morning_only"))
        if scope_norm == "afternoon":
            return bool(scope_info.get("has_full_day") or scope_info.get("has_afternoon_only"))
        return True

    def _mark_mva_pending_scope(self, scope_mode: str, data_br: str, message: str) -> None:
        self._mva_pending_runs[scope_mode] = {
            "data_br": data_br,
            "message": message,
            "scope_mode": scope_mode,
        }

    def _clear_mva_pending_scope(self, scope_mode: str) -> None:
        self._mva_pending_runs[scope_mode] = {}

    def _mark_eh_pending_scope(self, scope_mode: str, data_br: str, message: str) -> None:
        self._eh_pending_runs[scope_mode] = {
            "data_br": data_br,
            "message": message,
            "scope_mode": scope_mode,
        }

    def _clear_eh_pending_scope(self, scope_mode: str) -> None:
        self._eh_pending_runs[scope_mode] = {}

    def _prefetch_mva_payments(self, data_br: str) -> list[str]:
        avisos: list[str] = []
        try:
            baixados = baixar_relatorios_caixa_eh_azulzinha(
                data_br,
                company="MVA",
                need_pix=True,
                need_cartoes=True,
            )
            avisos.extend(list(baixados.get("avisos") or []))
        except Exception as exc:
            avisos.append(f"Não foi possível adiantar os pagamentos da Azulzinha da MVA: {exc}")
        return avisos

    def _generate_mva_reports_for_automation(
        self,
        data_br: str,
        *,
        scope_mode: str,
        force_refresh_payments: bool = False,
    ) -> tuple[dict | None, dict | None, list[str], str | None]:
        auto_files = self._auto_find_mva_caixa_files()
        missing: list[str] = []
        path_davs = auto_files.get("davs", "")
        path_orcamentos = auto_files.get("orcamentos", "")
        path_cupons = auto_files.get("cupons", "")

        if not path_davs:
            missing.append("DAV MVA")
        if not path_cupons:
            missing.append("Fechamento de Caixa")
        loaded_from_clipp = False
        if missing and database_is_configured():
            try:
                sale_date = dt.datetime.strptime(data_br, "%d/%m/%Y").date()
                clipp_reader = ClippMvaReader.from_environment()
                relatorio_davs = clipp_reader.build_dav_report(sale_date)
                relatorio_orcamentos = None
                relatorio_cupons = clipp_reader.build_closing_report(sale_date)
                loaded_from_clipp = True
            except (ValueError, ClippMvaConnectionError) as exc:
                message = f"Não foi possível ler os dados da MVA diretamente do Clipp: {exc}"
                self._mark_mva_pending_scope(scope_mode, data_br, message)
                return None, None, [], message

        if missing and not loaded_from_clipp:
            avisos = self._prefetch_mva_payments(data_br)
            self._mark_mva_pending_scope(
                scope_mode,
                data_br,
                f"Arquivos da MVA ainda ausentes para a {self._scope_label_text(scope_mode)}: {', '.join(missing)}.",
            )
            return None, None, avisos, f"Arquivos da MVA não encontrados automaticamente: {', '.join(missing)}."

        if not loaded_from_clipp:
            relatorio_davs, relatorio_orcamentos, relatorio_cupons, mva_msg = self._load_mva_reports_with_loading(
                path_davs,
                path_orcamentos,
                path_cupons,
                force_refresh_payments=force_refresh_payments,
                scope_mode=scope_mode,
                filter_opening_date_br=data_br if self._mva_special_scope_enabled else None,
            )
            if mva_msg:
                self._mark_mva_pending_scope(scope_mode, data_br, mva_msg)
                return None, None, [], mva_msg

        davs_ok, davs_msg = validar_arquivo_caixa_mva(relatorio_davs, "exportacao_dados_mva")
        if not davs_ok:
            return None, None, [], davs_msg

        if path_orcamentos:
            orc_ok, orc_msg = validar_arquivo_caixa_mva(relatorio_orcamentos, "orcamentos_mva")
            if not orc_ok:
                return None, None, [], orc_msg

        if path_orcamentos and relatorio_davs.get("periodo") and relatorio_orcamentos.get("periodo"):
            if relatorio_davs.get("periodo") != relatorio_orcamentos.get("periodo"):
                return None, None, [], (
                    "A Exportação de dados e o relatório de Orçamento da MVA precisam ser do mesmo período."
                )

        relatorios_mva = [relatorio_davs]
        if path_orcamentos and relatorio_orcamentos:
            relatorios_mva.append(relatorio_orcamentos)
        relatorio = combinar_relatorios_caixa_mva(relatorios_mva)
        if relatorio.get("pedidos_total", 0) <= 0:
            return None, None, [], "Nenhum pedido foi encontrado nos arquivos da MVA."

        caixa_ok, caixa_msg = validar_relatorio_pedidos_importados(
            relatorio,
            modelo_esperado="MVA",
        )
        if not caixa_ok:
            return None, None, [], caixa_msg

        resumo_ok, resumo_msg = validar_relatorio_resumo_nfce(
            relatorio_cupons,
            modelo_esperado="MVA",
        )
        if not resumo_ok:
            return None, None, [], resumo_msg
        if relatorio_cupons.get("quantidade_nfce", 0) <= 0:
            return None, None, [], "Nenhum cupom foi encontrado no Fechamento de Caixa da MVA."
        if not self._closing_scope_available(scope_mode, relatorio_cupons):
            aviso = self._scope_unavailable_message(scope_mode, "MVA") or "O fechamento da MVA ainda não está disponível para o escopo solicitado."
            self._mark_mva_pending_scope(scope_mode, data_br, aviso)
            return None, None, [], aviso

        periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
            relatorio,
            relatorio_cupons,
            titulo_secundario="relatorio de Cupons",
        )
        if not periodo_ok:
            return None, None, [], periodo_msg

        relatorio, relatorio_cupons, _ = self._apply_scope_to_reports(
            relatorio,
            relatorio_cupons,
            None,
            scope_mode=scope_mode,
        )
        fechamento = comparar_caixa_resumo_nfce(relatorio, relatorio_cupons)
        self._clear_mva_pending_scope(scope_mode)
        avisos_usuario = list(
            dict.fromkeys(
                list((relatorio_cupons or {}).get("avisos_usuario") or [])
                + list((fechamento or {}).get("avisos_usuario") or [])
            )
        )
        blocking_warnings = [aviso for aviso in avisos_usuario if self._warning_blocks_mva_automation_print(aviso)]
        if blocking_warnings or self._mva_report_has_minhas_notas_alert(fechamento):
            motivo = corrigir_texto(blocking_warnings[0]) if blocking_warnings else (
                "A validação fiscal dos cupons da MVA no Minhas Notas ficou indisponível nesta análise."
            )
            return (
                None,
                None,
                [],
                (
                    "A impressão automática da MVA foi bloqueada porque a validação no Minhas Notas "
                    "não foi concluída corretamente.\n"
                    f"Motivo: {motivo}\n"
                    "Sem o Minhas Notas, a conferência fiscal da MVA não será considerada válida para impressão."
                ),
            )
        return relatorio, fechamento, avisos_usuario, None

    def _generate_eh_reports_for_automation(
        self,
        data_br: str,
        *,
        scope_mode: str,
    ) -> tuple[dict | None, dict | None, dict | None, list[str], str | None]:
        relatorio, relatorio_nfce, relatorio_pix, eh_msg = self._load_eh_caixa_reports_with_loading(
            data_br,
            force_refresh_payments=False,
            scope_mode=scope_mode,
        )
        if eh_msg == "__cancelled__":
            return None, None, None, [], "A automacao da EH foi cancelada."
        if eh_msg:
            return None, None, None, [], eh_msg

        caixa_ok, caixa_msg = validar_relatorio_pedidos_importados(
            relatorio,
            modelo_esperado="EH",
        )
        if not caixa_ok:
            return None, None, None, [], caixa_msg
        if relatorio.get("pedidos_total", 0) <= 0:
            return None, None, None, [], "Nenhum pedido foi encontrado no caixa da EH."

        fechamento = None
        avisos_usuario: list[str] = []

        if relatorio_nfce:
            resumo_ok, resumo_msg = validar_relatorio_resumo_nfce(
                relatorio_nfce,
                modelo_esperado="EH",
            )
            if not resumo_ok:
                return None, None, None, [], resumo_msg
            if relatorio_nfce.get("quantidade_nfce", 0) <= 0:
                return None, None, None, [], "Nenhuma NFC-e foi encontrada no Fechamento de caixa do Zweb."
            if not self._closing_scope_available(scope_mode, relatorio_nfce):
                return None, None, None, [], (
                    self._scope_unavailable_message(scope_mode, "EH")
                    or "O fechamento da EH ainda não está disponível para o escopo solicitado."
                )

            periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
                relatorio,
                relatorio_nfce,
                titulo_secundario="Fechamento de caixa",
            )
            if not periodo_ok:
                return None, None, None, [], periodo_msg

            relatorio, relatorio_nfce, relatorio_pix = self._apply_scope_to_reports(
                relatorio,
                relatorio_nfce,
                relatorio_pix,
                scope_mode=scope_mode,
            )
            fechamento = comparar_caixa_resumo_nfce(relatorio, relatorio_nfce)
            avisos_usuario = list(
                dict.fromkeys(
                    list(relatorio_nfce.get("avisos_usuario") or [])
                    + list((fechamento or {}).get("avisos_usuario") or [])
                    + list((relatorio_pix or {}).get("avisos_usuario") or [])
                )
            )
            blocking_warnings = [aviso for aviso in avisos_usuario if self._warning_blocks_eh_automation_print(aviso)]
            if blocking_warnings or self._eh_report_uses_financeiro_zweb(fechamento):
                motivo = corrigir_texto(blocking_warnings[0]) if blocking_warnings else (
                    "A comparação caiu em Financeiro > Movimentações do Zweb."
                )
                self._mark_eh_pending_scope(scope_mode, data_br, motivo)
                return (
                    None,
                    None,
                    None,
                    [],
                    (
                        "A impressão automática da EH foi bloqueada porque os pagamentos da Caixa/Azulzinha "
                        "não foram validados corretamente.\n"
                        f"Motivo: {motivo}\n"
                        "O Financeiro do Zweb não será considerado válido para essa comparação."
                    ),
                )
        else:
            avisos_usuario.append(
                "O Fechamento de caixa do Zweb não ficou disponível; a EH será impressa sem a aba de fechamento."
            )

        periodo_pix = (relatorio_nfce or {}).get("periodo") or relatorio.get("periodo")
        if relatorio_pix is None and periodo_pix:
            relatorio_pix = {
                "arquivo": "",
                "periodo": periodo_pix,
                "quantidade_autorizados": 0,
                "total_autorizado": 0.0,
                "itens_autorizados": [],
                "mensagem": "Nenhum pagamento digital de NFC-e foi encontrado em Financeiro > Movimentacoes para este dia.",
            }
        elif relatorio_pix is None:
            relatorio_pix = {
                "arquivo": "",
                "periodo": None,
                "quantidade_autorizados": 0,
                "total_autorizado": 0.0,
                "itens_autorizados": [],
                "mensagem": "O período do caixa não foi identificado; não foi possível consultar os pagamentos digitais do Zweb.",
            }

        self._clear_eh_pending_scope(scope_mode)
        return relatorio, fechamento, relatorio_pix, avisos_usuario, None

    def _collect_automation_print_jobs(
        self,
        origem: str,
        relatorio: dict,
        fechamento: dict | None = None,
        relatorio_pix: dict | None = None,
    ) -> list[dict[str, str]]:
        dialog = CaixaReportDialog(self, relatorio, fechamento, relatorio_pix)
        try:
            company = self._normalize_pending_print_company(origem) or "EH"
            created_at = dt.datetime.now().replace(microsecond=0).isoformat()
            job_seed = time.time_ns()
            jobs: list[dict[str, str]] = []
            for index, (titulo, html) in enumerate(dialog.build_automation_bundle_jobs()):
                jobs.append(
                    {
                        "id": f"{company}-{job_seed}-{index}",
                        "company": company,
                        "title": f"{company}: {titulo}",
                        "html": html,
                        "created_at": created_at,
                        "retry_at": "",
                        "last_error": "",
                    }
                )
            return jobs
        finally:
            dialog.deleteLater()

    def _format_automation_section(self, title: str, lines: list[str]) -> str:
        cleaned_lines = [
            corrigir_texto(corrigir_estrutura_texto(str(line or "").strip()))
            for line in lines
            if str(line or "").strip()
        ]
        if not cleaned_lines:
            return ""
        return f"{corrigir_texto(title)}\n" + "\n".join(f"- {line}" for line in cleaned_lines)

    def _format_automation_summary(
        self,
        *,
        printed_titles: list[str] | None = None,
        warnings: list[str] | None = None,
        errors: list[str] | None = None,
        empty_message: str = "Nenhum relatório foi processado.",
    ) -> str:
        sections: list[str] = []
        printed_titles = [
            corrigir_texto(str(title or "").strip())
            for title in (printed_titles or [])
            if str(title or "").strip()
        ]
        warnings = [
            corrigir_texto(str(item or "").strip())
            for item in (warnings or [])
            if str(item or "").strip()
        ]
        errors = [
            corrigir_texto(str(item or "").strip())
            for item in (errors or [])
            if str(item or "").strip()
        ]
        if printed_titles:
            sections.append(
                self._format_automation_section(
                    f"Impressos enviados: {len(printed_titles)}",
                    printed_titles,
                )
            )
        if warnings:
            sections.append(self._format_automation_section("Avisos", warnings))
        if errors:
            sections.append(self._format_automation_section("Falhas", errors))
        sections = [section for section in sections if section]
        if not sections:
            return corrigir_texto(empty_message)
        return "\n\n".join(sections)

    def _warning_blocks_eh_automation_print(self, warning: str) -> bool:
        text = corrigir_texto(corrigir_estrutura_texto(str(warning or "").strip())).casefold()
        text = "".join(
            char
            for char in unicodedata.normalize("NFD", text)
            if unicodedata.category(char) != "Mn"
        )
        text = text.replace("?", "")
        return (
            "baixar automaticamente" in text
            and "caixa" in text
            and ("relatorios" in text or "relat" in text)
        )

    def _warning_blocks_mva_automation_print(self, warning: str) -> bool:
        text = corrigir_texto(corrigir_estrutura_texto(str(warning or "").strip())).casefold()
        text = "".join(
            char
            for char in unicodedata.normalize("NFD", text)
            if unicodedata.category(char) != "Mn"
        )
        text = text.replace("?", "")
        return (
            "minhas notas" in text
            and (
                "nao foi possivel consultar" in text
                or "consulta indispon" in text
            )
        )

    def _eh_report_uses_financeiro_zweb(self, fechamento: dict | None) -> bool:
        if not isinstance(fechamento, dict):
            return False
        for report in (fechamento.get("relatorios_pagamento") or {}).values():
            for row in (report.get("correlacao_rows") or []):
                if any("financeiro zweb" in corrigir_texto(str(cell or "")).casefold() for cell in row):
                    return True
        return False

    def _mva_report_has_minhas_notas_alert(self, fechamento: dict | None) -> bool:
        if not isinstance(fechamento, dict):
            return False
        for report in (fechamento.get("relatorios_pagamento") or {}).values():
            for row in (report.get("alert_rows") or []):
                normalized_row = [
                    "".join(
                        char
                        for char in unicodedata.normalize("NFD", corrigir_texto(corrigir_estrutura_texto(str(cell or "").strip())).casefold())
                        if unicodedata.category(char) != "Mn"
                    ).replace("?", "")
                    for cell in row
                ]
                if any("minhas notas" in cell for cell in normalized_row):
                    return True
        return False

    def _print_automation_jobs(
        self,
        jobs: list[dict[str, str]],
    ) -> tuple[list[dict[str, str]], list[dict[str, str]], str | None]:
        printed_jobs: list[dict[str, str]] = []
        font_family = self.font().family() or "Lexend"
        for index, job in enumerate(list(jobs or [])):
            html = str(job.get("html") or "")
            if not html:
                return (
                    printed_jobs,
                    [dict(item) for item in jobs[index:]],
                    "Um dos documentos pendentes de impressao esta vazio.",
                )
            try:
                _render_html_document_to_printer(
                    html,
                    _resolve_default_printer(),
                    font_family,
                )
            except Exception as exc:
                return printed_jobs, [dict(item) for item in jobs[index:]], str(exc)
            printed_jobs.append(dict(job))
        return printed_jobs, [], None

    def _retry_due_pending_print_jobs(self, now: dt.datetime | None = None) -> bool:
        now = now or dt.datetime.now()
        due_companies: list[str] = []
        for company in ("EH", "MVA"):
            jobs = self._pending_print_jobs_for_company(company)
            if not jobs:
                continue
            if any(
                (_parse_pending_print_datetime(job.get("retry_at")) or now) <= now
                for job in jobs
            ):
                due_companies.append(company)
        if not due_companies:
            return False
        for company in due_companies:
            self._run_pending_print_jobs_for_company(
                company,
                notify_user=False,
                trigger_label="retry automático das 08:00",
            )
        return True

    def _run_pending_print_jobs_for_company(
        self,
        company: str,
        *,
        notify_user: bool,
        trigger_label: str | None = None,
    ) -> None:
        company_key = self._normalize_pending_print_company(company)
        jobs = self._pending_print_jobs_for_company(company_key)
        if not company_key or not jobs or self._automation_running:
            return

        trigger_label = trigger_label or f"botao pendente {company_key}"
        self._automation_running = True
        self.btn_automation_power.setEnabled(False)
        self.btn_automation_test.setEnabled(False)
        self._automation_last_status = (
            f"Reimpressao pendente da {company_key} iniciada via {trigger_label}."
        )
        self._refresh_automation_controls_ui()

        printed_jobs: list[dict[str, str]] = []
        failed_jobs: list[dict[str, str]] = []
        error_message: str | None = None
        try:
            printed_jobs, failed_jobs, error_message = self._print_automation_jobs(jobs)
            if failed_jobs:
                self._replace_pending_print_jobs(
                    company_key,
                    failed_jobs,
                    error_message=error_message,
                )
            else:
                self._replace_pending_print_jobs(company_key, [])
        finally:
            self._automation_running = False
            self.btn_automation_power.setEnabled(True)
            self.btn_automation_test.setEnabled(True)

        printed_titles = [str(job.get("title") or "").strip() for job in printed_jobs if str(job.get("title") or "").strip()]
        resumo_partes: list[str] = []
        if printed_titles:
            resumo_partes.append(self._format_automation_section(f"Impressos enviados: {len(printed_titles)}", printed_titles))
        if failed_jobs:
            retry_text = self._format_pending_print_retry_text(
                self._pending_print_jobs_for_company(company_key)
            )
            resumo_partes.append(
                corrigir_texto(
                    f"Falha de impressão na {company_key}. Nova tentativa prevista para {retry_text}; "
                    "o botão pendente continua disponível."
                )
            )
        elif printed_titles:
            resumo_partes.append(corrigir_texto(f"Nenhuma impressão pendente da {company_key} restou na fila local."))
        if error_message:
            resumo_partes.append(self._format_automation_section("Erro", [error_message]))
        if not resumo_partes:
            resumo_partes.append(corrigir_texto(f"Nenhuma impressão pendente da {company_key} foi processada."))

        self._automation_last_status = "\n\n".join(item for item in resumo_partes if item)
        self._refresh_automation_controls_ui()

        if notify_user:
            title = f"{company_key} pendente"
            message = self._automation_last_status
            if failed_jobs:
                messagebox.showwarning(title, message)
            else:
                messagebox.showinfo(title, message)

    def _run_scheduled_automation(self, trigger_label: str, notify_user: bool, *, scope_mode: str) -> None:
        if self._automation_running:
            return

        gmail_status = self._get_cached_gmail_status(force=True)
        if bool(gmail_status.get("needs_auth")):
            message = (
                "Gmail não autenticado. Autorize o Gmail antes de rodar a automação do Caixa.\n\n"
                + corrigir_texto(str(gmail_status.get("message") or ""))
            ).strip()
            self._automation_last_status = message
            self._refresh_automation_controls_ui()
            if notify_user:
                messagebox.showwarning("Automação bloqueada", message)
            return

        self._automation_running = True
        self.btn_automation_power.setEnabled(False)
        self.btn_automation_test.setEnabled(False)
        data_br = self._automation_target_date_br(scope_mode)
        self._automation_last_status = (
            f"Automacao iniciada via {trigger_label} para a {self._scope_label_text(scope_mode)} de {data_br}."
        )
        self._refresh_automation_controls_ui()

        printed_titles: list[str] = []
        print_jobs: list[dict[str, str]] = []
        warnings: list[str] = []
        errors: list[str] = []

        try:
            relatorio_mva, fechamento_mva, mva_warnings, mva_error = self._generate_mva_reports_for_automation(
                data_br,
                scope_mode=scope_mode,
            )
            if mva_error:
                errors.append(f"MVA: {mva_error}")
            else:
                print_jobs.extend(
                    self._collect_automation_print_jobs("MVA", relatorio_mva, fechamento_mva)
                )
            warnings.extend([f"MVA: {aviso}" for aviso in mva_warnings if aviso])

            relatorio_eh, fechamento_eh, relatorio_pix_eh, eh_warnings, eh_error = self._generate_eh_reports_for_automation(
                data_br,
                scope_mode=scope_mode,
            )
            if eh_error:
                errors.append(f"EH: {eh_error}")
            else:
                print_jobs.extend(
                    self._collect_automation_print_jobs(
                        "EH",
                        relatorio_eh,
                        fechamento_eh,
                        relatorio_pix_eh,
                    )
                )
                warnings.extend([f"EH: {aviso}" for aviso in eh_warnings if aviso])

            if print_jobs:
                printed_jobs, failed_jobs, print_error = self._print_automation_jobs(print_jobs)
                printed_titles.extend(
                    [
                        str(job.get("title") or "").strip()
                        for job in printed_jobs
                        if str(job.get("title") or "").strip()
                    ]
                )
                if failed_jobs:
                    queue_message = self._merge_pending_print_jobs(
                        failed_jobs,
                        error_message=print_error,
                    )
                    if queue_message:
                        warnings.append(queue_message)
                if print_error:
                    errors.append(print_error)
        except Exception as exc:
            error_message = _format_exception_message(exc, "Falha inesperada durante a automação.")
            if error_message:
                errors.append(error_message)
        finally:
            self._automation_running = False
            self.btn_automation_power.setEnabled(True)
            self.btn_automation_test.setEnabled(True)

        resumo_partes: list[str] = []
        if printed_titles:
            resumo_partes.append(
                self._format_automation_section(
                    f"Impressos enviados: {len(printed_titles)}",
                    printed_titles,
                )
            )
        if warnings:
            resumo_partes.append(self._format_automation_section("Avisos", warnings))
        if errors:
            resumo_partes.append(self._format_automation_section("Falhas", errors))
        if not resumo_partes:
            resumo_partes.append("Nenhum relatório foi processado.")

        self._automation_last_status = "\n\n".join(item for item in resumo_partes if item)
        self._refresh_automation_controls_ui()

        if notify_user:
            title = "Teste da automação"
            message = f"Escopo: {self._scope_label_text(scope_mode)}\nData alvo: {data_br}\n\n{self._automation_last_status}"
            if errors:
                messagebox.showwarning(title, message)
            else:
                messagebox.showinfo(title, message)

    def _run_pending_mva_scope(self, scope_mode: str) -> None:
        payload = dict(self._mva_pending_runs.get(scope_mode) or {})
        if not payload:
            return
        data_br = str(payload.get("data_br") or self._automation_target_date_br()).strip()
        relatorio_mva, fechamento_mva, avisos_usuario, mva_error = self._generate_mva_reports_for_automation(
            data_br,
            scope_mode=scope_mode,
            force_refresh_payments=False,
        )
        self._refresh_automation_controls_ui()
        if mva_error:
            messagebox.showwarning(
                f"MVA {self._scope_label_text(scope_mode)}",
                f"{payload.get('message') or mva_error}\n\n{mva_error}",
            )
            return
        if avisos_usuario:
            messagebox.showwarning("Aviso", "\n\n".join(avisos_usuario))
        CaixaReportDialog(self, relatorio_mva, fechamento_mva).exec()

    def _run_pending_eh_scope(self, scope_mode: str) -> None:
        payload = dict(self._eh_pending_runs.get(scope_mode) or {})
        if not payload:
            return
        data_br = str(payload.get("data_br") or self._automation_target_date_br()).strip()
        relatorio_eh, fechamento_eh, relatorio_pix_eh, avisos_usuario, eh_error = self._generate_eh_reports_for_automation(
            data_br,
            scope_mode=scope_mode,
        )
        self._refresh_automation_controls_ui()
        if eh_error:
            messagebox.showwarning(
                f"EH {self._scope_label_text(scope_mode)}",
                f"{payload.get('message') or eh_error}\n\n{eh_error}",
            )
            return
        if avisos_usuario:
            messagebox.showwarning("Aviso", "\n\n".join(avisos_usuario))
        CaixaReportDialog(self, relatorio_eh, fechamento_eh, relatorio_pix_eh).exec()

    def _handle_caixa_report(self) -> None:
        cnpj = CaixaCnpjDialog(self).choice()
        if not cnpj:
            return
        if not self._ensure_gmail_authenticated_for_caixa():
            return

        if cnpj == "MVA":
            auto_files = self._auto_find_mva_caixa_files()

            path_davs = auto_files.get("davs", "")
            if not path_davs:
                if not InstructionDialog(
                    self,
                    "Caixa MVA - Passo 1 de 3",
                    "Selecione agora o PDF DAV MVA.\n\n"
                    "O app tentou localizar automaticamente um arquivo com nome DAV e não encontrou.",
                ).confirmed():
                    return
                path_davs = filedialog.askopenfilename(
                    filetypes=[("Arquivos PDF", "*.pdf")],
                    title="Caixa MVA - Passo 1 de 3: selecionar DAV MVA",
                )
            if not path_davs:
                return

            path_orcamentos = auto_files.get("orcamentos", "")
            if not path_orcamentos:
                budget_choice = MvaBudgetMissingDialog(self).choice()
                if budget_choice is None:
                    return
                if budget_choice == "select":
                    path_orcamentos = filedialog.askopenfilename(
                        filetypes=[("Arquivos PDF", "*.pdf")],
                        title="Caixa MVA - Passo 2 de 3: selecionar Orcamento",
                    )
                    if not path_orcamentos:
                        return

            path_cupons = auto_files.get("cupons", "")
            if not path_cupons:
                if not InstructionDialog(
                    self,
                    "Caixa MVA - Passo 3 de 3",
                    "Selecione agora o PDF Fechamento de Caixa.\n\n"
                    "O app tentou localizar automaticamente um arquivo com nome Fechamento de Caixa e não encontrou.",
                ).confirmed():
                    return
                path_cupons = filedialog.askopenfilename(
                    filetypes=[("Arquivos PDF", "*.pdf")],
                    title="Caixa MVA - Passo 3 de 3: selecionar Fechamento de Caixa",
                )
            if not path_cupons:
                continuar_sem_cupons = messagebox.askyesno(
                    "Fechamento de Caixa não selecionado",
                    "O Fechamento de Caixa não foi selecionado.\n\n"
                    "Deseja continuar somente com a análise dos DAVs da MVA?",
                )
                if not continuar_sem_cupons:
                    return

            allow_cielo_fallback = True
            if path_cupons:
                allow_cielo_fallback = messagebox.askyesno(
                    "Cielo",
                    "Usar Cielo?",
                )

            selected_scope_mode: str | None = None
            selected_opening_date: str | None = None
            if path_cupons and self._mva_special_scope_enabled:
                try:
                    relatorio_cupons_preview = analisar_pdf_fechamento_caixa_mva_clipp(
                        path_cupons,
                        auto_download_missing=False,
                    )
                except Exception as exc:
                    messagebox.showerror("Erro", f"Erro ao analisar o Fechamento de Caixa:\n{exc}")
                    return
                preview_ok, _preview_msg = validar_relatorio_resumo_nfce(
                    relatorio_cupons_preview,
                    modelo_esperado="MVA",
                )
                if preview_ok and relatorio_cupons_preview.get("quantidade_nfce", 0) > 0:
                    selected_opening_date = str(relatorio_cupons_preview.get("periodo") or "").split(" - ", 1)[0].strip() or None
                    selected_scope_mode = self._resolve_manual_closing_scope(relatorio_cupons_preview, "MVA")
                    if selected_scope_mode is None:
                        return

            relatorio_davs, relatorio_orcamentos, relatorio_cupons, mva_msg = self._load_mva_reports_with_loading(
                path_davs,
                path_orcamentos,
                path_cupons,
                force_refresh_payments=False,
                allow_cielo_fallback=allow_cielo_fallback,
                scope_mode=selected_scope_mode,
                filter_opening_date_br=selected_opening_date,
            )
            if mva_msg:
                messagebox.showerror("Erro", f"Erro ao analisar PDF de Caixa:\n{mva_msg}")
                return
            fechamento = None

            davs_ok, davs_msg = validar_arquivo_caixa_mva(
                relatorio_davs,
                "exportacao_dados_mva",
            )
            if not davs_ok:
                messagebox.showwarning("Arquivo inválido", davs_msg)
                return

            if path_orcamentos:
                orc_ok, orc_msg = validar_arquivo_caixa_mva(
                    relatorio_orcamentos,
                    "orcamentos_mva",
                )
                if not orc_ok:
                    messagebox.showwarning("Arquivo inválido", orc_msg)
                    return

            if path_orcamentos and relatorio_davs.get("periodo") and relatorio_orcamentos.get("periodo"):
                if relatorio_davs.get("periodo") != relatorio_orcamentos.get("periodo"):
                    messagebox.showwarning(
                        "Período inválido",
                        "A Exportação de dados e o relatório de Orçamentos precisam ser do mesmo período.",
                    )
                    return

            relatorios_mva = [relatorio_davs]
            if path_orcamentos and relatorio_orcamentos:
                relatorios_mva.append(relatorio_orcamentos)
            relatorio = combinar_relatorios_caixa_mva(relatorios_mva)

            if relatorio.get("pedidos_total", 0) <= 0:
                messagebox.showwarning("Aviso", "Nenhum pedido foi encontrado neste PDF.")
                return

            caixa_ok, caixa_msg = validar_relatorio_pedidos_importados(
                relatorio,
                modelo_esperado="MVA",
            )
            if not caixa_ok:
                messagebox.showwarning("Arquivo inválido", caixa_msg)
                return

            if path_cupons and relatorio_cupons:
                resumo_ok, resumo_msg = validar_relatorio_resumo_nfce(
                    relatorio_cupons,
                    modelo_esperado="MVA",
                )
                if not resumo_ok:
                    messagebox.showwarning("Arquivo inválido", resumo_msg)
                    return
                if relatorio_cupons.get("quantidade_nfce", 0) <= 0:
                    messagebox.showwarning("Aviso", "Nenhum cupom foi encontrado no relatório informado.")
                    return
                periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
                    relatorio,
                    relatorio_cupons,
                    titulo_secundario="relatório de Cupons",
                )
                if not periodo_ok:
                    messagebox.showwarning("Período inválido", periodo_msg)
                    return
                scope_mode = selected_scope_mode or self._resolve_manual_closing_scope(relatorio_cupons, "MVA")
                if scope_mode is None:
                    return
                if not self._closing_scope_available(scope_mode, relatorio_cupons):
                    messagebox.showwarning(
                        "Escopo indisponível",
                        self._scope_unavailable_message(scope_mode, "MVA")
                        or "O fechamento da MVA ainda não está disponível para o escopo solicitado.",
                    )
                    return
                relatorio, relatorio_cupons, _ = self._apply_scope_to_reports(
                    relatorio,
                    relatorio_cupons,
                    None,
                    scope_mode=scope_mode,
                )
                fechamento = comparar_caixa_resumo_nfce(relatorio, relatorio_cupons)

            avisos_usuario = list(
                dict.fromkeys(
                    list((relatorio_cupons or {}).get("avisos_usuario") or [])
                    + list((fechamento or {}).get("avisos_usuario") or [])
                )
            )
            if avisos_usuario:
                messagebox.showwarning("Aviso", "\n\n".join(avisos_usuario))

            CaixaReportDialog(self, relatorio, fechamento).exec()
            return

        data_caixa = CaixaDateDialog(
            self,
            "Caixa EH - Data",
            "Selecione o dia do relatório da EH.",
        ).selected_date()
        if not data_caixa:
            return

        fechamento_inicio_br = data_caixa
        fechamento_fim_br = data_caixa
        filtrar_fechamento_por_data_venda = False
        selected_scope_mode: str | None = None
        if self._eh_special_closing_enabled:
            try:
                data_dt = dt.datetime.strptime(data_caixa, "%d/%m/%Y")
                fechamento_fim_br = (data_dt + dt.timedelta(days=1)).strftime("%d/%m/%Y")
                filtrar_fechamento_por_data_venda = True
            except ValueError:
                messagebox.showwarning("Data inválida", "A data selecionada para o Caixa EH é inválida.")
                return
            selected_scope_mode = CaixaScopeDialog(self, company_label="EH").choice()
            if selected_scope_mode is None:
                return

        relatorio, relatorio_nfce, relatorio_pix, eh_msg = self._load_eh_caixa_reports_with_loading(
            data_caixa,
            force_refresh_payments=False,
            fechamento_data_inicio_br=fechamento_inicio_br,
            fechamento_data_fim_br=fechamento_fim_br,
            filtrar_fechamento_por_data_venda=filtrar_fechamento_por_data_venda,
            scope_mode=selected_scope_mode,
        )
        if eh_msg == "__cancelled__":
            return

        if eh_msg:
            messagebox.showerror("Caixa EH", eh_msg)
            return

        fechamento = None

        caixa_ok, caixa_msg = validar_relatorio_pedidos_importados(
            relatorio,
            modelo_esperado="EH",
        )
        if not caixa_ok:
            messagebox.showwarning("Arquivo inválido", caixa_msg)
            return

        if relatorio.get("pedidos_total", 0) <= 0:
            messagebox.showwarning("Aviso", "Nenhum pedido foi encontrado neste PDF.")
            return

        if relatorio_nfce:
            resumo_ok, resumo_msg = validar_relatorio_resumo_nfce(
                relatorio_nfce,
                modelo_esperado="EH",
            )
            if not resumo_ok:
                messagebox.showwarning(
                    "Arquivo inválido",
                    "O Fechamento de caixa do Zweb não trouxe um total válido para comparação.",
                )
                return
            if relatorio_nfce.get("quantidade_nfce", 0) <= 0:
                messagebox.showwarning("Aviso", "Nenhuma NFC-e foi encontrada no Fechamento de caixa do Zweb.")
                return
            periodo_ok, periodo_msg = validar_periodo_relatorios_caixa(
                relatorio,
                relatorio_nfce,
                titulo_secundario="Fechamento de caixa",
            )
            if not periodo_ok:
                messagebox.showwarning("Período inválido", periodo_msg)
                return
            scope_mode = selected_scope_mode or self._resolve_manual_closing_scope(relatorio_nfce, "EH")
            if scope_mode is None:
                return
            if not self._closing_scope_available(scope_mode, relatorio_nfce):
                messagebox.showwarning(
                    "Escopo indisponível",
                    self._scope_unavailable_message(scope_mode, "EH")
                    or "O fechamento da EH ainda não está disponível para o escopo solicitado.",
                )
                return
            relatorio, relatorio_nfce, relatorio_pix = self._apply_scope_to_reports(
                relatorio,
                relatorio_nfce,
                relatorio_pix,
                scope_mode=scope_mode,
            )
            fechamento = comparar_caixa_resumo_nfce(relatorio, relatorio_nfce)
            avisos_usuario = list(
                dict.fromkeys(
                    list(relatorio_nfce.get("avisos_usuario") or [])
                    + list((fechamento or {}).get("avisos_usuario") or [])
                    + list((relatorio_pix or {}).get("avisos_usuario") or [])
                )
            )
            if avisos_usuario:
                messagebox.showwarning("Aviso", "\n\n".join(avisos_usuario))

        periodo_pix = (relatorio_nfce or {}).get("periodo") or relatorio.get("periodo")
        if relatorio_pix is None and periodo_pix:
            relatorio_pix = {
                "arquivo": "",
                "periodo": periodo_pix,
                "quantidade_autorizados": 0,
                "total_autorizado": 0.0,
                "itens_autorizados": [],
                "mensagem": "Nenhum pagamento digital de NFC-e foi encontrado em Financeiro > Movimentações para este dia.",
            }
        elif relatorio_pix is None:
            relatorio_pix = {
                "arquivo": "",
                "periodo": None,
                "quantidade_autorizados": 0,
                "total_autorizado": 0.0,
                "itens_autorizados": [],
                "mensagem": "O período do caixa não foi identificado; não foi possível consultar os pagamentos digitais do Zweb.",
            }

        CaixaReportDialog(self, relatorio, fechamento, relatorio_pix).exec()

    def _build_graphs_view(self) -> QtWidgets.QWidget:
        container = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(container)
        layout.setSpacing(10)

        controls = QtWidgets.QHBoxLayout()
        label_source = QtWidgets.QLabel("Fonte:")
        self.graph_source = QtWidgets.QComboBox()
        self.graph_source.addItems(["MVA", "EH", "Todos", "Vendas totais"])
        label_metric = QtWidgets.QLabel("Coluna:")
        self.graph_metric = QtWidgets.QComboBox()
        label_order = QtWidgets.QLabel("Ordem:")
        self.graph_order = QtWidgets.QComboBox()
        self.graph_order.addItems(["Desc", "Asc"])

        controls.addWidget(label_source)
        controls.addWidget(self.graph_source)
        controls.addSpacing(10)
        controls.addWidget(label_metric)
        controls.addWidget(self.graph_metric)
        controls.addSpacing(10)
        controls.addWidget(label_order)
        controls.addWidget(self.graph_order)
        controls.addStretch()

        layout.addLayout(controls)

        self.graph_chart = BarChartWidget()
        self.graph_scroll = QtWidgets.QScrollArea()
        self.graph_scroll.setWidgetResizable(True)
        self.graph_scroll.setWidget(self.graph_chart)
        self.graph_scroll.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Expanding)
        layout.addWidget(self.graph_scroll)

        self.graph_source.currentIndexChanged.connect(self._update_graph_metric_options)
        self.graph_metric.currentIndexChanged.connect(self._refresh_graphs_data)
        self.graph_order.currentIndexChanged.connect(self._refresh_graphs_data)

        self._update_graph_metric_options()
        return container

    def _update_graph_metric_options(self) -> None:
        source = self.graph_source.currentText()
        self.graph_metric.blockSignals(True)
        self.graph_metric.clear()
        self.graph_metric.addItems(list(self.cols_main[1:]))
        self.graph_metric.blockSignals(False)
        self._refresh_graphs_data()

    def _refresh_graphs_data(self) -> None:
        source = self.graph_source.currentText()
        metric = self.graph_metric.currentText()
        if not metric:
            self.graph_chart.set_data([], QtGui.QColor("#59C734"))
            return

        data = []
        show_decimals = metric == "Total Vendas"
        result = self._collect_results_by_source(source, metric)
        if result.get("dual"):
            data = result["data"]
            reverse = self.graph_order.currentText() == "Desc"
            data.sort(key=lambda item: item[1] + item[2], reverse=reverse)
            self.graph_chart.set_data_dual(
                data,
                colors=(QtGui.QColor("#FF8A00"), QtGui.QColor("#2F6BFF")),
                show_decimals=show_decimals,
            )
        else:
            data = result["data"]
            color = result["color"]
            gradient = result["gradient"]
            reverse = self.graph_order.currentText() == "Desc"
            data.sort(key=lambda item: item[1], reverse=reverse)
            self.graph_chart.set_data(data, color, show_decimals=show_decimals, gradient_colors=gradient)

    def _collect_table_data(self, tree: QtTreeAdapter, columns, metric: str):
        try:
            metric_index = columns.index(metric)
        except ValueError:
            return []
        out = []
        for item in tree.get_children():
            values = tree.item(item)["values"]
            if not values or len(values) <= metric_index:
                continue
            label = values[0]
            value = values[metric_index]
            out.append((label, float(parse_number(value))))
        return out

    def _collect_results_by_source(self, source: str, metric: str):
        try:
            from global_vars import results_by_source
        except Exception:
            results_by_source = {"MVA": [], "EH": []}

        def merge_results(items):
            merged = {}
            for _, res in items:
                if not isinstance(res, dict):
                    continue
                if res.get("__cancelled__") or res.get("__empty__") or res.get("__error__"):
                    continue
                for vendedor, dados in res.items():
                    if vendedor not in merged:
                        merged[vendedor] = {
                            "atendidos": 0,
                            "devolucoes": 0,
                            "total_clientes": 0,
                            "total_vendas": 0.0,
                        }
                    merged[vendedor]["atendidos"] += dados.get("atendidos", 0)
                    merged[vendedor]["devolucoes"] += dados.get("devolucoes", 0)
                    merged[vendedor]["total_vendas"] += parse_number(dados.get("total_vendas", 0))

            for dados in merged.values():
                dados["total_clientes"] = dados["atendidos"] - dados["devolucoes"]
            return merged

        gradient = None
        if source == "MVA":
            merged = merge_results(results_by_source.get("MVA", []))
            color = QtGui.QColor("#FF8A00")
        elif source == "EH":
            merged = merge_results(results_by_source.get("EH", []))
            color = QtGui.QColor("#2F6BFF")
        elif source == "Vendas totais":
            data = self._collect_table_data(self.tree_main, self.cols_main, metric)
            color = QtGui.QColor("#FF8A00")
            gradient = (QtGui.QColor("#FF8A00"), QtGui.QColor("#2F6BFF"))
            return {"data": data, "color": color, "gradient": gradient, "dual": False}
        else:
            merged_mva = merge_results(results_by_source.get("MVA", []))
            merged_eh = merge_results(results_by_source.get("EH", []))
            metric_key = {
                "Atendidos": "atendidos",
                "Devoluções": "devolucoes",
                "Total Final": "total_clientes",
                "Total Vendas": "total_vendas",
            }.get(metric)
            if not metric_key:
                return {"data": [], "color": QtGui.QColor("#FF8A00"), "gradient": None, "dual": True}
            vendors = sorted(set(merged_mva.keys()) | set(merged_eh.keys()))
            data = []
            for v in vendors:
                v1 = float(merged_mva.get(v, {}).get(metric_key, 0))
                v2 = float(merged_eh.get(v, {}).get(metric_key, 0))
                data.append((v, v1, v2))
            return {"data": data, "color": QtGui.QColor("#FF8A00"), "gradient": None, "dual": True}

        metric_key = {
            "Atendidos": "atendidos",
            "Devoluções": "devolucoes",
            "Total Final": "total_clientes",
            "Total Vendas": "total_vendas",
        }.get(metric)

        if not metric_key:
            return {"data": [], "color": color, "gradient": gradient, "dual": False}

        data = [(v, float(d.get(metric_key, 0))) for v, d in merged.items()]
        return {"data": data, "color": color, "gradient": gradient, "dual": False}

    def _toggle_graphs_view(self) -> None:
        if not self._showing_graphs:
            if not self._confirm_discard_edits("abrir gráficos"):
                return
            self._reset_edit_state()
            self._showing_graphs = True
            self.content_stack.setCurrentIndex(1)
            self._refresh_graphs_data()
            self.btn_graphs.setText("Tabelas")
            self._refresh_dashboard_status_cards()
            return

        self._showing_graphs = False
        self.content_stack.setCurrentIndex(0)
        self.btn_graphs.setText("Gráficos")
        self._refresh_dashboard_status_cards()

    def _handle_load_planilhas(self) -> None:
        if not self._confirm_discard_edits("carregar planilhas"):
            return
        use_online_bar = self._is_main_progress_active()
        if use_online_bar:
            self.progress_var_online.set(0)
            self.progress_bar_online.setVisible(True)
            progress_var = self.progress_var_online
            progress_bar = self.progress_bar_online_adapter
        else:
            self.progress_bar_online.setVisible(False)
            progress_var = self.progress_var
            progress_bar = self.progress_bar_adapter
        carregar_planilhas_duplas_async(
            self.tree_mva,
            self.tree_eh,
            progress_var,
            progress_bar,
            self.root_adapter,
        )

    def _handle_clear_tables(self) -> None:
        if not self._confirm_discard_edits("limpar tabelas"):
            return
        limpar_tabelas_duplas(
            self.tree_main,
            self.tree_mva,
            self.tree_eh,
            self.label_files_var,
            self.progress_var,
        )

    def _handle_merge_tables(self) -> None:
        if not self._confirm_discard_edits("mesclar tabelas"):
            return
        mesclar_tabelas_duplas(
            self.tree_main,
            self.progress_var,
            self.progress_bar_adapter,
            self.root_adapter,
            self.label_files_var,
            self.tree_mva,
            self.tree_eh,
        )
    def _export_dialog(self) -> None:
        dlg = QtWidgets.QDialog(self)
        dlg.setWindowTitle("Exportar")
        dlg.setFixedSize(250, 150)
        layout = QtWidgets.QVBoxLayout(dlg)
        label = QtWidgets.QLabel("Escolha o formato para exportar:")
        label.setAlignment(QtCore.Qt.AlignCenter)
        layout.addWidget(label)
        btn_excel = QtWidgets.QPushButton("Excel")
        btn_pdf = QtWidgets.QPushButton("PDF")
        btn_excel.setStyleSheet("text-align:center;")
        btn_pdf.setStyleSheet("text-align:center;")
        buttons = QtWidgets.QHBoxLayout()
        buttons.addStretch()
        buttons.addWidget(btn_excel)
        buttons.addWidget(btn_pdf)
        buttons.addStretch()
        layout.addLayout(buttons)

        btn_excel.clicked.connect(lambda: self._export_excel(dlg))
        btn_pdf.clicked.connect(lambda: self._export_pdf(dlg))
        dlg.exec()

    def _infer_origem_from_filename(self, path: str) -> str | None:
        name = os.path.basename(path).lower()
        tokens = re.findall(r"[a-z0-9]+", name)
        joined = " ".join(tokens)

        if re.search(r"\bmva\b", joined):
            return "MVA"
        if re.search(r"\beh\b", joined) or "horizonte" in joined:
            return "EH"

        def is_similar(value: str, target: str) -> bool:
            if value == target:
                return True
            ratio = difflib.SequenceMatcher(None, value, target).ratio()
            return ratio >= 0.75

        for token in tokens:
            if is_similar(token, "mva"):
                return "MVA"
            if is_similar(token, "eh"):
                return "EH"
            if is_similar(token, "horizonte"):
                return "EH"

        if is_similar(joined.replace(" ", ""), "mva"):
            return "MVA"
        if is_similar(joined.replace(" ", ""), "horizonte"):
            return "EH"
        return None

    def _toggle_table_edit(self) -> None:
        if not self._edit_mode:
            if not self._has_table_data():
                messagebox.showwarning("Aviso", "Importe um PDF antes de editar a tabela.")
                return
            self._edit_mode = True
            self._table_dirty = False
            self.table_main.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectRows)
            self.table_main.setEditTriggers(
                QtWidgets.QAbstractItemView.DoubleClicked
                | QtWidgets.QAbstractItemView.SelectedClicked
                | QtWidgets.QAbstractItemView.EditKeyPressed
            )
            self._set_table_edit_visual_state(True)
            self.btn_edit_table.setText("Salvar Tabela")
            self._refresh_dashboard_status_cards()
            return

        if not self._save_table_pdf():
            return

        self._edit_mode = False
        self._table_dirty = False
        self.table_main.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        self.table_main.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectItems)
        self._set_table_edit_visual_state(False)
        self.btn_edit_table.setText("Editar tabela")
        self._refresh_dashboard_status_cards()

    def _on_table_item_changed(self, _item: QtWidgets.QTableWidgetItem) -> None:
        if self._edit_mode:
            self._table_dirty = True
            self._refresh_dashboard_status_cards()

    def _export_excel(self, dlg: QtWidgets.QDialog) -> None:
        try:
            _excel_export(self.tree_main)
            dlg.accept()
        except Exception as exc:
            messagebox.showerror("Erro", f"Erro ao exportar Excel: {exc}")

    def _export_pdf(self, dlg: QtWidgets.QDialog) -> None:
        try:
            if _pdf_export(self.tree_main):
                dlg.accept()
        except Exception as exc:
            messagebox.showerror("Erro", f"Erro ao exportar PDF: {exc}")

    def _save_table_pdf(self) -> bool:
        try:
            return _pdf_export(self.tree_main)
        except Exception as exc:
            messagebox.showerror("Erro", f"Erro ao salvar tabela: {exc}")
            return False
    def _setup_import_neon(self) -> None:
        self._neon_timer = QtCore.QTimer(self)
        self._neon_timer.setInterval(25)
        self._neon_timer.timeout.connect(self._update_import_neon)
        self._neon_timer.start()
        self._update_import_neon()

    def _setup_graphs_refresh_timer(self) -> None:
        self._graphs_timer = QtCore.QTimer(self)
        self._graphs_timer.setInterval(500)
        self._graphs_timer.timeout.connect(self._refresh_graphs_if_visible)
        self._graphs_timer.start()

    def _refresh_graphs_if_visible(self) -> None:
        if self._showing_graphs:
            self._refresh_graphs_data()

    def _setup_progress_visibility_timer(self) -> None:
        self._progress_timer = QtCore.QTimer(self)
        self._progress_timer.setInterval(250)
        self._progress_timer.timeout.connect(self._update_progress_visibility)
        self._progress_timer.start()

    def _update_progress_visibility(self) -> None:
        if self.progress_bar_online.isVisible() and not self._is_main_progress_active():
            if self.progress_var_online.get() in (0, 100):
                self.progress_bar_online.setVisible(False)

    def _is_main_progress_active(self) -> bool:
        try:
            value = int(self.progress_var.get() or 0)
        except Exception:
            value = 0
        return 0 < value < 100 or self.btn_cancel.isEnabled()

    def _update_import_neon(self) -> None:
        if self._should_highlight_import_button():
            self._neon_on = True
            self._neon_hue = (self._neon_hue + 4) % 360
            color_a = QtGui.QColor.fromHsv(self._neon_hue, 180, 200)
            color_b = QtGui.QColor.fromHsv((self._neon_hue + 140) % 360, 180, 200)
            glow = QtGui.QColor.fromHsv(self._neon_hue, 220, 255)
            self.btn_select_pdf.setStyleSheet(
                "QPushButton{"
                "background:qlineargradient(x1:0,y1:0,x2:1,y2:0,"
                f"stop:0 {color_a.name()}, stop:1 {color_b.name()});"
                f"border:1px solid {glow.name()};"
                "border-radius:6px;padding:6px 10px;text-align:center;"
                "}"
            )
            self.btn_select_pdf.update()
            return

        if self._neon_on:
            self._neon_on = False
            self.btn_select_pdf.setStyleSheet("")
            self.btn_select_pdf.update()

    def _refresh_import_button_state(self) -> None:
        import_available = self._can_import_more_pdfs()
        if self.btn_select_pdf.isEnabled() != import_available:
            self.btn_select_pdf.setEnabled(import_available)
        if import_available:
            if self._loaded_pdf_count() == 0:
                self.btn_select_pdf.setToolTip("Importar PDF")
            else:
                self.btn_select_pdf.setToolTip("Adicionar segundo PDF")
            return
        if self._neon_on:
            self._neon_on = False
            self.btn_select_pdf.setStyleSheet("")
            self.btn_select_pdf.update()
        self.btn_select_pdf.setToolTip(
            "Importar indisponível depois que os dois PDFs já foram carregados. Use Limpar para liberar novamente."
        )

    def _should_highlight_import_button(self) -> bool:
        return self.btn_select_pdf.isEnabled() and self._loaded_pdf_count() == 0 and not self.tree_main.get_children()

    def _loaded_pdf_count(self) -> int:
        try:
            from global_vars import listFiles
        except Exception:
            return 0
        return len(listFiles or [])

    def _can_import_more_pdfs(self) -> bool:
        return self._loaded_pdf_count() < 2

    def _are_tables_empty(self) -> bool:
        return (
            not self.tree_main.get_children()
            and not self.tree_mva.get_children()
            and not self.tree_eh.get_children()
        )

    def _has_table_data(self) -> bool:
        return bool(self.tree_main.get_children())

    def _set_table_edit_visual_state(self, active: bool) -> None:
        if not hasattr(self, "table_main"):
            return
        next_state = bool(active)
        if self.table_main.property("editModeActive") == next_state:
            return
        self.table_main.setProperty("editModeActive", next_state)
        style = self.table_main.style()
        if style is not None:
            style.unpolish(self.table_main)
            style.polish(self.table_main)
        self.table_main.viewport().update()
        self.table_main.repaint()

    def _sync_table_hover_selection(self, row: int, column: int, force: bool = False) -> None:
        if not hasattr(self, "table_main"):
            return
        if row < 0 or column < 0 or not self._edit_mode:
            return
        if not force and self.table_main.state() == QtWidgets.QAbstractItemView.EditingState:
            return
        flags = (
            QtCore.QItemSelectionModel.ClearAndSelect
            | QtCore.QItemSelectionModel.Rows
        )
        if self.table_main.currentRow() == row and self.table_main.selectionModel().hasSelection():
            selected_rows = self.table_main.selectionModel().selectedRows()
            if len(selected_rows) == 1 and selected_rows[0].row() == row:
                return
        blocker = QtCore.QSignalBlocker(self.table_main)
        try:
            self.table_main.setCurrentCell(row, column, flags)
        finally:
            del blocker

    def _reset_edit_state(self) -> None:
        self._edit_mode = False
        self._table_dirty = False
        self.table_main.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
        self.table_main.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectItems)
        self._set_table_edit_visual_state(False)
        self.btn_edit_table.setText("Editar tabela")
        self._refresh_dashboard_status_cards()

    def _confirm_discard_edits(self, acao: str) -> bool:
        if not (self._edit_mode or self._table_dirty):
            return True
        dlg = QtWidgets.QMessageBox(self)
        dlg.setWindowTitle("Alterações não salvas")
        dlg.setText(
            f"Existem alterações não salvas. Se você {acao}, elas serão perdidas.\n"
            "Deseja salvar antes de continuar?"
        )
        dlg.setIcon(QtWidgets.QMessageBox.Warning)
        btn_save = dlg.addButton("Salvar", QtWidgets.QMessageBox.AcceptRole)
        btn_discard = dlg.addButton("Descartar", QtWidgets.QMessageBox.DestructiveRole)
        btn_cancel = dlg.addButton("Cancelar", QtWidgets.QMessageBox.RejectRole)
        _center_message_box_buttons(dlg)
        dlg.exec()
        clicked = dlg.clickedButton()
        if clicked == btn_save:
            if self._save_table_pdf():
                self._reset_edit_state()
                return True
            return False
        if clicked == btn_discard:
            self._reset_edit_state()
            return True
        return False


    def _confirm_generated_auto_reports_cleanup(self) -> bool:
        cleanup_generated_auto_reports()
        return True

    def closeEvent(self, event: QtGui.QCloseEvent) -> None:
        if self._edit_mode or self._table_dirty:
            dlg = QtWidgets.QMessageBox(self)
            dlg.setWindowTitle("Sair sem salvar?")
            dlg.setText(
                "A tabela esta em modo de edição. Alterações não serão salvas.\n"
                "Deseja salvar antes de sair?"
            )
            dlg.setIcon(QtWidgets.QMessageBox.Warning)
            btn_save = dlg.addButton("Salvar", QtWidgets.QMessageBox.AcceptRole)
            btn_discard = dlg.addButton("Descartar", QtWidgets.QMessageBox.DestructiveRole)
            btn_cancel = dlg.addButton("Cancelar", QtWidgets.QMessageBox.RejectRole)
            _center_message_box_buttons(dlg)
            dlg.exec()
            clicked = dlg.clickedButton()
            if clicked == btn_save:
                if self._save_table_pdf():
                    self._edit_mode = False
                    self._table_dirty = False
                    self.table_main.setEditTriggers(QtWidgets.QAbstractItemView.NoEditTriggers)
                    self.table_main.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectItems)
                    self._set_table_edit_visual_state(False)
                    self._set_online_tables_editable(False)
                    self.btn_edit_table.setText("Editar tabela")
                    if not self._confirm_generated_auto_reports_cleanup():
                        event.ignore()
                        return
                    event.accept()
                    return
                event.ignore()
                return
            if clicked == btn_discard:
                if not self._confirm_generated_auto_reports_cleanup():
                    event.ignore()
                    return
                event.accept()
                return
            if clicked == btn_cancel:
                event.ignore()
                return
        if not self._confirm_generated_auto_reports_cleanup():
            event.ignore()
            return
        super().closeEvent(event)

    def _sort_table(self, tree: QtTreeAdapter, cols, idx: int) -> None:
        col = cols[idx]
        key = (id(tree), col)
        reverse = self._sort_state.get(key, False)
        ordenar_coluna(tree, col, reverse)
        self._sort_state[key] = not reverse


def run_app() -> None:
    atexit.register(cleanup_generated_auto_reports)
    app = QtWidgets.QApplication.instance() or QtWidgets.QApplication(sys.argv)
    app.aboutToQuit.connect(cleanup_generated_auto_reports)
    window = MainWindow()
    window.show()
    try:
        sys.exit(app.exec())
    finally:
        cleanup_generated_auto_reports()

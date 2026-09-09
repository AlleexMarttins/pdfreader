from datetime import date, datetime

from clipp_mva import ClippMvaConnectionSettings, ClippMvaReader


class _ClosingCursor:
    def __init__(self):
        self._rows = []

    def execute(self, statement, params=()):
        normalized = " ".join(statement.lower().split())
        if "from tb_pdv_mov" in normalized:
            self._rows = [] if "dt_hr_fechamento is not null" in normalized else [
                (1235, 1, datetime(2026, 8, 10, 7, 52, 15), None, 250.0, 0.0, 0.0)
            ]
        elif "from tb_pdv_venda" in normalized:
            self._rows = [
                (10, 397678, date(2026, 8, 10), datetime(2026, 8, 10, 8, 6, 54).time(), "CLIENTE BALCAO", 29.0)
            ]
        elif "from v_nfvenda_pagamentos" in normalized:
            self._rows = [(10, "Cartao de Debito", 29.0)]
        else:
            raise AssertionError(f"Consulta inesperada: {statement}")

    def fetchall(self):
        return self._rows


class _ClosingConnection:
    def __init__(self):
        self.cursor_instance = _ClosingCursor()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        return False

    def cursor(self):
        return self.cursor_instance


class _ClosedAndOpenCursor:
    def __init__(self):
        self._rows = []

    def execute(self, statement, params=()):
        normalized = " ".join(statement.lower().split())
        if "from tb_pdv_mov" in normalized:
            self._rows = [
                (1235, 1, datetime(2026, 8, 10, 7, 52, 15), datetime(2026, 8, 10, 14, 16, 45), 250.0, 0.0, 0.0),
                (1236, 1, datetime(2026, 8, 10, 14, 16, 55), None, 250.0, 0.0, 0.0),
            ]
        elif "from tb_pdv_venda" in normalized:
            self._rows = [
                (10, 397678, date(2026, 8, 10), datetime(2026, 8, 10, 8, 6, 54).time(), "CLIENTE BALCAO", 29.0)
            ] if params == (1235,) else [
                (11, 397754, date(2026, 8, 10), datetime(2026, 8, 10, 14, 18, 0).time(), "CLIENTE BALCAO", 55.05)
            ]
        elif "from v_nfvenda_pagamentos" in normalized:
            self._rows = [(10, "Cartao de Debito", 29.0)]
        else:
            raise AssertionError(f"Consulta inesperada: {statement}")

    def fetchall(self):
        return self._rows


class _ClosedAndOpenConnection:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        return False

    def cursor(self):
        return _ClosedAndOpenCursor()


class _PixClosingCursor(_ClosingCursor):
    def execute(self, statement, params=()):
        super().execute(statement, params)
        if "from v_nfvenda_pagamentos" in " ".join(statement.lower().split()):
            self._rows = [(10, "Pagamento Instantâneo (PIX)", 29.0)]


class _PixClosingConnection:
    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        return False

    def cursor(self):
        return _PixClosingCursor()


class _CancelledCouponCursor:
    def __init__(self):
        self._rows = []
        self.params = ()

    def execute(self, statement, params=()):
        self.params = params
        normalized = " ".join(statement.lower().split())
        if "n.status = '135'" not in normalized:
            raise AssertionError(f"Consulta inesperada: {statement}")
        self._rows = [
            (399973, date(2026, 9, 2), datetime(2026, 9, 2, 10, 0, 54).time(), 111.0, "135"),
            (399988, date(2026, 9, 2), datetime(2026, 9, 2, 11, 18, 31).time(), 19.75, "135"),
        ]

    def fetchall(self):
        return self._rows


class _CancelledCouponConnection:
    def __init__(self):
        self.cursor_instance = _CancelledCouponCursor()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, traceback):
        return False

    def cursor(self):
        return self.cursor_instance


def test_closing_report_includes_authorized_sales_from_open_movement(monkeypatch):
    reader = ClippMvaReader(
        ClippMvaConnectionSettings(
            host="server",
            database="database",
            user="user",
            password="password",
        )
    )
    monkeypatch.setattr(reader, "_connect", _ClosingConnection)

    closing = reader.build_closing_report(date(2026, 8, 10))

    assert closing["quantidade_nfce"] == 1
    assert closing["total_nfce"] == 29.0
    assert closing["fechamento_parcial"] is True
    assert closing["fechamento_janelas"] == [
        {
            "id_movimento": 1235,
            "caixa": 1,
            "abertura": "10/08/2026 07:52:15",
            "fechamento": "",
            "abertura_valor": 250.0,
            "sangria": 0.0,
            "suprimento": 0.0,
        }
    ]
    assert closing["relatorios_pagamento"]["cartao_debito"]["total_autorizado"] == 29.0


def test_closing_report_maps_clipp_pix_to_the_closing_payment_key(monkeypatch):
    reader = ClippMvaReader(
        ClippMvaConnectionSettings(
            host="server",
            database="database",
            user="user",
            password="password",
        )
    )
    monkeypatch.setattr(reader, "_connect", _PixClosingConnection)

    closing = reader.build_closing_report(date(2026, 8, 10))

    assert closing["relatorios_pagamento"]["pix_fechamento"]["total_autorizado"] == 29.0
    assert "pix" not in closing["relatorios_pagamento"]


def test_closing_report_ignores_new_open_movement_after_a_closure(monkeypatch):
    reader = ClippMvaReader(
        ClippMvaConnectionSettings(
            host="server",
            database="database",
            user="user",
            password="password",
        )
    )
    monkeypatch.setattr(reader, "_connect", _ClosedAndOpenConnection)

    closing = reader.build_closing_report(date(2026, 8, 10))

    assert closing["quantidade_nfce"] == 1
    assert closing["total_nfce"] == 29.0
    assert closing["fechamento_parcial"] is False
    assert [window["id_movimento"] for window in closing["fechamento_janelas"]] == [1235]


def test_cancelled_coupon_status_map_uses_only_selected_closing_movements(monkeypatch):
    reader = ClippMvaReader(
        ClippMvaConnectionSettings(
            host="server",
            database="database",
            user="user",
            password="password",
        )
    )
    connection = _CancelledCouponConnection()
    monkeypatch.setattr(reader, "_connect", lambda: connection)

    cancelled = reader.build_cancelled_coupon_status_map(
        {
            "fechamento_janelas": [
                {"id_movimento": 1235},
                {"id_movimento": "1236"},
                {"id_movimento": "invalid"},
            ]
        }
    )

    assert connection.cursor_instance.params == (1235, 1236)
    assert cancelled == {
        "000399973": {
            "numero": "000399973",
            "numero_exibicao": "399973",
            "valor": 111.0,
            "cancelada": True,
            "status_codigo": 135,
            "emissao": "02/09/2026 10:00:54",
            "origem": "clipp_direto_mva",
        },
        "000399988": {
            "numero": "000399988",
            "numero_exibicao": "399988",
            "valor": 19.75,
            "cancelada": True,
            "status_codigo": 135,
            "emissao": "02/09/2026 11:18:31",
            "origem": "clipp_direto_mva",
        },
    }

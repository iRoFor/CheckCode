#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Каталог кодов ОКРБ + ТН ВЭД 5.0 — PyQt6 + SQLite3 + PyMuPDF (+ openpyxl).

Установка:
    pip install "PyQt6>=6.5" "PyMuPDF>=1.24" openpyxl
Запуск:
    python okrb_app.py
Самотест:
    python okrb_app.py --selftest

Вкладка «ОКРБ · постановления»:
  okrb_catalog / okrb_mentions / okrb_positions / okrb_decisions
  явно полностью -> ДА, подкоды ДА (по группе)
  явно частично  -> ЧАСТИЧНО + позиции, подкоды ТРЕБУЕТ ПРОВЕРКИ
  решение        -> ДА (по решению) / НЕ ВХОДИТ (проверено)
  подкод наверх не наследуется

Вкладка «ТН ВЭД · каталог»:
  tnved_catalog / tnved_groups
  Иерархия строится по кодам переменной длины (4/6/8/9/10 цифр),
  строки без кода дают контекст, тире задают уровень, есть признак
  прослеживаемости. Старый формат со стрелками тоже читается.
"""
from __future__ import annotations

import csv
import io
import json
import logging
import os
import re
import sqlite3
import sys
import traceback
import unicodedata
from dataclasses import dataclass, field
from datetime import date, datetime
from itertools import islice
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple

from PyQt6.QtCore import Qt, QThread, QTimer, pyqtSignal
from PyQt6.QtGui import QAction, QBrush, QColor, QFont, QKeySequence, QShortcut
from PyQt6.QtWidgets import (
    QAbstractItemView, QApplication, QCheckBox, QComboBox, QDialog, QDialogButtonBox,
    QFileDialog, QFormLayout, QGroupBox, QHBoxLayout, QHeaderView, QLabel, QLineEdit,
    QMainWindow, QMenu, QMessageBox, QProgressDialog, QPushButton, QScrollArea,
    QSpinBox, QTabWidget, QTableWidget, QTableWidgetItem, QTextEdit, QVBoxLayout, QWidget,
)

try:
    import pymupdf as fitz
except ImportError:
    try:
        import fitz
    except ImportError:
        fitz = None

try:
    import openpyxl
    from openpyxl.utils import get_column_letter
except ImportError:
    openpyxl = None

    def get_column_letter(idx: int) -> str:
        s = ""
        while idx > 0:
            idx, r = divmod(idx - 1, 26)
            s = chr(65 + r) + s
        return s or "A"


APP_NAME = "ОКРБ + ТН ВЭД"
APP_VERSION = "5.0"
DB_FILENAME = "okrb_catalog.db"
UI_FILENAME = "okrb_ui.json"
PAGE_SIZE = 100
PREVIEW_ROWS = 300

DOC_FLAGS: Tuple[str, ...] = ("in_decree_80", "in_168_app1", "in_168_app2", "in_168_app3")
DOC_TITLES = {
    "in_decree_80": "Пост. 80",
    "in_168_app1": "Пост. 168, Прил. 1",
    "in_168_app2": "Пост. 168, Прил. 2",
    "in_168_app3": "Пост. 168, Прил. 3",
}
DOC_SHORT = {
    "in_decree_80": "Пост. 80",
    "in_168_app1": "168 / Прил. 1",
    "in_168_app2": "168 / Прил. 2",
    "in_168_app3": "168 / Прил. 3",
}
BASIS_COL = {
    "in_decree_80": "basis_80",
    "in_168_app1": "basis_168_app1",
    "in_168_app2": "basis_168_app2",
    "in_168_app3": "basis_168_app3",
}

F_NONE, F_FULL, F_PARTIAL, F_FULL_INH, F_CHECK, F_DEC_IN, F_DEC_OUT = 0, 1, 2, 3, 4, 5, 6
FLAG_LABEL = {
    F_NONE: "нет", F_FULL: "да", F_PARTIAL: "частично", F_FULL_INH: "да (по группе)",
    F_CHECK: "требует проверки", F_DEC_IN: "да (по решению)", F_DEC_OUT: "не входит (проверено)",
}
INCLUDED = (F_FULL, F_PARTIAL, F_FULL_INH, F_DEC_IN)
DECIDABLE = (F_CHECK, F_DEC_IN, F_DEC_OUT)

M_FULL, M_PARTIAL = 1, 2
K_IN, K_OUT = 1, 2
D_NONE, D_IN, D_OUT = 0, 1, 2

FLT_ANY, FLT_IN, FLT_EXPLICIT, FLT_PARTIAL, FLT_CHECK, FLT_OUT, FLT_DEC_IN, FLT_DEC_OUT = \
    -1, 1, 2, 3, 4, 5, 6, 7

ROLE_CODE = Qt.ItemDataRole.UserRole
ROLE_POS = Qt.ItemDataRole(Qt.ItemDataRole.UserRole.value + 1)
ROLE_TYPE = Qt.ItemDataRole(Qt.ItemDataRole.UserRole.value + 2)
ROLE_REF = Qt.ItemDataRole(Qt.ItemDataRole.UserRole.value + 3)

LETTERS_RE = re.compile(r"[A-Za-zА-Яа-яЁё]")
EXCEPT_RE = re.compile(r"за\s+исключением\s*:?\s*", re.IGNORECASE)
TNVED_GROUP_RE = re.compile(r"^\s*группа\s*(\d{1,2})\s*[.:]?\s*(.*)$", re.IGNORECASE)
TNVED_DASH_ORDS = {0x002D, 0x2010, 0x2011, 0x2012, 0x2013, 0x2014, 0x2015, 0x2212}
TNVED_SEP_ORDS = {0x203A, 0x2039, 0x25B6, 0x25BA, 0x25B8,
                  0x2794, 0x279C, 0x27A4, 0x2022, 0x25CF}
TNVED_PROTECT_ORDS = {0x2116, 0x00B0, 0x20AC, 0x0024, 0x00B1, 0x00D7,
                      0x00F7, 0x2030, 0x00A9, 0x00AE, 0x2122, 0x00B5}
TNVED_LENGTHS = {2, 4, 6, 8, 9, 10}

INK = "#16233A"
MUTED = "#5A6B85"
ACCENT = "#2563EB"
DEEP = "#1F3A6D"
TEAL = "#0B7285"

STATUS_FG = {
    "full": "#0E7C5A", "inh": "#0B7285", "part": "#B45309", "check": "#6D28D9",
    "decin": "#0F766E", "decout": "#B4232A", "none": "#7A8AA3",
}
STATUS_BG = {
    "full": "#E6F6EF", "inh": "#E3F4F7", "part": "#FDF3E2", "check": "#F1EBFD",
    "decin": "#E4F5F2", "decout": "#FDECEC", "none": "#F2F5FA",
}
LEGEND_FG = {
    "full": "#6EE7B7", "inh": "#67E8F9", "part": "#FCD34D", "check": "#C4B5FD",
    "decin": "#5EEAD4", "decout": "#FCA5A5", "none": "#9FB2CE",
}
SUB_BG = {"in": "#EDF9F3", "out": "#FDECEC", "calc": "#F7F4ED",
          "ref": "#EEF3FB", "dec": "#F3EFFB"}

APP_QSS = f"""
QWidget {{ background: #F4F7FC; color: {INK};
    font-family: 'Segoe UI', 'Inter', sans-serif; font-size: 13px; }}
QMainWindow, QDialog {{ background: #F4F7FC; }}
QLabel {{ background: transparent; }}
QLineEdit, QComboBox, QSpinBox, QTextEdit {{
    background: #FFFFFF; border: 1px solid #CBD5E1; border-radius: 7px; padding: 5px 9px;
    selection-background-color: {ACCENT}; selection-color: #FFFFFF; }}
QLineEdit:focus, QComboBox:focus, QSpinBox:focus, QTextEdit:focus {{ border: 1px solid {ACCENT}; }}
QComboBox::drop-down {{ border: none; width: 22px; }}
QComboBox::down-arrow {{ width: 0; height: 0; margin-right: 8px;
    border-left: 4px solid transparent; border-right: 4px solid transparent;
    border-top: 5px solid {MUTED}; }}
QComboBox QAbstractItemView {{ background: #FFFFFF; border: 1px solid #CBD5E1;
    selection-background-color: #DCE7FF; selection-color: {INK}; }}
QPushButton {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {DEEP}, stop:1 #16233A);
    color: #EAF0FB; border: none; border-radius: 8px; padding: 8px 14px; font-weight: 600; }}
QPushButton:hover {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {ACCENT}, stop:1 {DEEP}); }}
QPushButton:pressed {{ background: #142A4E; }}
QPushButton:disabled {{ background: #C7D2E0; color: #EEF2F7; }}
QCheckBox {{ background: transparent; spacing: 7px; }}
QCheckBox::indicator {{ width: 16px; height: 16px; border-radius: 4px;
    border: 1px solid #A9B8CE; background: #FFFFFF; }}
QCheckBox::indicator:checked {{ background: {ACCENT}; border-color: {ACCENT}; }}
QGroupBox {{ background: #FFFFFF; border: 1px solid #D5DDEA; border-radius: 10px;
    margin-top: 12px; padding: 14px 10px 10px 10px; }}
QGroupBox::title {{ subcontrol-origin: margin; left: 14px; padding: 0 6px;
    color: {ACCENT}; font-weight: 700; }}
QTabWidget::pane {{ border: 1px solid #D5DDEA; border-radius: 10px; background: #FFFFFF; top: -1px; }}
QTabBar::tab {{ background: #E4EAF4; color: {MUTED}; padding: 9px 20px;
    border-top-left-radius: 9px; border-top-right-radius: 9px; margin-right: 3px; font-weight: 600; }}
QTabBar::tab:selected {{ background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 {DEEP}, stop:1 {TEAL});
    color: #FFFFFF; }}
QTableWidget, QTableView {{ background: #FFFFFF; alternate-background-color: #F7F9FD;
    gridline-color: #E5EAF3; border: 1px solid #D5DDEA; border-radius: 10px;
    selection-background-color: #DCE7FF; selection-color: {INK}; }}
QHeaderView {{ background: transparent; }}
QHeaderView::section {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 #24365E, stop:1 #16233A);
    color: #E8EEF9; padding: 9px 10px; border: none; border-right: 1px solid #35486F; font-weight: 600; }}
QHeaderView::section:hover {{ background: #2E4577; }}
QHeaderView::section:last {{ border-right: none; }}
QTableCornerButton::section {{ background: #16233A; border: none; }}
QScrollBar:vertical {{ background: #E9EEF7; width: 12px; margin: 3px; border-radius: 6px; }}
QScrollBar::handle:vertical {{ background: #9FB2CE; border-radius: 6px; min-height: 34px; }}
QScrollBar::handle:vertical:hover {{ background: {ACCENT}; }}
QScrollBar:horizontal {{ background: #E9EEF7; height: 12px; margin: 3px; border-radius: 6px; }}
QScrollBar::handle:horizontal {{ background: #9FB2CE; border-radius: 6px; min-width: 34px; }}
QScrollBar::handle:horizontal:hover {{ background: {TEAL}; }}
QScrollBar::add-line, QScrollBar::sub-line {{ width: 0; height: 0; }}
QScrollBar::add-page, QScrollBar::sub-page {{ background: transparent; }}
QMenuBar {{ background: #16233A; color: #DCE4F2; padding: 3px 6px; }}
QMenuBar::item {{ background: transparent; padding: 6px 12px; border-radius: 6px; }}
QMenuBar::item:selected {{ background: {ACCENT}; color: #FFFFFF; }}
QMenu {{ background: #FFFFFF; border: 1px solid #CBD5E1; border-radius: 8px; padding: 6px; }}
QMenu::item {{ padding: 7px 22px 7px 14px; border-radius: 6px; }}
QMenu::item:selected {{ background: #DCE7FF; color: {INK}; }}
QMenu::separator {{ height: 1px; background: #E2E8F2; margin: 5px 8px; }}
QStatusBar {{ background: #E9EEF7; color: {MUTED}; }}
QScrollArea {{ border: none; background: transparent; }}
"""


# ---------------------------------------------------------------------------
# Утилиты
# ---------------------------------------------------------------------------
def app_dir() -> Path:
    base = Path(sys.executable if getattr(sys, "frozen", False) else __file__).resolve().parent
    try:
        probe = base / ".okrb_write_test"
        probe.write_text("ok", encoding="utf-8")
        probe.unlink()
        return base
    except OSError:
        root = os.environ.get("APPDATA") or str(Path.home() / ".local" / "share")
        d = Path(root) / "OkrbCatalog"
        d.mkdir(parents=True, exist_ok=True)
        return d


APP_DIR = app_dir()
UI_PATH = APP_DIR / UI_FILENAME
_UI_STATE: Dict = {}
_UI_LOADED = False


def setup_logging() -> None:
    try:
        logging.basicConfig(filename=str(APP_DIR / "okrb_app.log"), level=logging.INFO,
                            format="%(asctime)s %(levelname)s %(message)s", encoding="utf-8")
    except Exception:
        logging.basicConfig(level=logging.INFO)


def ui_state() -> Dict:
    global _UI_STATE, _UI_LOADED
    if not _UI_LOADED:
        _UI_LOADED = True
        try:
            _UI_STATE = json.loads(UI_PATH.read_text(encoding="utf-8"))
            if not isinstance(_UI_STATE, dict):
                _UI_STATE = {}
        except Exception:
            _UI_STATE = {}
    return _UI_STATE


def save_ui_state() -> None:
    try:
        UI_PATH.write_text(json.dumps(ui_state(), ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception as e:
        logging.warning("Не удалось сохранить настройки интерфейса: %s", e)


def norm_text(s: Optional[str]) -> str:
    return re.sub(r"\s+", " ", s or "").strip().lower().replace("ё", "е")


def like_pattern(s: str) -> str:
    esc = s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
    return f"%{esc}%"


def has_letters(s: str) -> bool:
    return bool(LETTERS_RE.search(s or ""))


def chunks(seq: Sequence, size: int = 400):
    for i in range(0, len(seq), size):
        yield seq[i:i + size]


def is_code_shape(token: str, min_groups: int = 2) -> bool:
    g = (token or "").split(".")
    if len(g) == 1:
        return min_groups <= 1 and g[0].isdigit() and len(g[0]) == 2
    if not (min_groups <= len(g) <= 4):
        return False
    for i, part in enumerate(g):
        if not part.isdigit():
            return False
        if i < len(g) - 1:
            if len(part) != 2:
                return False
        elif not (1 <= len(part) <= 3):
            return False
    return True


def normalize_code(code: str) -> str:
    return re.sub(r"\s+", "", code or "")


def code_prefixes(code: str) -> List[str]:
    out: List[str] = []
    for i in range(2, len(code)):
        p = code[:i]
        if p.endswith("."):
            continue
        if is_code_shape(p, min_groups=1):
            out.append(p)
    return out


def expand_okrb_code(code: str) -> List[str]:
    code = normalize_code(code)
    if not is_code_shape(code, min_groups=1):
        return [code]
    return code_prefixes(code) + [code]


# --- ТН ВЭД: коды, уровни, разделители -------------------------------------
def normalize_tnved(code: str) -> str:
    return re.sub(r"\D", "", code or "")


def tnved_shape(code: str) -> bool:
    c = code or ""
    return c.isdigit() and len(c) in TNVED_LENGTHS


def format_tnved(code: str) -> str:
    c = code or ""
    n = len(c)
    if n == 10:
        return f"{c[:4]} {c[4:6]} {c[6:9]} {c[9:]}"
    if n == 9:
        return f"{c[:4]} {c[4:6]} {c[6:9]}"
    if n == 8:
        return f"{c[:4]} {c[4:6]} {c[6:8]}"
    if n == 6:
        return f"{c[:4]} {c[4:6]}"
    return c


def tnved_dash_level(text: str) -> int:
    n = 0
    for ch in (text or "").lstrip():
        if ord(ch) in TNVED_DASH_ORDS:
            n += 1
        elif ch.isspace():
            continue
        else:
            break
    return n


def strip_tnved_dashes(text: str) -> str:
    s = (text or "").lstrip()
    i = 0
    while i < len(s) and (ord(s[i]) in TNVED_DASH_ORDS or s[i].isspace()):
        i += 1
    return re.sub(r"\s+", " ", s[i:]).strip()


def split_tnved_name(raw: str) -> Tuple[str, str]:
    """Делит наименование по символу-стрелке (старый формат файла)."""
    s = re.sub(r"\s+", " ", raw or "").strip()
    if not s:
        return "", ""
    seps: List[str] = []
    for ch in sorted(set(s)):
        o = ord(ch)
        if o in TNVED_SEP_ORDS:
            seps.append(ch)
            continue
        if o in TNVED_PROTECT_ORDS or ch.isalnum() or ch.isspace():
            continue
        cat = unicodedata.category(ch)
        if cat and cat[0] in "PZC":
            continue
        if (o > 0xFFFF or 0x2190 <= o <= 0x21FF or 0x27F0 <= o <= 0x27FF
                or 0x2900 <= o <= 0x297F or 0x1F300 <= o <= 0x1FAFF
                or cat in ("So", "Sk") or "ARROW" in unicodedata.name(ch, "")):
            seps.append(ch)
    parts = re.split("[" + re.escape("".join(seps)) + "]", s) if seps else [s]
    parts = [p.strip(" :;,.-") for p in parts]
    parts = [p for p in parts if p]
    if not parts:
        return s, s
    return " \u203a ".join(parts), parts[-1]


def tnved_arrow_parts(raw: str) -> List[str]:
    full, _tail = split_tnved_name(raw)
    return [p.strip() for p in full.split("\u203a") if p.strip()]


# ---------------------------------------------------------------------------
# Настраиваемые колонки
# ---------------------------------------------------------------------------
class TableColumns:
    def __init__(self, table: QTableWidget, key: str, defaults: Sequence[int],
                 min_width: int = 46) -> None:
        self.table, self.key = table, key
        self.defaults, self.min_width = list(defaults), min_width
        hh = table.horizontalHeader()
        hh.setSectionResizeMode(QHeaderView.ResizeMode.Interactive)
        hh.setStretchLastSection(False)
        hh.setSectionsClickable(True)
        hh.setHighlightSections(False)
        hh.setMinimumSectionSize(min_width)
        hh.setDefaultAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        hh.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        hh.customContextMenuRequested.connect(self._menu)
        table.setHorizontalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        table.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        table.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        table.setTextElideMode(Qt.TextElideMode.ElideRight)
        table.setWordWrap(False)
        self._timer = QTimer(table)
        self._timer.setSingleShot(True)
        self._timer.setInterval(350)
        self._timer.timeout.connect(self.save)
        hh.sectionResized.connect(lambda *_a: self._timer.start())
        self.apply()

    def _stored(self) -> Dict:
        return ui_state().setdefault("tables", {}).get(self.key, {}) or {}

    def apply(self) -> None:
        st = self._stored()
        widths, hidden = st.get("widths") or [], set(st.get("hidden") or [])
        for c in range(self.table.columnCount()):
            w = widths[c] if c < len(widths) and isinstance(widths[c], int) else (
                self.defaults[c] if c < len(self.defaults) else 150)
            self.table.setColumnWidth(c, max(self.min_width, int(w)))
            self.table.setColumnHidden(c, c in hidden)
        self._ensure_visible()

    def save(self) -> None:
        ui_state().setdefault("tables", {})[self.key] = {
            "widths": [self.table.columnWidth(c) for c in range(self.table.columnCount())],
            "hidden": [c for c in range(self.table.columnCount()) if self.table.isColumnHidden(c)],
        }
        save_ui_state()

    def reset(self) -> None:
        for c in range(self.table.columnCount()):
            w = self.defaults[c] if c < len(self.defaults) else 150
            self.table.setColumnWidth(c, max(self.min_width, int(w)))
            self.table.setColumnHidden(c, False)
        self.save()

    def autofit(self, col: int, sample: int = 500, pad: int = 26, max_w: int = 700) -> None:
        if not (0 <= col < self.table.columnCount()):
            return
        fm = self.table.fontMetrics()
        head = self.table.horizontalHeaderItem(col)
        widest = fm.horizontalAdvance(head.text() if head else "") + 34
        for r in range(min(self.table.rowCount(), sample)):
            it = self.table.item(r, col)
            if it is not None and it.text():
                widest = max(widest, fm.horizontalAdvance(it.text()))
        self.table.setColumnWidth(col, max(self.min_width + 24, min(max_w, widest + pad)))
        self.save()

    def autofit_all(self) -> None:
        for c in range(self.table.columnCount()):
            if not self.table.isColumnHidden(c):
                self.autofit(c)

    def _ensure_visible(self) -> None:
        n = self.table.columnCount()
        if n and all(self.table.isColumnHidden(c) for c in range(n)):
            self.table.setColumnHidden(0, False)

    def set_hidden(self, col: int, hidden: bool) -> None:
        self.table.setColumnHidden(col, hidden)
        self._ensure_visible()
        self.save()

    def _menu(self, pos) -> None:
        hh = self.table.horizontalHeader()
        col = hh.logicalIndexAt(pos)
        m = QMenu(self.table)
        if col >= 0:
            m.addAction("Подогнать эту колонку").triggered.connect(lambda: self.autofit(col))
        m.addAction("Подогнать все колонки").triggered.connect(self.autofit_all)
        m.addAction("Сбросить ширины и видимость").triggered.connect(self.reset)
        m.addSeparator()
        visible = [c for c in range(self.table.columnCount()) if not self.table.isColumnHidden(c)]
        for c in range(self.table.columnCount()):
            head = self.table.horizontalHeaderItem(c)
            title = (head.text() if head and head.text() else f"Колонка {c+1}").strip()
            act = m.addAction(title[:48] or f"Колонка {c+1}")
            act.setCheckable(True)
            act.setChecked(not self.table.isColumnHidden(c))
            act.setEnabled(not (c in visible and len(visible) == 1))
            act.toggled.connect(lambda on, cc=c: self.set_hidden(cc, not on))
        m.exec(hh.mapToGlobal(pos))


# ---------------------------------------------------------------------------
# Модель
# ---------------------------------------------------------------------------
@dataclass
class Position:
    id: int
    code: str
    doc: str
    kind: int
    name: str
    page: int = 0
    source_file: str = ""


@dataclass
class Decision:
    id: int
    code: str
    doc: str
    verdict: int
    reason: str = ""
    decided_at: str = ""


@dataclass
class OkrbRecord:
    okrb_code: str
    product_name: str = ""
    flags: Dict[str, int] = field(default_factory=dict)
    basis: Dict[str, str] = field(default_factory=dict)
    children_included: int = 0

    def flag(self, doc: str) -> int:
        return int(self.flags.get(doc, 0))

    def inclusion_text(self) -> str:
        parts: List[str] = []
        v = self.flag("in_decree_80")
        if v:
            parts.append(f"Пост. 80: {FLAG_LABEL[v]}")
        apps = [f"{n} — {FLAG_LABEL[self.flag(d)]}"
                for n, d in ((1, "in_168_app1"), (2, "in_168_app2"), (3, "in_168_app3"))
                if self.flag(d)]
        if apps:
            parts.append("Пост. 168 (Прил. " + ", ".join(apps) + ")")
        return "; ".join(parts) if parts else "Не найдено в реестрах"

    def basis_text(self) -> str:
        return "; ".join(f"{DOC_SHORT[d]}: {self.basis[d]}" for d in DOC_FLAGS if self.basis.get(d))

    def partial_docs(self) -> List[str]:
        return [d for d in DOC_FLAGS if self.flag(d) == F_PARTIAL]

    def decidable_docs(self) -> List[str]:
        return [d for d in DOC_FLAGS if self.flag(d) in DECIDABLE]

    def nowhere(self) -> bool:
        return not any(self.flag(d) for d in DOC_FLAGS)

    def status(self) -> str:
        vals = [self.flag(d) for d in DOC_FLAGS]
        for v, key in ((F_FULL, "full"), (F_FULL_INH, "inh"), (F_DEC_IN, "decin"),
                       (F_PARTIAL, "part"), (F_CHECK, "check"), (F_DEC_OUT, "decout")):
            if v in vals:
                return key
        return "none"


@dataclass
class ParsedItem:
    code: str
    name: str
    partial: bool
    page: int = 0
    source: str = "текст"


@dataclass
class ParseResult:
    items: List[ParsedItem] = field(default_factory=list)
    pages: int = 0
    text_chars: int = 0
    tables: int = 0
    warnings: List[str] = field(default_factory=list)
    cancelled: bool = False


@dataclass
class PdfImportRow:
    code: str
    text: str
    doc: str
    mode: int
    kind: int = K_IN
    page: int = 0
    source: str = ""
    file: str = ""
    exists: bool = False


@dataclass
class CatalogRow:
    code: str
    name: str
    sheet: str
    row_no: int
    note: str = ""


@dataclass
class TnvedRow:
    code: str
    name: str
    sheet: str = ""
    row_no: int = 0
    dashes: int = 0
    ctx: List[Tuple[int, str]] = field(default_factory=list)
    path: str = ""
    grp: str = ""
    depth: int = 0
    parent: str = ""
    traceable: int = 0
    ord: int = 0
    note: str = ""


@dataclass
class TnvedRecord:
    code: str
    name: str
    path: str
    grp: str
    depth: int
    digits: int
    parent: str
    traceable: int
    grp_name: str = ""


@dataclass
class PdfSection:
    start_page: int
    end_page: int
    doc: Optional[str]
    title: str = ""

    def label(self) -> str:
        return DOC_TITLES.get(self.doc, "вне приложений")

    def pages_text(self) -> str:
        return f"{self.start_page}–{self.end_page}"


# ---------------------------------------------------------------------------
# База данных
# ---------------------------------------------------------------------------
class DatabaseManager:
    ORDER = {"code": "c.okrb_code", "name": "c.product_name_lc"}

    def __init__(self, db_path: str | Path) -> None:
        self.db_path = str(db_path)
        self.migrated_from_old = False
        try:
            self.conn = sqlite3.connect(self.db_path)
            self.conn.row_factory = sqlite3.Row
            self.conn.execute("PRAGMA journal_mode=WAL")
            self.conn.execute("PRAGMA synchronous=NORMAL")
        except sqlite3.Error as e:
            raise RuntimeError(f"Не удалось открыть базу «{self.db_path}»: {e}") from e
        self._init_schema()

    def _init_schema(self) -> None:
        try:
            with self.conn:
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS okrb_catalog (
                        okrb_code TEXT PRIMARY KEY,
                        product_name TEXT NOT NULL DEFAULT '',
                        product_name_lc TEXT NOT NULL DEFAULT '',
                        in_decree_80 INTEGER NOT NULL DEFAULT 0,
                        in_168_app1 INTEGER NOT NULL DEFAULT 0,
                        in_168_app2 INTEGER NOT NULL DEFAULT 0,
                        in_168_app3 INTEGER NOT NULL DEFAULT 0,
                        basis_80 TEXT NOT NULL DEFAULT '',
                        basis_168_app1 TEXT NOT NULL DEFAULT '',
                        basis_168_app2 TEXT NOT NULL DEFAULT '',
                        basis_168_app3 TEXT NOT NULL DEFAULT '',
                        children_included INTEGER NOT NULL DEFAULT 0
                    )""")
                cols = {r["name"] for r in self.conn.execute("PRAGMA table_info(okrb_catalog)")}
                for c in ("product_name_lc", "basis_80", "basis_168_app1", "basis_168_app2",
                          "basis_168_app3", "children_included"):
                    if c not in cols:
                        if c == "children_included":
                            self.conn.execute(f"ALTER TABLE okrb_catalog ADD COLUMN {c} INTEGER NOT NULL DEFAULT 0")
                        else:
                            self.conn.execute(f"ALTER TABLE okrb_catalog ADD COLUMN {c} TEXT NOT NULL DEFAULT ''")
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS okrb_mentions (
                        okrb_code TEXT NOT NULL, doc TEXT NOT NULL, mode INTEGER NOT NULL,
                        PRIMARY KEY (okrb_code, doc))""")
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS okrb_positions (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        okrb_code TEXT NOT NULL, doc TEXT NOT NULL,
                        kind INTEGER NOT NULL DEFAULT 1,
                        product_name TEXT NOT NULL DEFAULT '',
                        product_name_lc TEXT NOT NULL DEFAULT '',
                        page INTEGER NOT NULL DEFAULT 0,
                        source_file TEXT NOT NULL DEFAULT '')""")
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS okrb_decisions (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        okrb_code TEXT NOT NULL, doc TEXT NOT NULL,
                        verdict INTEGER NOT NULL,
                        reason TEXT NOT NULL DEFAULT '',
                        decided_at TEXT NOT NULL DEFAULT '',
                        UNIQUE (okrb_code, doc))""")
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS tnved_catalog (
                        code TEXT PRIMARY KEY,
                        name TEXT NOT NULL DEFAULT '',
                        name_lc TEXT NOT NULL DEFAULT '',
                        path TEXT NOT NULL DEFAULT '',
                        path_lc TEXT NOT NULL DEFAULT '',
                        tail TEXT NOT NULL DEFAULT '',
                        tail_lc TEXT NOT NULL DEFAULT '',
                        grp TEXT NOT NULL DEFAULT '',
                        dashes INTEGER NOT NULL DEFAULT 0,
                        depth INTEGER NOT NULL DEFAULT 0,
                        digits INTEGER NOT NULL DEFAULT 0,
                        parent TEXT NOT NULL DEFAULT '',
                        traceable INTEGER NOT NULL DEFAULT 0,
                        ord INTEGER NOT NULL DEFAULT 0
                    )""")
                self.conn.execute("""
                    CREATE TABLE IF NOT EXISTS tnved_groups (
                        grp TEXT PRIMARY KEY, name TEXT NOT NULL DEFAULT '')""")
                tcols = {r["name"] for r in self.conn.execute("PRAGMA table_info(tnved_catalog)")}
                for c, typ, dflt in (("path", "TEXT", "''"), ("path_lc", "TEXT", "''"),
                                     ("tail", "TEXT", "''"), ("tail_lc", "TEXT", "''"),
                                     ("grp", "TEXT", "''"), ("dashes", "INTEGER", "0"),
                                     ("depth", "INTEGER", "0"), ("digits", "INTEGER", "0"),
                                     ("parent", "TEXT", "''"), ("traceable", "INTEGER", "0"),
                                     ("ord", "INTEGER", "0")):
                    if c not in tcols:
                        self.conn.execute(
                            f"ALTER TABLE tnved_catalog ADD COLUMN {c} {typ} NOT NULL DEFAULT {dflt}")
                for sql in (
                    "CREATE INDEX IF NOT EXISTS idx_pos_code ON okrb_positions(okrb_code)",
                    "CREATE INDEX IF NOT EXISTS idx_pos_lc ON okrb_positions(product_name_lc)",
                    "CREATE UNIQUE INDEX IF NOT EXISTS idx_pos_uniq ON okrb_positions(okrb_code, doc, kind, product_name_lc)",
                    "CREATE INDEX IF NOT EXISTS idx_name_lc ON okrb_catalog(product_name_lc)",
                    "CREATE INDEX IF NOT EXISTS idx_dec_code ON okrb_decisions(okrb_code)",
                    "CREATE INDEX IF NOT EXISTS idx_tnved_lc ON tnved_catalog(name_lc)",
                    "CREATE INDEX IF NOT EXISTS idx_tnved_path ON tnved_catalog(path_lc)",
                    "CREATE INDEX IF NOT EXISTS idx_tnved_grp ON tnved_catalog(grp)",
                    "CREATE INDEX IF NOT EXISTS idx_tnved_digits ON tnved_catalog(digits)",
                ):
                    self.conn.execute(sql)

                fixes = []
                for r in self.conn.execute("SELECT okrb_code, product_name, product_name_lc FROM okrb_catalog"):
                    want = norm_text(r["product_name"])
                    if (r["product_name_lc"] or "") != want:
                        fixes.append((want, r["okrb_code"]))
                if fixes:
                    self.conn.executemany("UPDATE okrb_catalog SET product_name_lc=? WHERE okrb_code=?", fixes)

                ver = int(self.conn.execute("PRAGMA user_version").fetchone()[0])
                if ver < 3:
                    old = self.conn.execute(
                        "SELECT COUNT(*) FROM okrb_catalog WHERE in_decree_80<>0 OR in_168_app1<>0 "
                        "OR in_168_app2<>0 OR in_168_app3<>0").fetchone()[0]
                    ment = self.conn.execute("SELECT COUNT(*) FROM okrb_mentions").fetchone()[0]
                    if old and not ment:
                        self.conn.execute(
                            "UPDATE okrb_catalog SET in_decree_80=0, in_168_app1=0, in_168_app2=0, "
                            "in_168_app3=0, basis_80='', basis_168_app1='', basis_168_app2='', "
                            "basis_168_app3='', children_included=0")
                        self.migrated_from_old = True
                if ver < 5:
                    self._migrate_tnved()
                    self.conn.execute("PRAGMA user_version=5")
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка инициализации базы: {e}") from e

    def _migrate_tnved(self) -> None:
        """Старый формат: name = полный путь, tail = последняя часть."""
        rows = self.conn.execute(
            "SELECT code, name, tail, path FROM tnved_catalog").fetchall()
        if not rows:
            return
        need = [r for r in rows if not (r["path"] or "")]
        if not need:
            return
        objs: List[TnvedRow] = []
        for r in need:
            code = r["code"]
            own = (r["tail"] or "") or r["name"] or ""
            objs.append(TnvedRow(code=code, name=own, dashes=0, grp=code[:2]))
        build_tnved_paths(objs)
        params = [(o.path, norm_text(o.path), o.name, norm_text(o.name), o.depth,
                   len(o.code), o.parent, o.code[:2], o.code) for o in objs]
        self.conn.executemany(
            """UPDATE tnved_catalog SET path=?, path_lc=?, name=?, name_lc=?, depth=?,
               digits=?, parent=?, grp=?, tail=name, tail_lc=name_lc WHERE code=?""", params)

    def _row(self, r: sqlite3.Row) -> OkrbRecord:
        return OkrbRecord(
            okrb_code=r["okrb_code"], product_name=r["product_name"] or "",
            flags={d: int(r[d] or 0) for d in DOC_FLAGS},
            basis={d: (r[BASIS_COL[d]] or "") for d in DOC_FLAGS},
            children_included=int(r["children_included"] or 0))

    # -- справочник ОКРБ -----------------------------------------------------
    def get(self, code: str) -> Optional[OkrbRecord]:
        r = self.conn.execute("SELECT * FROM okrb_catalog WHERE okrb_code=?", (code,)).fetchone()
        return self._row(r) if r else None

    def save_catalog(self, code: str, name: str, overwrite: bool = True) -> None:
        try:
            with self.conn:
                if overwrite:
                    self.conn.execute("""INSERT INTO okrb_catalog(okrb_code, product_name, product_name_lc)
                        VALUES(?,?,?) ON CONFLICT(okrb_code) DO UPDATE SET
                        product_name=excluded.product_name, product_name_lc=excluded.product_name_lc""",
                                      (code, name, norm_text(name)))
                else:
                    self.conn.execute("""INSERT INTO okrb_catalog(okrb_code, product_name, product_name_lc)
                        VALUES(?,?,?) ON CONFLICT(okrb_code) DO UPDATE SET
                        product_name=CASE WHEN TRIM(okrb_catalog.product_name)=''
                            THEN excluded.product_name ELSE okrb_catalog.product_name END,
                        product_name_lc=CASE WHEN TRIM(okrb_catalog.product_name)=''
                            THEN excluded.product_name_lc ELSE okrb_catalog.product_name_lc END""",
                                      (code, name, norm_text(name)))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка сохранения кода {code}: {e}") from e

    def rename_code(self, old: str, new: str) -> None:
        try:
            with self.conn:
                if self.get(new) is not None:
                    raise RuntimeError(f"Код {new} уже существует.")
                for t in ("okrb_catalog", "okrb_mentions", "okrb_positions", "okrb_decisions"):
                    self.conn.execute(f"UPDATE {t} SET okrb_code=? WHERE okrb_code=?", (new, old))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка переименования кода: {e}") from e

    def delete(self, code: str) -> bool:
        try:
            with self.conn:
                for t in ("okrb_mentions", "okrb_positions", "okrb_decisions"):
                    self.conn.execute(f"DELETE FROM {t} WHERE okrb_code=?", (code,))
                cur = self.conn.execute("DELETE FROM okrb_catalog WHERE okrb_code=?", (code,))
                return cur.rowcount > 0
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка удаления {code}: {e}") from e

    def existing_codes(self, codes: Sequence[str]) -> Set[str]:
        found: Set[str] = set()
        for part in chunks(list(dict.fromkeys(codes))):
            if not part:
                continue
            sql = "SELECT okrb_code FROM okrb_catalog WHERE okrb_code IN (%s)" % ",".join("?" * len(part))
            found.update(r["okrb_code"] for r in self.conn.execute(sql, list(part)))
        return found

    def mentions(self, code: str) -> Dict[str, int]:
        return {r["doc"]: int(r["mode"]) for r in
                self.conn.execute("SELECT doc, mode FROM okrb_mentions WHERE okrb_code=?", (code,))}

    def mentions_for(self, codes: Sequence[str]) -> Dict[str, Dict[str, int]]:
        out: Dict[str, Dict[str, int]] = {}
        for part in chunks(list(dict.fromkeys(codes))):
            if not part:
                continue
            sql = "SELECT okrb_code, doc, mode FROM okrb_mentions WHERE okrb_code IN (%s)" % ",".join("?" * len(part))
            for r in self.conn.execute(sql, list(part)):
                out.setdefault(r["okrb_code"], {})[r["doc"]] = int(r["mode"])
        return out

    def set_mentions(self, code: str, modes: Dict[str, int]) -> None:
        try:
            with self.conn:
                self.conn.execute("DELETE FROM okrb_mentions WHERE okrb_code=?", (code,))
                self.conn.executemany("INSERT INTO okrb_mentions(okrb_code, doc, mode) VALUES(?,?,?)",
                                      [(code, d, int(m)) for d, m in modes.items() if m])
                for d, m in modes.items():
                    if not m:
                        self.conn.execute("DELETE FROM okrb_positions WHERE okrb_code=? AND doc=?", (code, d))
                        self.conn.execute("DELETE FROM okrb_decisions WHERE okrb_code=? AND doc=?", (code, d))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка сохранения отметок {code}: {e}") from e

    def partial_ancestors(self, codes: Sequence[str]) -> Dict[str, Dict[str, str]]:
        prefs: Dict[str, List[str]] = {}
        allp: Set[str] = set()
        for c in codes:
            p = code_prefixes(c)
            prefs[c] = p
            allp.update(p)
        ment = self.mentions_for(sorted(allp))
        out: Dict[str, Dict[str, str]] = {}
        for c, plist in prefs.items():
            m: Dict[str, str] = {}
            for d in DOC_FLAGS:
                for p in reversed(plist):
                    if ment.get(p, {}).get(d) == M_PARTIAL:
                        m[d] = p
                        break
            if m:
                out[c] = m
        return out

    def positions_for(self, codes: Sequence[str]) -> Dict[str, List[Position]]:
        out: Dict[str, List[Position]] = {}
        for part in chunks(list(dict.fromkeys(codes))):
            if not part:
                continue
            sql = ("SELECT * FROM okrb_positions WHERE okrb_code IN (%s) ORDER BY doc, kind, id"
                   % ",".join("?" * len(part)))
            for r in self.conn.execute(sql, list(part)):
                out.setdefault(r["okrb_code"], []).append(
                    Position(int(r["id"]), r["okrb_code"], r["doc"], int(r["kind"]),
                             r["product_name"] or "", int(r["page"] or 0), r["source_file"] or ""))
        return out

    def add_position(self, code: str, doc: str, kind: int, name: str,
                     page: int = 0, source_file: str = "") -> None:
        try:
            with self.conn:
                self.conn.execute("""INSERT OR IGNORE INTO okrb_positions
                    (okrb_code, doc, kind, product_name, product_name_lc, page, source_file)
                    VALUES(?,?,?,?,?,?,?)""",
                                  (code, doc, kind, name, norm_text(name), page, source_file))
                self.conn.execute("""INSERT INTO okrb_mentions(okrb_code, doc, mode) VALUES(?,?,2)
                    ON CONFLICT(okrb_code, doc) DO UPDATE SET mode=2""", (code, doc))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка добавления позиции: {e}") from e

    def update_position(self, pos_id: int, doc: str, kind: int, name: str, page: int) -> None:
        try:
            with self.conn:
                self.conn.execute("""UPDATE okrb_positions SET doc=?, kind=?, product_name=?,
                    product_name_lc=?, page=? WHERE id=?""",
                                  (doc, kind, name, norm_text(name), page, pos_id))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка изменения позиции: {e}") from e

    def delete_position(self, pos_id: int) -> None:
        try:
            with self.conn:
                self.conn.execute("DELETE FROM okrb_positions WHERE id=?", (pos_id,))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка удаления позиции: {e}") from e

    def decisions_for(self, codes: Sequence[str]) -> Dict[str, List[Decision]]:
        out: Dict[str, List[Decision]] = {}
        for part in chunks(list(dict.fromkeys(codes))):
            if not part:
                continue
            sql = "SELECT * FROM okrb_decisions WHERE okrb_code IN (%s) ORDER BY doc" % ",".join("?" * len(part))
            for r in self.conn.execute(sql, list(part)):
                out.setdefault(r["okrb_code"], []).append(
                    Decision(int(r["id"]), r["okrb_code"], r["doc"], int(r["verdict"]),
                             r["reason"] or "", r["decided_at"] or ""))
        return out

    def set_decision(self, code: str, doc: str, verdict: int, reason: str = "") -> None:
        try:
            with self.conn:
                if not verdict:
                    self.conn.execute("DELETE FROM okrb_decisions WHERE okrb_code=? AND doc=?", (code, doc))
                else:
                    self.conn.execute("""INSERT INTO okrb_decisions(okrb_code, doc, verdict, reason, decided_at)
                        VALUES(?,?,?,?,?) ON CONFLICT(okrb_code, doc) DO UPDATE SET
                        verdict=excluded.verdict, reason=excluded.reason, decided_at=excluded.decided_at""",
                                      (code, doc, int(verdict), reason,
                                       datetime.now().strftime("%Y-%m-%d %H:%M")))
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка сохранения решения: {e}") from e

    def _where(self, code_q: str, name_q: str, filters: Optional[Dict[str, int]],
               only_empty: bool, only_pos: bool) -> Tuple[str, List]:
        cl: List[str] = []
        pr: List = []
        cq = normalize_code(code_q)
        if cq:
            cl.append("c.okrb_code LIKE ? ESCAPE '\\'")
            pr.append(like_pattern(cq))
        nq = norm_text(name_q)
        if nq:
            pat = like_pattern(nq)
            cl.append("(c.product_name_lc LIKE ? ESCAPE '\\' OR EXISTS "
                      "(SELECT 1 FROM okrb_positions p WHERE p.okrb_code=c.okrb_code "
                      "AND p.product_name_lc LIKE ? ESCAPE '\\'))")
            pr += [pat, pat]
        for d in DOC_FLAGS:
            m = (filters or {}).get(d, FLT_ANY)
            if m == FLT_IN:
                cl.append(f"c.{d} IN (1,3,5)")
            elif m == FLT_EXPLICIT:
                cl.append(f"c.{d} IN (1,2)")
            elif m == FLT_PARTIAL:
                cl.append(f"c.{d} = 2")
            elif m == FLT_CHECK:
                cl.append(f"c.{d} = 4")
            elif m == FLT_OUT:
                cl.append(f"c.{d} IN (0,6)")
            elif m == FLT_DEC_IN:
                cl.append(f"c.{d} = 5")
            elif m == FLT_DEC_OUT:
                cl.append(f"c.{d} = 6")
        if only_empty:
            cl.append("TRIM(c.product_name)=''")
        if only_pos:
            cl.append("EXISTS (SELECT 1 FROM okrb_positions p WHERE p.okrb_code=c.okrb_code)")
        return (" WHERE " + " AND ".join(cl)) if cl else "", pr

    def search(self, code_q="", name_q="", filters=None, only_empty=False, only_pos=False,
               limit: Optional[int] = PAGE_SIZE, offset: int = 0,
               order_by="code", desc=False) -> List[OkrbRecord]:
        w, pr = self._where(code_q, name_q, filters, only_empty, only_pos)
        order = self.ORDER.get(order_by, "c.okrb_code")
        sql = f"SELECT c.* FROM okrb_catalog c{w} ORDER BY {order} {'DESC' if desc else 'ASC'}, c.okrb_code"
        if limit is not None:
            sql += " LIMIT ? OFFSET ?"
            pr = pr + [int(limit), int(offset)]
        try:
            return [self._row(r) for r in self.conn.execute(sql, pr)]
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка поиска: {e}") from e

    def count(self, code_q="", name_q="", filters=None, only_empty=False, only_pos=False) -> int:
        w, pr = self._where(code_q, name_q, filters, only_empty, only_pos)
        return int(self.conn.execute(f"SELECT COUNT(*) FROM okrb_catalog c{w}", pr).fetchone()[0])

    def count_all(self) -> int:
        return int(self.conn.execute("SELECT COUNT(*) FROM okrb_catalog").fetchone()[0])

    def import_pdf_rows(self, rows: List[PdfImportRow], reset_docs: Sequence[str] = (),
                        overwrite_names: bool = False) -> Tuple[int, int, int]:
        for d in reset_docs:
            if d not in DOC_FLAGS:
                raise ValueError(f"Неизвестный документ: {d}")
        try:
            codes = list(dict.fromkeys(r.code for r in rows))
            existing = self.existing_codes(codes)
            with self.conn:
                for d in reset_docs:
                    self.conn.execute("DELETE FROM okrb_mentions WHERE doc=?", (d,))
                    self.conn.execute("DELETE FROM okrb_positions WHERE doc=?", (d,))
                    self.conn.execute("DELETE FROM okrb_decisions WHERE doc=?", (d,))
                new_codes = [c for c in codes if c not in existing]
                self.conn.executemany(
                    "INSERT OR IGNORE INTO okrb_catalog(okrb_code, product_name, product_name_lc) "
                    "VALUES(?,'','')", [(c,) for c in new_codes])
                for r in rows:
                    if r.mode == M_FULL and r.text:
                        if overwrite_names:
                            self.conn.execute(
                                "UPDATE okrb_catalog SET product_name=?, product_name_lc=? WHERE okrb_code=?",
                                (r.text, norm_text(r.text), r.code))
                        else:
                            self.conn.execute(
                                "UPDATE okrb_catalog SET product_name=?, product_name_lc=? "
                                "WHERE okrb_code=? AND TRIM(product_name)=''",
                                (r.text, norm_text(r.text), r.code))
                self.conn.executemany(
                    """INSERT INTO okrb_mentions(okrb_code, doc, mode) VALUES(?,?,?)
                       ON CONFLICT(okrb_code, doc) DO UPDATE SET mode=MIN(mode, excluded.mode)""",
                    [(r.code, r.doc, r.mode) for r in rows])
                pos = [(r.code, r.doc, r.kind, r.text, norm_text(r.text), r.page, r.file)
                       for r in rows if r.mode == M_PARTIAL and r.text]
                self.conn.executemany(
                    """INSERT OR IGNORE INTO okrb_positions
                       (okrb_code, doc, kind, product_name, product_name_lc, page, source_file)
                       VALUES(?,?,?,?,?,?,?)""", pos)
            return len(new_codes), len(codes) - len(new_codes), len(pos)
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка импорта: {e}") from e

    def import_catalog(self, rows: List[CatalogRow], overwrite_names: bool) -> Tuple[int, int]:
        if not rows:
            return 0, 0
        codes = [r.code for r in rows]
        existing = self.existing_codes(codes)
        try:
            with self.conn:
                for part in chunks([(r.code, r.name, norm_text(r.name)) for r in rows], 500):
                    if overwrite_names:
                        self.conn.executemany(
                            """INSERT INTO okrb_catalog(okrb_code, product_name, product_name_lc)
                               VALUES(?,?,?) ON CONFLICT(okrb_code) DO UPDATE SET
                               product_name=excluded.product_name,
                               product_name_lc=excluded.product_name_lc""", part)
                    else:
                        self.conn.executemany(
                            """INSERT INTO okrb_catalog(okrb_code, product_name, product_name_lc)
                               VALUES(?,?,?) ON CONFLICT(okrb_code) DO UPDATE SET
                               product_name=CASE WHEN TRIM(okrb_catalog.product_name)=''
                                   THEN excluded.product_name ELSE okrb_catalog.product_name END,
                               product_name_lc=CASE WHEN TRIM(okrb_catalog.product_name)=''
                                   THEN excluded.product_name_lc ELSE okrb_catalog.product_name_lc END""",
                            part)
            new_cnt = sum(1 for c in codes if c not in existing)
            return new_cnt, len(codes) - new_cnt
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка загрузки классификатора: {e}") from e

    def recompute(self) -> Dict[str, int]:
        try:
            mentions: Dict[str, Dict[str, int]] = {}
            for r in self.conn.execute("SELECT okrb_code, doc, mode FROM okrb_mentions"):
                mentions.setdefault(r["okrb_code"], {})[r["doc"]] = int(r["mode"])
            decisions: Dict[str, Dict[str, int]] = {}
            for r in self.conn.execute("SELECT okrb_code, doc, verdict FROM okrb_decisions"):
                decisions.setdefault(r["okrb_code"], {})[r["doc"]] = int(r["verdict"])
            codes = [r[0] for r in self.conn.execute("SELECT okrb_code FROM okrb_catalog ORDER BY okrb_code")]
            counters: Dict[str, int] = {c: 0 for c in codes}
            results = []
            for code in codes:
                pref = code_prefixes(code)
                own = mentions.get(code, {})
                dec = decisions.get(code, {})
                vals: Dict[str, int] = {}
                bases: Dict[str, str] = {}
                for d in DOC_FLAGS:
                    o = own.get(d, 0)
                    if o == M_FULL:
                        v, b = F_FULL, "явно"
                    else:
                        anc_full = anc_part = None
                        for p in reversed(pref):
                            m = mentions.get(p, {}).get(d, 0)
                            if m == M_FULL:
                                anc_full = p
                                break
                            if m == M_PARTIAL and anc_part is None:
                                anc_part = p
                        if anc_full:
                            v, b = F_FULL_INH, f"группа {anc_full}"
                        elif o == M_PARTIAL:
                            v, b = F_PARTIAL, "явно"
                        elif anc_part:
                            dv = dec.get(d, D_NONE)
                            if dv == D_IN:
                                v, b = F_DEC_IN, f"решение по группе {anc_part}"
                            elif dv == D_OUT:
                                v, b = F_DEC_OUT, f"решение по группе {anc_part}"
                            else:
                                v, b = F_CHECK, f"группа {anc_part} (частично)"
                        else:
                            v, b = F_NONE, ""
                    vals[d] = v
                    bases[d] = b
                if any(vals[d] in INCLUDED for d in DOC_FLAGS):
                    for p in pref:
                        if p in counters:
                            counters[p] += 1
                results.append((code, vals, bases))
            with self.conn:
                self.conn.executemany(
                    """UPDATE okrb_catalog SET in_decree_80=?, in_168_app1=?, in_168_app2=?,
                       in_168_app3=?, basis_80=?, basis_168_app1=?, basis_168_app2=?,
                       basis_168_app3=?, children_included=? WHERE okrb_code=?""",
                    [(r[1]["in_decree_80"], r[1]["in_168_app1"], r[1]["in_168_app2"], r[1]["in_168_app3"],
                      r[2]["in_decree_80"], r[2]["in_168_app1"], r[2]["in_168_app2"], r[2]["in_168_app3"],
                      counters.get(r[0], 0), r[0]) for r in results])
            return {"codes": len(codes), "mentions": sum(len(v) for v in mentions.values()),
                    "decisions": sum(len(v) for v in decisions.values())}
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка пересчёта: {e}") from e

    # -- ТН ВЭД --------------------------------------------------------------
    def tnved_import(self, rows: List[TnvedRow], groups: Dict[str, str],
                     overwrite: bool) -> Tuple[int, int]:
        if not rows:
            return 0, 0
        codes = [r.code for r in rows]
        existing: Set[str] = set()
        for part in chunks(list(dict.fromkeys(codes))):
            sql = "SELECT code FROM tnved_catalog WHERE code IN (%s)" % ",".join("?" * len(part))
            existing.update(r["code"] for r in self.conn.execute(sql, list(part)))
        try:
            with self.conn:
                if groups:
                    self.conn.executemany(
                        """INSERT INTO tnved_groups(grp, name) VALUES(?,?)
                           ON CONFLICT(grp) DO UPDATE SET name=excluded.name""",
                        list(groups.items()))
                params = [(r.code, r.name, norm_text(r.name), r.path, norm_text(r.path),
                           r.name, norm_text(r.name), r.code[:2], r.dashes, r.depth,
                           len(r.code), r.parent, r.traceable, r.ord) for r in rows]
                for part in chunks(params, 400):
                    if overwrite:
                        self.conn.executemany(
                            """INSERT INTO tnved_catalog
                               (code, name, name_lc, path, path_lc, tail, tail_lc, grp,
                                dashes, depth, digits, parent, traceable, ord)
                               VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                               ON CONFLICT(code) DO UPDATE SET
                               name=excluded.name, name_lc=excluded.name_lc,
                               path=excluded.path, path_lc=excluded.path_lc,
                               tail=excluded.tail, tail_lc=excluded.tail_lc,
                               grp=excluded.grp, dashes=excluded.dashes, depth=excluded.depth,
                               digits=excluded.digits, parent=excluded.parent,
                               traceable=MAX(tnved_catalog.traceable, excluded.traceable),
                               ord=excluded.ord""", part)
                    else:
                        self.conn.executemany(
                            """INSERT INTO tnved_catalog
                               (code, name, name_lc, path, path_lc, tail, tail_lc, grp,
                                dashes, depth, digits, parent, traceable, ord)
                               VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                               ON CONFLICT(code) DO UPDATE SET
                               name=CASE WHEN TRIM(tnved_catalog.name)='' THEN excluded.name ELSE tnved_catalog.name END,
                               name_lc=CASE WHEN TRIM(tnved_catalog.name)='' THEN excluded.name_lc ELSE tnved_catalog.name_lc END,
                               path=CASE WHEN TRIM(tnved_catalog.path)='' THEN excluded.path ELSE tnved_catalog.path END,
                               path_lc=CASE WHEN TRIM(tnved_catalog.path)='' THEN excluded.path_lc ELSE tnved_catalog.path_lc END,
                               traceable=MAX(tnved_catalog.traceable, excluded.traceable)""", part)
            new_cnt = sum(1 for c in codes if c not in existing)
            return new_cnt, len(codes) - new_cnt
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка загрузки ТН ВЭД: {e}") from e

    def tnved_save(self, code: str, name: str, traceable: int = 0) -> None:
        try:
            with self.conn:
                self.conn.execute(
                    """INSERT INTO tnved_catalog(code, name, name_lc, tail, tail_lc, grp, digits)
                       VALUES(?,?,?,?,?,?,?) ON CONFLICT(code) DO UPDATE SET
                       name=excluded.name, name_lc=excluded.name_lc,
                       tail=excluded.tail, tail_lc=excluded.tail_lc,
                       grp=excluded.grp, digits=excluded.digits, traceable=excluded.traceable""",
                    (code, name, norm_text(name), name, norm_text(name), code[:2], len(code), traceable))
            self.tnved_rebuild()
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка сохранения ТН ВЭД {code}: {e}") from e

    def tnved_delete(self, code: str) -> bool:
        try:
            with self.conn:
                cur = self.conn.execute("DELETE FROM tnved_catalog WHERE code=?", (code,))
                ok = cur.rowcount > 0
            if ok:
                self.tnved_rebuild()
            return ok
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка удаления ТН ВЭД {code}: {e}") from e

    def tnved_rebuild(self) -> int:
        rows = self.conn.execute("SELECT code, name, dashes, ord FROM tnved_catalog ORDER BY ord").fetchall()
        objs = [TnvedRow(code=r["code"], name=r["name"] or "", dashes=int(r["dashes"] or 0),
                         ord=int(r["ord"] or 0)) for r in rows]
        build_tnved_paths(objs)
        with self.conn:
            self.conn.executemany(
                """UPDATE tnved_catalog SET path=?, path_lc=?, depth=?, parent=?, grp=?
                   WHERE code=?""",
                [(o.path, norm_text(o.path), o.depth, o.parent, o.code[:2], o.code) for o in objs])
        return len(objs)

    def _tnved_where(self, code_q: str, name_q: str, mode: str, grp: str,
                     only_leaf: bool, only_trace: bool, prefix: str) -> Tuple[str, List]:
        cl: List[str] = []
        pr: List = []
        if prefix:
            cl.append("c.code LIKE ? ESCAPE '\\'")
            pr.append(like_pattern(prefix).lstrip("%"))
        cq = normalize_tnved(code_q)
        if cq:
            cl.append("c.code LIKE ? ESCAPE '\\'")
            pr.append(like_pattern(cq))
        nq = norm_text(name_q)
        if nq:
            col = "c.path_lc" if mode == "path" else "c.name_lc"
            cl.append(f"{col} LIKE ? ESCAPE '\\'")
            pr.append(like_pattern(nq))
        g = normalize_tnved(grp)
        if g:
            cl.append("c.grp = ?")
            pr.append(g)
        if only_leaf:
            cl.append("c.digits = 10")
        if only_trace:
            cl.append("c.traceable = 1")
        return (" WHERE " + " AND ".join(cl)) if cl else "", pr

    def tnved_search(self, code_q="", name_q="", mode="name", grp="", only_leaf=False,
                     only_trace=False, prefix="", limit: Optional[int] = PAGE_SIZE,
                     offset: int = 0) -> List[TnvedRecord]:
        w, pr = self._tnved_where(code_q, name_q, mode, grp, only_leaf, only_trace, prefix)
        sql = (f"SELECT c.*, COALESCE(g.name,'') AS gname FROM tnved_catalog c "
               f"LEFT JOIN tnved_groups g ON g.grp=c.grp{w} ORDER BY c.code")
        if limit is not None:
            sql += " LIMIT ? OFFSET ?"
            pr = pr + [int(limit), int(offset)]
        try:
            return [TnvedRecord(r["code"], r["name"] or "", r["path"] or "", r["grp"] or "",
                                int(r["depth"] or 0), int(r["digits"] or 0), r["parent"] or "",
                                int(r["traceable"] or 0), r["gname"] or "")
                    for r in self.conn.execute(sql, pr)]
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка поиска ТН ВЭД: {e}") from e

    def tnved_count(self, code_q="", name_q="", mode="name", grp="", only_leaf=False,
                    only_trace=False, prefix="") -> int:
        w, pr = self._tnved_where(code_q, name_q, mode, grp, only_leaf, only_trace, prefix)
        return int(self.conn.execute(f"SELECT COUNT(*) FROM tnved_catalog c{w}", pr).fetchone()[0])

    def tnved_count_all(self) -> int:
        return int(self.conn.execute("SELECT COUNT(*) FROM tnved_catalog").fetchone()[0])

    def tnved_group_list(self) -> List[Tuple[str, str]]:
        return [(r[0], r[1] or "") for r in self.conn.execute(
            "SELECT DISTINCT c.grp, COALESCE(g.name,'') FROM tnved_catalog c "
            "LEFT JOIN tnved_groups g ON g.grp=c.grp WHERE c.grp<>'' ORDER BY c.grp")]

    def tnved_get(self, code: str) -> Optional[TnvedRecord]:
        for r in self.tnved_search(code_q=code, limit=None):
            if r.code == code:
                return r
        return None

    def stats(self) -> Dict[str, int]:
        s = ["COUNT(*) AS total", "SUM(TRIM(product_name)='') AS empty_name",
             "SUM(in_decree_80=0 AND in_168_app1=0 AND in_168_app2=0 AND in_168_app3=0) AS nowhere"]
        for d in DOC_FLAGS:
            for v, name in ((1, "full"), (2, "part"), (3, "inh"), (4, "check"), (5, "din"), (6, "dout")):
                s.append(f"SUM({d}={v}) AS {d}_{name}")
        r = self.conn.execute(f"SELECT {', '.join(s)} FROM okrb_catalog").fetchone()
        out = {k: int(r[k] or 0) for k in r.keys()}
        out["mentions"] = int(self.conn.execute("SELECT COUNT(*) FROM okrb_mentions").fetchone()[0])
        out["positions"] = int(self.conn.execute("SELECT COUNT(*) FROM okrb_positions").fetchone()[0])
        out["decisions"] = int(self.conn.execute("SELECT COUNT(*) FROM okrb_decisions").fetchone()[0])
        out["tnved"] = self.tnved_count_all()
        out["tnved_leaf"] = int(self.conn.execute("SELECT COUNT(*) FROM tnved_catalog WHERE digits=10").fetchone()[0])
        out["tnved_trace"] = int(self.conn.execute("SELECT COUNT(*) FROM tnved_catalog WHERE traceable=1").fetchone()[0])
        out["tnved_groups"] = int(self.conn.execute("SELECT COUNT(*) FROM tnved_groups").fetchone()[0])
        return out

    def backup(self, dest: str) -> None:
        dst = sqlite3.connect(dest)
        try:
            self.conn.backup(dst)
        except sqlite3.Error as e:
            raise RuntimeError(f"Ошибка резервного копирования: {e}") from e
        finally:
            dst.close()

    def close(self) -> None:
        try:
            self.conn.close()
        except sqlite3.Error:
            pass


# ---------------------------------------------------------------------------
# Парсер PDF (ОКРБ)
# ---------------------------------------------------------------------------
class PDFParser:
    TOKEN_RE = re.compile(r"(?<!\w)(из\s*)?(\d+(?:\.\d+)+)(?!\d)(?!\.\d)", re.IGNORECASE)
    LEADING_NOISE_RE = re.compile(
        r"^(?:из\s+|код\s+окрб\s*|окрб\s*|приложение\s+|постановление\s+|№\s*|#\s*|[-–—]\s*)+",
        re.IGNORECASE)
    STOP_RE = re.compile(
        r"^(приложение|утверждено|постановление|совет\s+министров|республика\s+беларусь|"
        r"примечание|примечания|стр\.?|страница|глава|раздел|пункт)\b", re.IGNORECASE)

    @staticmethod
    def is_okrb_code(token: str, min_groups: int = 3) -> bool:
        return is_code_shape(token, min_groups)

    @staticmethod
    def normalize_code(code: str) -> str:
        return normalize_code(code)

    @classmethod
    def clean_name(cls, raw: str) -> str:
        if not raw:
            return ""
        s = raw.replace("\u00ad", "")
        s = re.sub(r"(\w)-\s*\n\s*(\w)", r"\1\2", s)
        s = re.sub(r"\s+", " ", s).strip()
        s = cls.LEADING_NOISE_RE.sub("", s)
        s = s.strip(" \t\r\n.,;:-–—|()[]{}'\"«»")
        s = re.sub(r"\s*\*+\s*$", "", s)
        s = re.sub(r"(?<!\d)\d{2}(?:\.\d{2,3}){2,3}\s*$", "", s)
        return s.strip(" -–—,;.|")

    @classmethod
    def _find_codes(cls, text: str, min_groups: int):
        out = []
        for m in cls.TOKEN_RE.finditer(text):
            tok = m.group(2)
            if not cls.is_okrb_code(tok, min_groups):
                continue
            pre = text[max(0, m.start() - 8):m.start()]
            if re.search(r"(?:от|дата)\s+$", pre, re.IGNORECASE):
                continue
            post = text[m.end():m.end() + 10]
            if re.match(r"\s*(?:г\.|года\b|год\b)", post, re.IGNORECASE):
                continue
            out.append((m, tok, bool(m.group(1))))
        return out

    @classmethod
    def _stop(cls, s: str) -> bool:
        t = (s or "").strip()
        return (not t) or (not has_letters(t)) or bool(cls.STOP_RE.match(t))

    @classmethod
    def _below(cls, lines, li, code_lines, max_lines=4, max_chars=320):
        parts, total = [], 0
        for j in range(li + 1, min(li + 1 + max_lines, len(lines))):
            if j in code_lines or cls._stop(lines[j]):
                break
            t = lines[j].strip()
            parts.append(t)
            total += len(t)
            if total >= max_chars:
                break
        return " ".join(parts)

    @classmethod
    def _above(cls, lines, li, code_lines, max_lines=3, max_chars=320):
        parts, total = [], 0
        for j in range(li - 1, max(li - 1 - max_lines, -1), -1):
            if j in code_lines or cls._stop(lines[j]):
                break
            t = lines[j].strip()
            parts.insert(0, t)
            total += len(t)
            if total >= max_chars:
                break
        return " ".join(parts)

    @classmethod
    def _cont(cls, lines, li, code_lines, max_lines=2):
        parts = []
        for j in range(li + 1, min(li + 1 + max_lines, len(lines))):
            if j in code_lines:
                break
            t = lines[j].strip()
            if not t or cls._stop(t) or not re.match(r"^[a-zа-яё(«\-–—]", t):
                break
            parts.append(t)
        return " ".join(parts)

    @classmethod
    def extract_items_from_text(cls, text: str, min_groups=3, mode="auto", page=0) -> List[ParsedItem]:
        matches = cls._find_codes(text or "", min_groups)
        if not matches:
            return []
        lines = text.split("\n")
        starts, pos = [], 0
        for ln in lines:
            starts.append(pos)
            pos += len(ln) + 1
        import bisect

        def lidx(p):
            return bisect.bisect_right(starts, p) - 1

        code_lines = {lidx(m.start(2)) for m, _, _ in matches}
        items: List[ParsedItem] = []
        chain: List[bool] = []
        for i, (m, code, partial) in enumerate(matches):
            li = lidx(m.start(2))
            line = lines[li]
            ce = m.end() - starts[li]
            nxt = matches[i + 1][0].start() if i + 1 < len(matches) else len(text)
            tail = line[ce:]
            if nxt <= starts[li] + len(line):
                tail = line[ce:max(ce, nxt - starts[li])]
            same = cls.clean_name(tail)
            gap = text[m.end():nxt]
            chained = (i + 1 < len(matches)) and bool(re.fullmatch(r"[\s,;]*(?:и\s*)?", gap))
            chain.append(chained)
            if mode == "same":
                name = same
            elif mode == "below":
                name = cls.clean_name(" ".join(x for x in (same, cls._below(lines, li, code_lines)) if x))
            elif mode == "above":
                name = cls.clean_name(" ".join(x for x in (cls._above(lines, li, code_lines), same) if x))
            else:
                name = same
                if has_letters(name):
                    c = cls._cont(lines, li, code_lines)
                    if c:
                        name = cls.clean_name(name + " " + c)
                else:
                    b = cls._below(lines, li, code_lines)
                    if has_letters(b):
                        name = cls.clean_name(b)
                    else:
                        a = cls._above(lines, li, code_lines)
                        if has_letters(a):
                            name = cls.clean_name(a)
            items.append(ParsedItem(code, name, partial, page, "текст"))
        for i in range(1, len(items)):
            if chain[i - 1]:
                items[i].partial = items[i - 1].partial
        for i in range(len(items) - 2, -1, -1):
            if chain[i]:
                items[i].name = items[i + 1].name or items[i].name
        return items

    @staticmethod
    def _name_from_cells(cells: List[str], ci: int) -> str:
        for group in ([c for j, c in enumerate(cells) if j > ci],
                      [c for j, c in enumerate(cells) if j < ci]):
            parts = [re.sub(r"\s+", " ", c).strip() for c in group
                     if len(c.strip()) > 1 and has_letters(c)]
            if parts:
                return " ".join(parts)
        return ""

    @classmethod
    def _items_from_table(cls, rows, min_groups, page) -> List[ParsedItem]:
        out: List[ParsedItem] = []
        for row in rows or []:
            cells = [re.sub(r"\s+", " ", (c or "")).strip() for c in row]
            ci, codes, partial = -1, [], False
            for k, cell in enumerate(cells):
                if not cell or not re.search(r"\d", cell):
                    continue
                found = cls._find_codes(cell, min_groups)
                if not found:
                    continue
                res = cls.TOKEN_RE.sub("", cell)
                res = re.sub(r"\bиз\b", "", res, flags=re.IGNORECASE)
                res = re.sub(r"[\s,;.\-–—()\[\]№]+", "", res)
                if res == "":
                    ci, codes = k, [c for _, c, _ in found]
                    partial = bool(re.search(r"\bиз\b", cell, re.IGNORECASE))
                    break
            if codes:
                name = cls.clean_name(cls._name_from_cells(cells, ci))
                for c in codes:
                    out.append(ParsedItem(c, name, partial, page, "таблица"))
                continue
            ne = [c for c in cells if c]
            if out and len(ne) == 1 and has_letters(ne[0]) and not cls._stop(ne[0]) and len(ne[0]) < 250:
                out[-1].name = cls.clean_name(out[-1].name + " " + ne[0])
            for cell in cells:
                if cell and cls._find_codes(cell, min_groups) and has_letters(cell):
                    out.extend(cls.extract_items_from_text(cell, min_groups, "auto", page))
        return out

    def _page_tables(self, page, min_groups, pno):
        items, cnt = [], 0
        try:
            finder = page.find_tables()
        except Exception:
            return items, 0
        for t in getattr(finder, "tables", []) or []:
            try:
                rows = t.extract()
            except Exception:
                continue
            got = self._items_from_table(rows, min_groups, pno)
            if got:
                cnt += 1
                items.extend(got)
        return items, cnt

    @staticmethod
    def _merge(items: List[ParsedItem]) -> List[ParsedItem]:
        by: Dict[str, ParsedItem] = {}
        for it in items:
            cur = by.get(it.code)
            if cur is None:
                by[it.code] = ParsedItem(it.code, it.name, it.partial, it.page, it.source)
            else:
                cur.partial = cur.partial and it.partial
                if len(it.name) > len(cur.name):
                    cur.name = it.name
                if it.source == "таблица":
                    cur.source = "таблица"
        return sorted(by.values(), key=lambda x: x.code)

    def parse_pdf(self, path: str, min_groups=3, name_mode="auto", cancel_cb=None) -> ParseResult:
        if fitz is None:
            raise RuntimeError("Не установлен PyMuPDF: pip install \"PyMuPDF>=1.24\"")
        if not os.path.isfile(path):
            raise FileNotFoundError(path)
        res = ParseResult()
        try:
            doc = fitz.open(path)
        except Exception as e:
            raise RuntimeError(f"Не удалось открыть «{os.path.basename(path)}»: {e}") from e
        all_items: List[ParsedItem] = []
        try:
            res.pages = doc.page_count
            for pno in range(doc.page_count):
                if cancel_cb and cancel_cb():
                    res.cancelled = True
                    break
                page = doc.load_page(pno)
                try:
                    text = page.get_text("text") or ""
                except Exception:
                    text = ""
                res.text_chars += len(text.strip())
                pi: List[ParsedItem] = []
                if name_mode in ("auto", "table"):
                    ti, tc = self._page_tables(page, min_groups, pno + 1)
                    res.tables += tc
                    pi.extend(ti)
                if name_mode != "table":
                    mode = "auto" if name_mode == "auto" else name_mode
                    known = {i.code for i in pi}
                    pi.extend(i for i in self.extract_items_from_text(text, min_groups, mode, pno + 1)
                              if i.code not in known)
                all_items.extend(pi)
        finally:
            doc.close()
        res.items = self._merge(all_items)
        if res.pages and res.text_chars < 50 * res.pages:
            res.warnings.append("В PDF почти нет текста — вероятно, скан. Нужен OCR.")
        if not res.items and not res.cancelled:
            res.warnings.append("Коды не найдены. Попробуйте «минимум групп = 2».")
        return res


APP_STRICT = re.compile(r"^\s*приложение\s*(?:№|N|n)?\s*([1-9])\s*(?:$|к\b)", re.IGNORECASE)
APP_LOOSE = re.compile(r"^\s*приложение\s*(?:№|N|n)?\s*([1-9])\b", re.IGNORECASE)


def detect_pdf_sections(path: str, head_lines: int = 25) -> Tuple[List[PdfSection], List[str]]:
    if fitz is None:
        raise RuntimeError("Не установлен PyMuPDF")
    warns: List[str] = []
    strict, loose = [], []
    total = 0
    doc = fitz.open(path)
    try:
        total = doc.page_count
        cs = cl = 0
        for pno in range(total):
            try:
                text = doc.load_page(pno).get_text("text") or ""
            except Exception:
                text = ""
            gs = gl = False
            for li, raw in enumerate(text.split("\n")[:head_lines]):
                ln = raw.strip()
                if not ln or "..." in ln or "…" in ln:
                    continue
                if not gs:
                    m = APP_STRICT.match(ln)
                    if m:
                        gs = True
                        n = int(m.group(1))
                        if n > cs:
                            strict.append((pno + 1, n, ln[:120]))
                            cs = n
                            if li > 5:
                                warns.append(f"«Приложение {n}» не в начале стр. {pno+1} — "
                                             f"вся страница отнесена к нему, проверьте.")
                if not gl:
                    m = APP_LOOSE.match(ln)
                    if m:
                        gl = True
                        n = int(m.group(1))
                        if n > cl:
                            loose.append((pno + 1, n, ln[:120]))
                            cl = n
                if gs and gl:
                    break
    finally:
        doc.close()
    marks = strict or loose
    if not marks:
        warns.append("Заголовки приложений не найдены — укажите документ и страницы вручную.")
        return [PdfSection(1, max(1, total), None, "Приложения не найдены")], warns
    sections: List[PdfSection] = []
    if marks[0][0] > 1:
        sections.append(PdfSection(1, marks[0][0] - 1, None, "Текст постановления"))
    for i, (pg, n, title) in enumerate(marks):
        end = marks[i + 1][0] - 1 if i + 1 < len(marks) else total
        col = f"in_168_app{n}" if n in (1, 2, 3) else None
        sections.append(PdfSection(pg, end, col, title))
    return sections, warns


def parse_page_ranges(text: str, page_count: int) -> List[Tuple[int, int]]:
    t = (text or "").strip()
    if not t:
        return [(1, max(1, page_count))]
    out = []
    for part in re.split(r"[,;]+", t):
        p = part.strip()
        if not p:
            continue
        a = re.fullmatch(r"(\d+)\s*[-–—:]\s*(\d+)", p)
        b = re.fullmatch(r"(\d+)\s*[-–—:]", p)
        c = re.fullmatch(r"[-–—:]\s*(\d+)", p)
        d = re.fullmatch(r"(\d+)", p)
        if a:
            x, y = int(a.group(1)), int(a.group(2))
        elif b:
            x, y = int(b.group(1)), page_count
        elif c:
            x, y = 1, int(c.group(1))
        elif d:
            x = y = int(d.group(1))
        else:
            raise ValueError(f"Непонятный диапазон «{p}». Примеры: 3-12, 15, 20-")
        if x < 1 or y < x or x > page_count:
            raise ValueError(f"Диапазон «{p}» вне файла (1–{page_count}).")
        out.append((x, min(y, page_count)))
    if not out:
        raise ValueError("Не указан ни один диапазон.")
    return out


def guess_document(filename: str) -> Optional[str]:
    base = os.path.basename(filename).lower()
    cleaned = re.sub(r"\d{1,2}[./-]\d{1,2}[./-]\d{2,4}", " ", base)
    cleaned = re.sub(r"\b(?:19|20)\d{2}\b", " ", cleaned)
    nums = re.findall(r"\d+", cleaned)
    m = re.search(r"(?:прил(?:ожение|\.?)|app|часть)\s*[№n]?\s*([123])", cleaned)
    if "168" in nums:
        if m:
            return f"in_168_app{m.group(1)}"
        rest = [n for n in nums if n != "168"]
        for a in ("1", "2", "3"):
            if a in rest:
                return f"in_168_app{a}"
        return "auto"
    if "80" in nums:
        return "in_decree_80"
    return None


# ---------------------------------------------------------------------------
# Чтение XLSX / CSV
# ---------------------------------------------------------------------------
def code_from_cell(v, min_groups=2, kind="okrb") -> Tuple[str, str]:
    if v is None or isinstance(v, bool):
        return "", ""
    if isinstance(v, (datetime, date)):
        return "", "Excel превратил код в дату"
    note = ""
    if kind == "tnved":
        if isinstance(v, (int, float)):
            raw = str(int(v))
            note = "код из числа Excel"
        else:
            raw = normalize_tnved(str(v))
        # Excel съедает ведущий ноль: 0305 -> 305, 0803 -> 803
        if len(raw) not in TNVED_LENGTHS and (len(raw) + 1) in TNVED_LENGTHS:
            raw = raw.zfill(len(raw) + 1)
            note = "ведущий ноль восстановлен"
        return (raw, note) if tnved_shape(raw) else ("", "")
    if isinstance(v, (int, float)):
        if isinstance(v, int):
            raw = str(v)
        else:
            raw = f"{v:.6f}".rstrip("0").rstrip(".")
            g = raw.split(".")
            if len(g) > 4:
                return "", ""
            raw = ".".join(x + "0" if len(x) == 1 else x for x in g)
        note = "код восстановлен из числа Excel"
    else:
        raw = normalize_code(str(v).replace("\u00a0", " ")).strip("\"'").rstrip(".")
    if not raw:
        return "", ""
    return (raw, note) if is_code_shape(raw, min_groups) else ("", "")


def name_from_cell(v) -> str:
    if v is None or isinstance(v, (datetime, date)):
        return ""
    s = str(v).replace("\u00a0", " ").replace("\u00ad", "")
    return re.sub(r"[ \t]+", " ", s).strip()


def load_csv(path: str) -> List[List[str]]:
    data = None
    for enc in ("utf-8-sig", "cp1251", "utf-8"):
        try:
            with open(path, "r", encoding=enc, newline="") as fh:
                data = fh.read()
            break
        except UnicodeDecodeError:
            continue
    if data is None:
        raise RuntimeError("Не удалось определить кодировку CSV.")
    try:
        delim = csv.Sniffer().sniff(data[:4096], delimiters=";,\t").delimiter
    except csv.Error:
        delim = ";"
    return [list(r) for r in csv.reader(io.StringIO(data), delimiter=delim)]


def xlsx_sheets(path: str) -> List[str]:
    if os.path.splitext(path)[1].lower() in (".csv", ".txt"):
        return []
    if openpyxl is None:
        raise RuntimeError("Нужен openpyxl: pip install openpyxl")
    wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
    try:
        return list(wb.sheetnames)
    finally:
        wb.close()


def xlsx_sample(path: str, sheet: Optional[str], n=120) -> List[List]:
    if os.path.splitext(path)[1].lower() in (".csv", ".txt"):
        return load_csv(path)[:n]
    wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
    try:
        ws = wb[sheet] if sheet else wb[wb.sheetnames[0]]
        return [list(r) for r in islice(ws.iter_rows(values_only=True), n)]
    finally:
        wb.close()


def detect_columns(sample: List[List], min_groups=2, kind="okrb") -> Tuple[int, int, int]:
    nc = max((len(r) for r in sample), default=0)
    if not nc:
        return -1, -1, 0
    cs, ts = [0] * nc, [0] * nc
    for row in sample:
        for c in range(nc):
            v = row[c] if c < len(row) else None
            if code_from_cell(v, min_groups, kind)[0]:
                cs[c] += 1
            else:
                s = name_from_cell(v)
                if len(s) >= 3 and has_letters(s):
                    ts[c] += min(len(s), 120)
    cc = max(range(nc), key=lambda i: cs[i])
    if cs[cc] == 0:
        return -1, -1, 0
    cand = [c for c in range(nc) if c != cc and ts[c] > 0]
    right = [c for c in cand if c > cc]
    ncol = max(right or cand, key=lambda i: ts[i]) if cand else -1
    start = 0
    for i, row in enumerate(sample):
        v = row[cc] if cc < len(row) else None
        if code_from_cell(v, min_groups, kind)[0]:
            start = i
            break
    return cc, ncol, start


def build_tnved_paths(rows: List[TnvedRow]) -> None:
    """Иерархия по кодам + контекст строк без кода."""
    by = {r.code: r for r in rows}
    codes = set(by)
    for r in rows:
        r.grp = r.code[:2]
        r.parent = ""
        for k in range(len(r.code) - 1, 1, -1):
            cand = r.code[:k]
            if cand in codes and tnved_shape(cand):
                r.parent = cand
                break
    memo: Dict[str, str] = {}

    def path_of(code: str, guard: int = 0) -> str:
        if code in memo:
            return memo[code]
        r = by[code]
        ctx = [t for (lvl, t) in r.ctx if lvl <= r.dashes]
        if r.parent and guard < 24:
            full = " \u203a ".join([path_of(r.parent, guard + 1)] + ctx + [r.name])
        else:
            full = " \u203a ".join(ctx + [r.name])
        memo[code] = full
        return full

    for r in sorted(rows, key=lambda x: (len(x.code), x.code)):
        r.path = path_of(r.code)
    for r in rows:
        d, cur, guard = 0, r, 0
        while cur.parent and guard < 24:
            cur = by[cur.parent]
            d += 1
            guard += 1
        r.depth = d


def parse_tnved_source(path, sheets, code_col, name_col, start_row,
                       progress_cb=None, cancel_cb=None):
    st = dict(rows=0, codes=0, context=0, traceable=0, groups=0, dups=0, arrows=0, numeric=0)
    warns: List[str] = []
    out: List[TnvedRow] = []
    by: Dict[str, int] = {}
    groups: Dict[str, str] = {}
    pending: List[Tuple[int, str]] = []
    last_idx = -1
    order = 0

    def handle(sheet: str, rows_iter, start: int) -> bool:
        nonlocal last_idx, order
        for i, raw in enumerate(rows_iter):
            if i < start:
                continue
            st["rows"] += 1
            if cancel_cb and st["rows"] % 2000 == 0 and cancel_cb():
                return False
            vals = [name_from_cell(v) for v in (raw or [])]
            joined = " ".join(vals).lower()
            cv = (raw[code_col] if 0 <= code_col < len(raw or []) else None)
            code, note = code_from_cell(cv, 2, "tnved")
            text = vals[name_col] if 0 <= name_col < len(vals) else ""
            if not text:
                for j, s in enumerate(vals):
                    if j == code_col:
                        continue
                    if len(s) >= 3 and has_letters(s) and not tnved_shape(normalize_tnved(s)):
                        text = s
                        break
            if not code and "прослеживаем" in joined:
                if last_idx >= 0 and not out[last_idx].traceable:
                    out[last_idx].traceable = 1
                    st["traceable"] += 1
                continue
            gm = TNVED_GROUP_RE.match(text or "")
            if gm and not code:
                g = gm.group(1).zfill(2)
                nm = gm.group(2).strip() or f"Группа {g}"
                if g not in groups:
                    st["groups"] += 1
                groups[g] = nm
                pending = []
                continue
            if not text:
                continue
            lvl = tnved_dash_level(text)
            own = strip_tnved_dashes(text)
            ctx = []
            if not own:
                continue
            if not code:
                pending.append((lvl, own))
                st["context"] += 1
                continue
            if note:
                st["numeric"] += 1
            if code in by:
                st["dups"] += 1
                idx = by[code]
                if len(own) > len(out[idx].name):
                    out[idx].name = own
                last_idx = idx
                pending = []
                continue
            rec = TnvedRow(code=code, name=own, sheet=sheet, row_no=i + 1, dashes=lvl,
                           ctx=(ctx + pending) if ctx else list(pending), ord=order)
            order += 1
            by[code] = len(out)
            out.append(rec)
            last_idx = len(out) - 1
            st["codes"] += 1
            pending = []
        return True

    if os.path.splitext(path)[1].lower() in (".csv", ".txt"):
        if progress_cb:
            progress_cb(0, 1, os.path.basename(path))
        handle(os.path.basename(path), load_csv(path), start_row)
    else:
        if openpyxl is None:
            raise RuntimeError("Нужен openpyxl: pip install openpyxl")
        wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
        try:
            names = list(sheets) or list(wb.sheetnames)
            for k, sh in enumerate(names):
                if sh not in wb.sheetnames:
                    continue
                if progress_cb:
                    progress_cb(k, len(names), sh)
                if not handle(sh, wb[sh].iter_rows(values_only=True), start_row):
                    break
        finally:
            wb.close()
    build_tnved_paths(out)
    if st["numeric"]:
        warns.append(f"{st['numeric']} кодов прочитано из числового формата Excel — "
                     "проверьте ведущие нули (лучше формат «Текстовый»).")
    if st["arrows"]:
        warns.append(f"{st['arrows']} строк в старом формате со стрелками — иерархия взята из текста.")
    return out, groups, st, warns


def parse_okrb_source(path, sheets, code_col, name_col, start_row, min_groups,
                      skip_no_name, skip_numeric, progress_cb=None, cancel_cb=None):
    st = dict(rows=0, unique=0, no_name=0, skip_name=0, numeric=0, skip_num=0, dates=0, dups=0)
    warns: List[str] = []
    by: Dict[str, CatalogRow] = {}

    def handle(sheet, rows_iter, start):
        for i, raw in enumerate(rows_iter):
            if i < start:
                continue
            st["rows"] += 1
            if cancel_cb and st["rows"] % 2000 == 0 and cancel_cb():
                return False
            vals = list(raw) if raw else []
            cv = vals[code_col] if 0 <= code_col < len(vals) else None
            code, note = code_from_cell(cv, min_groups, "okrb")
            name = name_from_cell(vals[name_col]) if 0 <= name_col < len(vals) else ""
            if not name:
                for c in range(code_col + 1, len(vals)):
                    if c == name_col:
                        continue
                    s = name_from_cell(vals[c])
                    if len(s) >= 3 and has_letters(s) and not code_from_cell(vals[c], 1, "okrb")[0]:
                        name = s
                        break
            if not code:
                if note:
                    st["dates"] += 1
                continue
            if note:
                st["numeric"] += 1
                if skip_numeric:
                    st["skip_num"] += 1
                    continue
            if not name:
                st["no_name"] += 1
                if skip_no_name:
                    st["skip_name"] += 1
                    continue
            name = re.sub(r"\s+", " ", name).strip()
            prev = by.get(code)
            if prev is None:
                by[code] = CatalogRow(code, name, sheet, i + 1, note)
            else:
                st["dups"] += 1
                if len(name) > len(prev.name):
                    prev.name = name
        return True

    if os.path.splitext(path)[1].lower() in (".csv", ".txt"):
        if progress_cb:
            progress_cb(0, 1, os.path.basename(path))
        handle(os.path.basename(path), load_csv(path), start_row)
    else:
        if openpyxl is None:
            raise RuntimeError("Нужен openpyxl: pip install openpyxl")
        wb = openpyxl.load_workbook(path, read_only=True, data_only=True)
        try:
            names = list(sheets) or list(wb.sheetnames)
            for k, sh in enumerate(names):
                if sh not in wb.sheetnames:
                    continue
                if progress_cb:
                    progress_cb(k, len(names), sh)
                if not handle(sh, wb[sh].iter_rows(values_only=True), start_row):
                    break
        finally:
            wb.close()
    rows = sorted(by.values(), key=lambda r: r.code)
    st["unique"] = len(rows)
    if st["dates"]:
        warns.append(f"{st['dates']} строк: Excel превратил код в дату — пропущены.")
    if st["numeric"]:
        warns.append(f"{st['numeric']} кодов восстановлено из чисел Excel — проверьте.")
    return rows, st, warns


# ---------------------------------------------------------------------------
# Потоки
# ---------------------------------------------------------------------------
class PdfWorker(QThread):
    progress = pyqtSignal(int, int, str)
    done = pyqtSignal(list, list)
    failed = pyqtSignal(str)

    def __init__(self, jobs, min_groups, name_mode):
        super().__init__()
        self.jobs, self.min_groups, self.name_mode = jobs, min_groups, name_mode
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            parser = PDFParser()
            rows: List[PdfImportRow] = []
            rep: List[str] = []
            for i, (path, col, pages_text) in enumerate(self.jobs):
                if self._cancel:
                    rep.append("Отменено пользователем.")
                    break
                fname = os.path.basename(path)
                self.progress.emit(i, len(self.jobs), fname)
                try:
                    res = parser.parse_pdf(path, self.min_groups, self.name_mode,
                                           cancel_cb=lambda: self._cancel)
                except Exception as e:
                    rep.append(f"✗ «{fname}»: {e}")
                    continue
                sections: List[PdfSection] = []
                ranges = [(1, max(1, res.pages))]
                if col == "auto":
                    try:
                        sections, w = detect_pdf_sections(path)
                    except Exception as e:
                        rep.append(f"✗ «{fname}»: {e}")
                        continue
                    rep.append(f"«{fname}» — структура ({res.pages} стр.):")
                    for s in sections:
                        rep.append(f"   стр. {s.pages_text()} → {s.label()}  [{s.title}]")
                    rep += [f"   ⚠ {x}" for x in w]
                else:
                    try:
                        ranges = parse_page_ranges(pages_text, max(1, res.pages))
                    except ValueError as e:
                        rep.append(f"✗ «{fname}»: {e}")
                        continue
                    rep.append(f"«{fname}» → {DOC_TITLES[col]}"
                               + (f", страницы {pages_text}" if pages_text.strip() else " (весь файл)"))
                counts: Dict[str, int] = {}
                partial_no_text = 0
                skipped = 0
                for it in res.items:
                    target = (next((s.doc for s in sections if s.start_page <= it.page <= s.end_page), None)
                              if col == "auto" else
                              (col if any(a <= it.page <= b for a, b in ranges) else None))
                    if not target:
                        skipped += 1
                        continue
                    text = it.name
                    mode, kind = (M_PARTIAL, K_IN) if it.partial else (M_FULL, K_IN)
                    m = EXCEPT_RE.search(text or "")
                    if m:
                        mode, kind = M_PARTIAL, K_OUT
                        text = text[m.end():].strip()
                    if mode == M_PARTIAL and not text:
                        partial_no_text += 1
                    rows.append(PdfImportRow(it.code, text, target, mode, kind, it.page, it.source, fname))
                    counts[target] = counts.get(target, 0) + 1
                rep.append("   кодов " + str(len(res.items)) + " → "
                           + ("; ".join(f"{DOC_SHORT[c]}: {n}" for c, n in sorted(counts.items()))
                              or "ничего не отобрано")
                           + (f"; пропущено вне разделов: {skipped}" if skipped else ""))
                if partial_no_text:
                    rep.append(f"   ⚠ {partial_no_text} «частично» без текста товара — впишите позиции вручную.")
                rep += [f"   ⚠ {x}" for x in res.warnings]
            self.progress.emit(len(self.jobs), len(self.jobs), "готово")
            self.done.emit(rows, rep)
        except Exception as e:
            logging.error(traceback.format_exc())
            self.failed.emit(f"{type(e).__name__}: {e}")


class XlsxWorker(QThread):
    progress = pyqtSignal(int, int, str)
    done = pyqtSignal(list, dict, list, dict)
    failed = pyqtSignal(str)

    def __init__(self, kind, args):
        super().__init__()
        self.kind, self.args = kind, args
        self._cancel = False

    def cancel(self):
        self._cancel = True

    def run(self):
        try:
            if self.kind == "tnved":
                rows, groups, st, w = parse_tnved_source(
                    *self.args, progress_cb=lambda d, t, n: self.progress.emit(d, t, n),
                    cancel_cb=lambda: self._cancel)
                self.done.emit(rows, st, w, groups)
            else:
                rows, st, w = parse_okrb_source(
                    *self.args, progress_cb=lambda d, t, n: self.progress.emit(d, t, n),
                    cancel_cb=lambda: self._cancel)
                self.done.emit(rows, st, w, {})
        except Exception as e:
            logging.error(traceback.format_exc())
            self.failed.emit(f"{type(e).__name__}: {e}")


# ---------------------------------------------------------------------------
# Диалоги ОКРБ
# ---------------------------------------------------------------------------
class CodeDialog(QDialog):
    def __init__(self, db: DatabaseManager, parent=None, record: Optional[OkrbRecord] = None):
        super().__init__(parent)
        self.db = db
        self.setWindowTitle("Код ОКРБ" if record is None else f"Правка {record.okrb_code}")
        self.setModal(True)
        self.setMinimumWidth(640)
        root = QVBoxLayout(self)
        form = QFormLayout()
        self.e_code = QLineEdit()
        self.e_name = QLineEdit()
        form.addRow("Код ОКРБ:", self.e_code)
        form.addRow("Наименование (классификатор):", self.e_name)
        root.addLayout(form)
        box = QGroupBox("Явные отметки в постановлениях")
        bf = QFormLayout(box)
        self.cmb: Dict[str, QComboBox] = {}
        for d in DOC_FLAGS:
            c = QComboBox()
            c.addItem("нет", 0)
            c.addItem("полностью", M_FULL)
            c.addItem("частично (по позициям)", M_PARTIAL)
            bf.addRow(DOC_TITLES[d] + ":", c)
            self.cmb[d] = c
        root.addWidget(box)
        self.lbl_info = QLabel("")
        self.lbl_info.setWordWrap(True)
        self.lbl_info.setStyleSheet(f"color: {MUTED};")
        root.addWidget(self.lbl_info)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        bb.button(QDialogButtonBox.StandardButton.Save).setText("Сохранить")
        bb.button(QDialogButtonBox.StandardButton.Cancel).setText("Отмена")
        bb.accepted.connect(self._ok)
        bb.rejected.connect(self.reject)
        root.addWidget(bb)
        if record:
            self.e_code.setText(record.okrb_code)
            self.e_name.setText(record.product_name)
            ment = db.mentions(record.okrb_code)
            for d in DOC_FLAGS:
                self.cmb[d].setCurrentIndex(max(0, self.cmb[d].findData(ment.get(d, 0))))
            self.lbl_info.setText("Сейчас вычислено: " + record.inclusion_text()
                                  + "\nОснование: " + (record.basis_text() or "—")
                                  + "\n\nНаследование по группам считается автоматически; "
                                    "здесь задаются только явные отметки.")

    def _ok(self):
        code = normalize_code(self.e_code.text())
        if not is_code_shape(code, 2):
            QMessageBox.warning(self, "Проверка", f"Код «{code}» не похож на код ОКРБ.")
            return
        self.e_code.setText(code)
        self.accept()

    def result_data(self) -> Tuple[str, str, Dict[str, int]]:
        return (normalize_code(self.e_code.text()), self.e_name.text().strip(),
                {d: int(self.cmb[d].currentData()) for d in DOC_FLAGS})


class PositionDialog(QDialog):
    def __init__(self, parent=None, code="", pos: Optional[Position] = None):
        super().__init__(parent)
        self.setWindowTitle("Позиция постановления")
        self.setModal(True)
        self.setMinimumWidth(660)
        root = QVBoxLayout(self)
        form = QFormLayout()
        self.e_code = QLineEdit(code)
        self.c_doc = QComboBox()
        for d in DOC_FLAGS:
            self.c_doc.addItem(DOC_TITLES[d], d)
        self.c_kind = QComboBox()
        self.c_kind.addItem("Включено (товар попал под постановление)", K_IN)
        self.c_kind.addItem("Исключено (за исключением этого товара)", K_OUT)
        self.e_name = QLineEdit()
        self.e_name.setPlaceholderText("Товар дословно из постановления")
        self.s_page = QSpinBox()
        self.s_page.setRange(0, 100000)
        self.e_file = QLineEdit()
        form.addRow("Код ОКРБ:", self.e_code)
        form.addRow("Документ:", self.c_doc)
        form.addRow("Вид позиции:", self.c_kind)
        form.addRow("Наименование товара:", self.e_name)
        form.addRow("Страница:", self.s_page)
        form.addRow("Файл-источник:", self.e_file)
        root.addLayout(form)
        hint = QLabel("Строка «за исключением…» в таблице строится автоматически из этих позиций.")
        hint.setWordWrap(True)
        hint.setStyleSheet(f"color: {MUTED};")
        root.addWidget(hint)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        bb.button(QDialogButtonBox.StandardButton.Save).setText("Сохранить")
        bb.button(QDialogButtonBox.StandardButton.Cancel).setText("Отмена")
        bb.accepted.connect(self._ok)
        bb.rejected.connect(self.reject)
        root.addWidget(bb)
        if pos:
            self.e_code.setText(pos.code)
            self.c_doc.setCurrentIndex(max(0, self.c_doc.findData(pos.doc)))
            self.c_kind.setCurrentIndex(max(0, self.c_kind.findData(pos.kind)))
            self.e_name.setText(pos.name)
            self.s_page.setValue(pos.page)
            self.e_file.setText(pos.source_file)

    def _ok(self):
        if not is_code_shape(normalize_code(self.e_code.text()), 2):
            QMessageBox.warning(self, "Проверка", "Некорректный код ОКРБ.")
            return
        if not self.e_name.text().strip():
            QMessageBox.warning(self, "Проверка", "Заполните наименование товара.")
            return
        self.accept()

    def data(self) -> Tuple[str, str, int, str, int, str]:
        return (normalize_code(self.e_code.text()), str(self.c_doc.currentData()),
                int(self.c_kind.currentData()), self.e_name.text().strip(),
                int(self.s_page.value()), self.e_file.text().strip())


class PositionsDialog(QDialog):
    def __init__(self, db: DatabaseManager, code: str, parent=None):
        super().__init__(parent)
        self.db, self.code = db, code
        self.setWindowTitle(f"Позиции постановления — {code}")
        self.setModal(True)
        self.resize(960, 520)
        root = QVBoxLayout(self)
        self.t = QTableWidget(0, 5)
        self.t.setHorizontalHeaderLabels(["Документ", "Вид", "Товар", "Стр.", "Файл"])
        self.t.verticalHeader().setVisible(False)
        self.t.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.t.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.t.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.t.setAlternatingRowColors(True)
        self.t.verticalHeader().setDefaultSectionSize(28)
        self.t.doubleClicked.connect(lambda _i: self.edit())
        root.addWidget(self.t, 1)
        self.cols = TableColumns(self.t, "positions", [150, 130, 460, 70, 210])
        row = QHBoxLayout()
        for text, slot in (("Добавить", self.add), ("Изменить", self.edit), ("Удалить", self.remove)):
            b = QPushButton(text)
            b.clicked.connect(slot)
            row.addWidget(b)
        row.addStretch(1)
        b = QPushButton("Закрыть")
        b.clicked.connect(self.accept)
        row.addWidget(b)
        root.addLayout(row)
        self.pos: List[Position] = []
        self.reload()

    def reload(self):
        self.pos = self.db.positions_for([self.code]).get(self.code, [])
        self.t.setUpdatesEnabled(False)
        try:
            self.t.setRowCount(len(self.pos))
            for i, p in enumerate(self.pos):
                bg = QBrush(QColor(SUB_BG["in"] if p.kind == K_IN else SUB_BG["out"]))
                vals = [DOC_SHORT.get(p.doc, p.doc),
                        "✔ включено" if p.kind == K_IN else "✘ исключено",
                        p.name, str(p.page), p.source_file]
                for c, v in enumerate(vals):
                    it = QTableWidgetItem(v)
                    it.setData(ROLE_POS, p.id)
                    it.setBackground(bg)
                    it.setToolTip(v)
                    self.t.setItem(i, c, it)
        finally:
            self.t.setUpdatesEnabled(True)

    def _cur(self) -> Optional[Position]:
        r = self.t.currentRow()
        return self.pos[r] if 0 <= r < len(self.pos) else None

    def add(self):
        dlg = PositionDialog(self, self.code)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            code, doc, kind, name, page, fname = dlg.data()
            self.db.add_position(code, doc, kind, name, page, fname)
            self.reload()

    def edit(self):
        p = self._cur()
        if not p:
            return
        dlg = PositionDialog(self, self.code, p)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            _c, doc, kind, name, page, _f = dlg.data()
            self.db.update_position(p.id, doc, kind, name, page)
            self.reload()

    def remove(self):
        p = self._cur()
        if not p:
            return
        if QMessageBox.question(self, "Удаление", f"Удалить позицию «{p.name}»?",
                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
            self.db.delete_position(p.id)
            self.reload()


class DecisionDialog(QDialog):
    def __init__(self, db: DatabaseManager, code: str, parent=None):
        super().__init__(parent)
        self.db, self.code = db, code
        self.setWindowTitle(f"Решение по коду — {code}")
        self.setModal(True)
        self.resize(880, 640)
        root = QVBoxLayout(self)
        rec = db.get(code)
        head = QLabel(f"<b>{code}</b> — {rec.product_name if rec else ''}")
        head.setWordWrap(True)
        root.addWidget(head)
        note = QLabel("Решение снимает неопределённость «требует проверки»: группа включена частично, "
                      "и вы определяете, попадает ли конкретный код под ограничение группы.\n"
                      "Наименование самого кода при этом не меняется — обоснование хранится отдельно.")
        note.setWordWrap(True)
        note.setStyleSheet(f"color: {MUTED};")
        root.addWidget(note)
        anc = db.partial_ancestors([code]).get(code, {})
        decisions = {d.doc: d for d in db.decisions_for([code]).get(code, [])}
        docs = [d for d in DOC_FLAGS if d in anc or d in decisions]
        area = QScrollArea()
        area.setWidgetResizable(True)
        inner = QWidget()
        lay = QVBoxLayout(inner)
        self.widgets: Dict[str, Tuple[QComboBox, QLineEdit]] = {}
        if not docs:
            lay.addWidget(QLabel("Для этого кода нет состояний «требует проверки» — решение не требуется."))
        for d in docs:
            group = anc.get(d, "")
            box = QGroupBox(DOC_TITLES[d] + (f" · группа {group}" if group else " · группа не найдена"))
            bl = QVBoxLayout(box)
            plist = [p for p in (db.positions_for([group]).get(group, []) if group else []) if p.doc == d]
            texts = [("✔ включено: " if p.kind == K_IN else "✘ исключено: ") + p.name for p in plist]
            ref = QTextEdit()
            ref.setReadOnly(True)
            ref.setMaximumHeight(96)
            ref.setPlainText("\n".join(texts) if texts else "Позиции группы не заданы.")
            bl.addWidget(QLabel("Ограничение из постановления (справочно):"))
            bl.addWidget(ref)
            fr = QFormLayout()
            cmb = QComboBox()
            cmb.addItem("не задано (требует проверки)", D_NONE)
            cmb.addItem("входит — товар соответствует ограничению группы", D_IN)
            cmb.addItem("не входит — товар не соответствует ограничению", D_OUT)
            cur = decisions.get(d)
            if cur:
                cmb.setCurrentIndex(max(0, cmb.findData(cur.verdict)))
            fr.addRow("Решение:", cmb)
            reason = QLineEdit(cur.reason if cur else "")
            reason.setPlaceholderText("Обоснование (можно подставить из группы кнопкой ниже)")
            fr.addRow("Обоснование:", reason)
            bl.addLayout(fr)
            b = QPushButton("Подставить обоснование из группы")
            joined = "; ".join(p.name for p in plist)
            b.clicked.connect(lambda _c=False, cc=cmb, rr=reason, g=group, t=joined:
                              self._fill_reason(cc, rr, g, t))
            bl.addWidget(b)
            if cur and cur.decided_at:
                lab = QLabel(f"Задано: {cur.decided_at}")
                lab.setStyleSheet(f"color: {MUTED};")
                bl.addWidget(lab)
            lay.addWidget(box)
            self.widgets[d] = (cmb, reason)
        lay.addStretch(1)
        area.setWidget(inner)
        root.addWidget(area, 1)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        bb.button(QDialogButtonBox.StandardButton.Save).setText("Сохранить решения")
        bb.button(QDialogButtonBox.StandardButton.Cancel).setText("Отмена")
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        root.addWidget(bb)

    @staticmethod
    def _fill_reason(cmb: QComboBox, reason: QLineEdit, group: str, text: str) -> None:
        v = int(cmb.currentData())
        if not group:
            reason.setText("Группа не определена.")
            return
        if v == D_OUT:
            reason.setText(f"не соответствует ограничению группы {group}: {text}"[:900])
        elif v == D_IN:
            reason.setText(f"соответствует ограничению группы {group}: {text}"[:900])
        else:
            reason.setText("")

    def save(self) -> None:
        for d, (cmb, reason) in self.widgets.items():
            self.db.set_decision(self.code, d, int(cmb.currentData()), reason.text().strip())


class TnvedDialog(QDialog):
    def __init__(self, parent=None, rec: Optional[TnvedRecord] = None):
        super().__init__(parent)
        self.setWindowTitle("Код ТН ВЭД" if rec is None else f"Правка {rec.code}")
        self.setModal(True)
        self.resize(780, 400)
        root = QVBoxLayout(self)
        form = QFormLayout()
        self.e_code = QLineEdit(format_tnved(rec.code) if rec else "")
        self.e_code.setPlaceholderText("например 4412 51 000 1")
        form.addRow("Код ТН ВЭД:", self.e_code)
        root.addLayout(form)
        root.addWidget(QLabel("Собственное наименование (без тире уровня):"))
        self.e_name = QTextEdit(rec.name if rec else "")
        root.addWidget(self.e_name, 1)
        self.chk_trace = QCheckBox("прослеживаемый товар")
        self.chk_trace.setChecked(bool(rec.traceable) if rec else False)
        root.addWidget(self.chk_trace)
        hint = QLabel("Полный путь и уровень пересчитываются автоматически по кодам-предкам.")
        hint.setStyleSheet(f"color: {MUTED};")
        hint.setWordWrap(True)
        root.addWidget(hint)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        bb.button(QDialogButtonBox.StandardButton.Save).setText("Сохранить")
        bb.button(QDialogButtonBox.StandardButton.Cancel).setText("Отмена")
        bb.accepted.connect(self._ok)
        bb.rejected.connect(self.reject)
        root.addWidget(bb)

    def _ok(self):
        code = normalize_tnved(self.e_code.text())
        if not tnved_shape(code):
            QMessageBox.warning(self, "Проверка",
                                "Код ТН ВЭД должен содержать 2, 4, 6, 8, 9 или 10 цифр.")
            return
        if not self.e_name.toPlainText().strip():
            QMessageBox.warning(self, "Проверка", "Заполните наименование.")
            return
        self.accept()

    def data(self) -> Tuple[str, str, int]:
        return (normalize_tnved(self.e_code.text()),
                strip_tnved_dashes(re.sub(r"\s+", " ", self.e_name.toPlainText()).strip()),
                1 if self.chk_trace.isChecked() else 0)


# ---------------------------------------------------------------------------
# Диалог импорта PDF
# ---------------------------------------------------------------------------
class ImportPdfDialog(QDialog):
    MODE_FULL = "полностью"
    MODE_IN = "частично: включено"
    MODE_OUT = "частично: исключено"

    def __init__(self, db: DatabaseManager, parent=None, files: Sequence[str] = ()):
        super().__init__(parent)
        self.db = db
        self._w: Optional[PdfWorker] = None
        self._p: Optional[QProgressDialog] = None
        self.setWindowTitle("Импорт из PDF — предпросмотр")
        self.setModal(True)
        self.resize(1180, 840)
        root = QVBoxLayout(self)
        head = QLabel("1. Документ для каждого файла. «Авто» — программа найдёт «Приложение 1/2/3» внутри PDF.\n"
                      "Если заголовки нестандартные: добавьте файл несколько раз и укажите страницы (3-12, 13-20…).")
        head.setWordWrap(True)
        root.addWidget(head)
        self.tf = QTableWidget(0, 3)
        self.tf.setHorizontalHeaderLabels(["Файл", "Документ", "Страницы (напр. 3-12)"])
        self.tf.verticalHeader().setVisible(False)
        self.tf.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.tf.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.tf.setMinimumHeight(150)
        self.tf.setMaximumHeight(200)
        self.tf.verticalHeader().setDefaultSectionSize(34)
        root.addWidget(self.tf)
        self.cols_files = TableColumns(self.tf, "pdf_files", [430, 250, 200])
        r = QHBoxLayout()
        for t, s in (("Добавить файлы…", self.choose), ("Убрать файл", self.remove_file),
                     ("Проверить структуру PDF", self.structure)):
            b = QPushButton(t)
            b.clicked.connect(s)
            r.addWidget(b)
        r.addStretch(1)
        root.addLayout(r)
        box = QGroupBox("2. Настройки")
        f = QFormLayout(box)
        self.c_groups = QComboBox()
        for n, t in ((2, "2 — вида 01.11"), (3, "3 — вида 01.11.11 (рекомендуется)"),
                     (4, "4 — вида 01.11.11.000")):
            self.c_groups.addItem(t, n)
        self.c_groups.setCurrentIndex(1)
        f.addRow("Минимум групп в коде:", self.c_groups)
        self.c_mode = QComboBox()
        for t, v in (("Авто: таблицы, затем текст", "auto"), ("Только таблицы", "table"),
                     ("Текст: в той же строке", "same"), ("Текст: следующие строки", "below"),
                     ("Текст: предыдущие строки", "above")):
            self.c_mode.addItem(t, v)
        f.addRow("Где искать наименование:", self.c_mode)
        self.chk_reset = QCheckBox("Перед импортом сбросить отметки, позиции и решения выбранных документов")
        f.addRow(self.chk_reset)
        self.chk_names = QCheckBox("Обновлять наименования каталога из текста постановления")
        f.addRow(self.chk_names)
        root.addWidget(box)
        r2 = QHBoxLayout()
        self.b_read = QPushButton("3. Прочитать PDF")
        self.b_read.clicked.connect(self.read)
        r2.addWidget(self.b_read)
        r2.addStretch(1)
        root.addLayout(r2)
        self.report = QTextEdit()
        self.report.setReadOnly(True)
        self.report.setMaximumHeight(130)
        root.addWidget(self.report)
        self.tp = QTableWidget(0, 7)
        self.tp.setHorizontalHeaderLabels(
            ["✔", "Код ОКРБ", "Товар / наименование", "Режим", "Документ", "Стр.", "Примечание"])
        self.tp.verticalHeader().setVisible(False)
        self.tp.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.tp.setAlternatingRowColors(True)
        self.tp.verticalHeader().setDefaultSectionSize(28)
        root.addWidget(self.tp, 1)
        self.cols_preview = TableColumns(self.tp, "pdf_preview", [40, 130, 420, 190, 140, 60, 210])
        r3 = QHBoxLayout()
        for t, s in (("Отметить все", lambda: self.check_all(True)),
                     ("Снять все", lambda: self.check_all(False)),
                     ("→ полностью", lambda: self.set_mode(self.MODE_FULL)),
                     ("→ частично: включено", lambda: self.set_mode(self.MODE_IN)),
                     ("→ частично: исключено", lambda: self.set_mode(self.MODE_OUT))):
            b = QPushButton(t)
            b.clicked.connect(s)
            r3.addWidget(b)
        r3.addStretch(1)
        root.addLayout(r3)
        r4 = QHBoxLayout()
        self.b_commit = QPushButton("4. Записать в базу")
        self.b_commit.setEnabled(False)
        self.b_commit.clicked.connect(self.commit)
        r4.addWidget(self.b_commit)
        r4.addStretch(1)
        b = QPushButton("Закрыть")
        b.clicked.connect(self.reject)
        r4.addWidget(b)
        root.addLayout(r4)
        if files:
            self.add_files(files)

    def choose(self):
        files, _ = QFileDialog.getOpenFileNames(self, "PDF перечней", "", "PDF (*.pdf)")
        if files:
            self.add_files(files)

    def add_files(self, files: Sequence[str]):
        for path in files:
            r = self.tf.rowCount()
            self.tf.insertRow(r)
            it = QTableWidgetItem(os.path.basename(path))
            it.setData(ROLE_CODE, path)
            it.setToolTip(path)
            it.setFlags(it.flags() & ~Qt.ItemFlag.ItemIsEditable)
            self.tf.setItem(r, 0, it)
            c = QComboBox()
            c.addItem("— не импортировать —", None)
            c.addItem("Авто: приложения внутри PDF", "auto")
            for d in DOC_FLAGS:
                c.addItem(DOC_TITLES[d], d)
            g = guess_document(path)
            if g:
                c.setCurrentIndex(max(0, c.findData(g)))
            self.tf.setCellWidget(r, 1, c)
            self.tf.setItem(r, 2, QTableWidgetItem(""))

    def remove_file(self):
        r = self.tf.currentRow()
        if r >= 0:
            self.tf.removeRow(r)

    def structure(self):
        r = self.tf.currentRow()
        if r < 0:
            QMessageBox.information(self, "Нет файла", "Выделите строку с файлом.")
            return
        path = self.tf.item(r, 0).data(ROLE_CODE)
        try:
            sec, w = detect_pdf_sections(path)
        except Exception as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        lines = [f"Файл: {os.path.basename(path)}", ""]
        for s in sec:
            lines.append(f"стр. {s.pages_text()} → {s.label()}   [{s.title}]")
        lines += [""] + [f"⚠ {x}" for x in w]
        QMessageBox.information(self, "Структура PDF", "\n".join(lines))

    def jobs(self):
        out = []
        for r in range(self.tf.rowCount()):
            c: QComboBox = self.tf.cellWidget(r, 1)
            col = c.currentData()
            if not col:
                continue
            out.append((self.tf.item(r, 0).data(ROLE_CODE), str(col),
                        self.tf.item(r, 2).text() if self.tf.item(r, 2) else ""))
        return out

    def read(self):
        jobs = self.jobs()
        if not jobs:
            QMessageBox.information(self, "Нет файлов", "Добавьте файлы и укажите документ.")
            return
        self.b_read.setEnabled(False)
        self.b_commit.setEnabled(False)
        self.tp.setRowCount(0)
        self._w = PdfWorker(jobs, int(self.c_groups.currentData()), str(self.c_mode.currentData()))
        self._p = QProgressDialog("Чтение PDF…", "Отмена", 0, len(jobs), self)
        self._p.setWindowTitle("Импорт")
        self._p.setWindowModality(Qt.WindowModality.WindowModal)
        self._p.setMinimumDuration(0)
        self._p.setAutoClose(False)
        self._p.canceled.connect(self._w.cancel)
        self._w.progress.connect(self.on_progress)
        self._w.done.connect(self.on_done)
        self._w.failed.connect(self.on_failed)
        self._w.start()

    def on_progress(self, d, t, n):
        if self._p:
            self._p.setMaximum(max(1, t))
            self._p.setValue(d)
            self._p.setLabelText(f"Чтение: {n}")

    def _end_progress(self):
        if self._p:
            self._p.close()
            self._p = None
        self.b_read.setEnabled(True)

    def on_failed(self, msg):
        self._end_progress()
        QMessageBox.critical(self, "Ошибка", msg)

    def on_done(self, rows: List[PdfImportRow], rep: List[str]):
        self._end_progress()
        exists = self.db.existing_codes([r.code for r in rows])
        for r in rows:
            r.exists = r.code in exists
        warn = QBrush(QColor("#FDF3E2"))
        t = self.tp
        t.setUpdatesEnabled(False)
        try:
            t.setRowCount(len(rows))
            for i, r in enumerate(rows):
                chk = QTableWidgetItem("")
                chk.setFlags(Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsEnabled
                             | Qt.ItemFlag.ItemIsSelectable)
                chk.setCheckState(Qt.CheckState.Checked)
                t.setItem(i, 0, chk)
                t.setItem(i, 1, QTableWidgetItem(r.code))
                itn = QTableWidgetItem(r.text)
                itn.setToolTip(r.text)
                if r.mode == M_PARTIAL and not r.text:
                    itn.setBackground(warn)
                t.setItem(i, 2, itn)
                mode = self.MODE_FULL if r.mode == M_FULL else (
                    self.MODE_IN if r.kind == K_IN else self.MODE_OUT)
                itm = QTableWidgetItem(mode)
                itm.setForeground(QBrush(QColor(STATUS_FG["full"] if r.mode == M_FULL
                                                else STATUS_FG["part"])))
                t.setItem(i, 3, itm)
                itd = QTableWidgetItem(DOC_SHORT[r.doc])
                itd.setFlags(itd.flags() & ~Qt.ItemFlag.ItemIsEditable)
                t.setItem(i, 4, itd)
                itp = QTableWidgetItem(str(r.page))
                itp.setFlags(itp.flags() & ~Qt.ItemFlag.ItemIsEditable)
                t.setItem(i, 5, itp)
                note = f"{r.source}, " + ("есть в базе" if r.exists else "новый код")
                itx = QTableWidgetItem(note)
                itx.setFlags(itx.flags() & ~Qt.ItemFlag.ItemIsEditable)
                itx.setToolTip(note)
                t.setItem(i, 6, itx)
        finally:
            t.setUpdatesEnabled(True)
        self.report.setPlainText("\n".join(rep))
        self.b_commit.setEnabled(bool(rows))
        QMessageBox.information(self, "Чтение завершено",
                                "\n".join(rep[:30]) + "\n\nПроверьте таблицу и нажмите «Записать в базу».")

    def check_all(self, state: bool):
        st = Qt.CheckState.Checked if state else Qt.CheckState.Unchecked
        for r in range(self.tp.rowCount()):
            self.tp.item(r, 0).setCheckState(st)

    def set_mode(self, mode: str):
        for r in {i.row() for i in self.tp.selectedIndexes()}:
            self.tp.item(r, 3).setText(mode)

    def commit(self):
        items: List[PdfImportRow] = []
        bad: List[str] = []
        docs: Set[str] = set()
        for r in range(self.tp.rowCount()):
            if self.tp.item(r, 0).checkState() != Qt.CheckState.Checked:
                continue
            code = normalize_code(self.tp.item(r, 1).text())
            if not is_code_shape(code, 2):
                bad.append(f"строка {r+1}: «{code}»")
                continue
            text = PDFParser.clean_name(self.tp.item(r, 2).text())
            mtxt = self.tp.item(r, 3).text().strip().lower()
            if mtxt.startswith("полностью"):
                mode, kind = M_FULL, K_IN
            elif "исключ" in mtxt:
                mode, kind = M_PARTIAL, K_OUT
            else:
                mode, kind = M_PARTIAL, K_IN
            dt = self.tp.item(r, 4).text()
            col = next((d for d in DOC_FLAGS if DOC_SHORT[d] == dt), None)
            if col is None:
                bad.append(f"строка {r+1}: неизвестный документ")
                continue
            docs.add(col)
            items.append(PdfImportRow(code, text, col, mode, kind,
                                      int(self.tp.item(r, 5).text() or 0), "", ""))
        if bad:
            QMessageBox.warning(self, "Проверьте данные", "\n".join(bad[:20]))
            return
        if not items:
            QMessageBox.information(self, "Нечего записывать", "Не отмечено ни одной строки.")
            return
        per: Dict[str, int] = {}
        for it in items:
            per[it.doc] = per.get(it.doc, 0) + 1
        breakdown = "\n".join(f"   {DOC_TITLES[d]}: {n}" for d, n in sorted(per.items()))
        reset = sorted(docs) if self.chk_reset.isChecked() else []
        extra = ("\n\nВНИМАНИЕ: будут сброшены прежние отметки, позиции и решения документов:\n"
                 + ", ".join(DOC_TITLES[d] for d in reset)) if reset else ""
        if QMessageBox.question(self, "Подтверждение",
                                f"Записать {len(items)} строк:\n{breakdown}{extra}",
                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                QMessageBox.StandardButton.Yes) != QMessageBox.StandardButton.Yes:
            return
        try:
            new_c, upd_c, pos_c = self.db.import_pdf_rows(items, reset, self.chk_names.isChecked())
            self.db.recompute()
        except (RuntimeError, ValueError) as e:
            logging.error(traceback.format_exc())
            QMessageBox.critical(self, "Ошибка записи", str(e))
            return
        QMessageBox.information(self, "Готово",
                                f"Новых кодов: {new_c}\nОбновлено кодов: {upd_c}\n"
                                f"Позиций записано: {pos_c}\n\nВключение пересчитано.\n{breakdown}")
        self.accept()

    def reject(self):
        if self._w and self._w.isRunning():
            self._w.cancel()
            self._w.wait(5000)
        super().reject()


# ---------------------------------------------------------------------------
# Диалог импорта XLSX (ОКРБ и ТН ВЭД)
# ---------------------------------------------------------------------------
class ImportXlsxDialog(QDialog):
    def __init__(self, db: DatabaseManager, path: str, parent=None, kind="okrb"):
        super().__init__(parent)
        self.db, self.path, self.kind = db, path, kind
        self.rows: List = []
        self.groups: Dict[str, str] = {}
        self._w: Optional[XlsxWorker] = None
        self._p: Optional[QProgressDialog] = None
        self.setWindowTitle("Загрузка классификатора ОКРБ" if kind == "okrb"
                            else "Загрузка каталога ТН ВЭД")
        self.setModal(True)
        self.resize(1120, 780)
        root = QVBoxLayout(self)
        lb = QLabel(f"Файл: {path}\nБаза: {db.db_path}\n"
                    + ("Отметки постановлений не изменяются." if kind == "okrb" else
                       "Коды 2/4/6/8/9/10 цифр. Уровни — по кодам-предкам и тире; "
                       "строки без кода дают контекст; признак «прослеживаемый» сохраняется."))
        lb.setWordWrap(True)
        root.addWidget(lb)
        r = QHBoxLayout()
        r.addWidget(QLabel("Лист:"))
        self.c_sheet = QComboBox()
        self.c_sheet.currentIndexChanged.connect(lambda _i: self.autodetect())
        r.addWidget(self.c_sheet, 1)
        self.chk_all = QCheckBox("читать все листы")
        self.chk_all.setChecked(kind == "tnved")
        r.addWidget(self.chk_all)
        root.addLayout(r)
        box = QGroupBox("Настройки разбора")
        f = QFormLayout(box)
        self.c_code = QComboBox()
        self.c_name = QComboBox()
        self.s_start = QSpinBox()
        self.s_start.setRange(1, 1000000)
        self.c_groups = QComboBox()
        for n, t in ((1, "1 — включая разделы «01»"), (2, "2 — вида 01.11 (рекомендуется)"),
                     (3, "3 — вида 01.11.11")):
            self.c_groups.addItem(t, n)
        self.c_groups.setCurrentIndex(1)
        f.addRow("Колонка с кодом:", self.c_code)
        f.addRow("Колонка с наименованием:", self.c_name)
        f.addRow("Начать со строки №:", self.s_start)
        if kind == "okrb":
            f.addRow("Минимум групп в коде:", self.c_groups)
        self.chk_over = QCheckBox("обновлять уже заполненные наименования")
        self.chk_over.setChecked(True)
        f.addRow(self.chk_over)
        if kind == "okrb":
            self.chk_skipname = QCheckBox("пропускать строки без наименования")
            self.chk_skipname.setChecked(True)
            f.addRow(self.chk_skipname)
            self.chk_skipnum = QCheckBox("пропускать коды, восстановленные из чисел Excel")
            f.addRow(self.chk_skipnum)
        root.addWidget(box)
        r2 = QHBoxLayout()
        self.b_read = QPushButton("Прочитать файл")
        self.b_read.clicked.connect(self.read)
        r2.addWidget(self.b_read)
        self.lbl = QLabel("Колонки определены автоматически — проверьте и нажмите «Прочитать файл».")
        self.lbl.setWordWrap(True)
        r2.addWidget(self.lbl, 1)
        root.addLayout(r2)
        heads = (["Код", "Наименование", "Лист / строка", "Примечание"] if kind == "okrb" else
                 ["Код ТН ВЭД", "Наименование (уровень)", "Ур.", "Группа", "Прослеж.", "Полный путь"])
        self.t = QTableWidget(0, len(heads))
        self.t.setHorizontalHeaderLabels(heads)
        self.t.verticalHeader().setVisible(False)
        self.t.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.t.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.t.setAlternatingRowColors(True)
        self.t.verticalHeader().setDefaultSectionSize(28)
        root.addWidget(self.t, 1)
        self.cols = TableColumns(self.t, f"xlsx_{kind}",
                                 [140, 520, 170, 250] if kind == "okrb"
                                 else [150, 400, 50, 70, 80, 520])
        r3 = QHBoxLayout()
        self.b_commit = QPushButton("Записать в базу")
        self.b_commit.setEnabled(False)
        self.b_commit.clicked.connect(self.commit)
        r3.addWidget(self.b_commit)
        r3.addStretch(1)
        b = QPushButton("Закрыть")
        b.clicked.connect(self.reject)
        r3.addWidget(b)
        root.addLayout(r3)
        self.init_sheets()

    def init_sheets(self):
        try:
            names = xlsx_sheets(self.path)
        except Exception as e:
            QMessageBox.critical(self, "Ошибка файла", str(e))
            names = []
        self.c_sheet.blockSignals(True)
        self.c_sheet.clear()
        if names:
            self.c_sheet.addItems(names)
        else:
            self.c_sheet.addItem("(CSV)")
            self.c_sheet.setEnabled(False)
            self.chk_all.setEnabled(False)
        self.c_sheet.blockSignals(False)
        self.autodetect()

    def autodetect(self):
        sheet = self.c_sheet.currentText() if self.c_sheet.isEnabled() else None
        try:
            sample = xlsx_sample(self.path, sheet)
        except Exception as e:
            QMessageBox.critical(self, "Ошибка чтения", str(e))
            return
        cc, nc, start = detect_columns(sample, int(self.c_groups.currentData()), self.kind)
        ncol = max((len(r) for r in sample), default=1) or 1
        header = sample[start - 1] if 0 < start <= len(sample) else (sample[0] if sample else [])
        for cmb, target in ((self.c_code, cc), (self.c_name, nc)):
            cmb.blockSignals(True)
            cmb.clear()
            for c in range(ncol):
                t = name_from_cell(header[c]) if c < len(header) else ""
                cmb.addItem(get_column_letter(c + 1) + (f" — {t[:45]}" if t else ""), c)
            if target >= 0:
                cmb.setCurrentIndex(min(target, cmb.count() - 1))
            cmb.blockSignals(False)
        self.s_start.setValue(start + 1)

    def read(self):
        sheets = []
        if self.c_sheet.isEnabled():
            sheets = xlsx_sheets(self.path) if self.chk_all.isChecked() else [self.c_sheet.currentText()]
        if self.kind == "tnved":
            args = (self.path, sheets, int(self.c_code.currentData()),
                    int(self.c_name.currentData()), self.s_start.value() - 1)
        else:
            args = (self.path, sheets, int(self.c_code.currentData()), int(self.c_name.currentData()),
                    self.s_start.value() - 1, int(self.c_groups.currentData()),
                    self.chk_skipname.isChecked(), self.chk_skipnum.isChecked())
        self.b_read.setEnabled(False)
        self._w = XlsxWorker(self.kind, args)
        self._p = QProgressDialog("Чтение файла…", "Отмена", 0, max(1, len(sheets)), self)
        self._p.setWindowTitle("Классификатор")
        self._p.setWindowModality(Qt.WindowModality.WindowModal)
        self._p.setMinimumDuration(0)
        self._p.setAutoClose(False)
        self._p.canceled.connect(self._w.cancel)
        self._w.progress.connect(self.on_progress)
        self._w.done.connect(self.on_done)
        self._w.failed.connect(self.on_failed)
        self._w.start()

    def on_progress(self, d, t, n):
        if self._p:
            self._p.setMaximum(max(1, t))
            self._p.setValue(d)
            self._p.setLabelText(f"Лист: {n}")

    def _end(self):
        if self._p:
            self._p.close()
            self._p = None
        self.b_read.setEnabled(True)

    def on_failed(self, msg):
        self._end()
        QMessageBox.critical(self, "Ошибка", msg)

    def on_done(self, rows, st, warns, groups):
        self._end()
        self.rows, self.groups = rows, groups or {}
        shown = rows[:PREVIEW_ROWS]
        self.t.setUpdatesEnabled(False)
        try:
            self.t.setRowCount(len(shown))
            for i, r in enumerate(shown):
                if self.kind == "okrb":
                    vals = [r.code, r.name, f"{r.sheet} / {r.row_no}", r.note]
                else:
                    vals = [format_tnved(r.code), "  " * min(r.depth, 6) + r.name,
                            str(r.depth), r.grp, "да" if r.traceable else "", r.path]
                for c, v in enumerate(vals):
                    it = QTableWidgetItem(v)
                    it.setToolTip(v)
                    self.t.setItem(i, c, it)
        finally:
            self.t.setUpdatesEnabled(True)
        if self.kind == "okrb":
            info = (f"Строк: {st['rows']}. Кодов: {st['unique']}. Без наименования: {st['no_name']}. "
                    f"Из чисел Excel: {st['numeric']}. Дат вместо кода: {st['dates']}. Дублей: {st['dups']}.")
        else:
            leaf = sum(1 for r in rows if len(r.code) == 10)
            info = (f"Строк: {st['rows']}. Кодов: {len(rows)} (из них 10-значных {leaf}). "
                    f"Строк-контекста без кода: {st['context']}. Прослеживаемых: {st['traceable']}. "
                    f"Групп: {len(self.groups)}. Дублей: {st['dups']}.")
        self.lbl.setText(info + "\n" + "\n".join("⚠ " + w for w in warns)
                         + f"\nПоказаны первые {len(shown)} строк; записаны будут все.")
        self.b_commit.setEnabled(bool(rows))

    def commit(self):
        if not self.rows:
            return
        what = "кодов классификатора ОКРБ" if self.kind == "okrb" else "кодов ТН ВЭД"
        if QMessageBox.question(self, "Подтверждение", f"Записать {len(self.rows)} {what}?",
                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                QMessageBox.StandardButton.Yes) != QMessageBox.StandardButton.Yes:
            return
        try:
            if self.kind == "tnved":
                new_c, upd_c = self.db.tnved_import(self.rows, self.groups, self.chk_over.isChecked())
            else:
                new_c, upd_c = self.db.import_catalog(self.rows, self.chk_over.isChecked())
                self.db.recompute()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        QMessageBox.information(self, "Готово", f"Новых кодов: {new_c}\nОбновлено: {upd_c}")
        self.accept()

    def reject(self):
        if self._w and self._w.isRunning():
            self._w.cancel()
            self._w.wait(5000)
        super().reject()


# ---------------------------------------------------------------------------
# Главное окно
# ---------------------------------------------------------------------------
class MainWindow(QMainWindow):
    def __init__(self, db: DatabaseManager):
        super().__init__()
        self.db = db
        self._limit = PAGE_SIZE
        self._order, self._desc = "code", False
        self._tlimit = PAGE_SIZE
        self._t_prefix = ""
        view = ui_state().setdefault("view", {})
        self._compact = bool(view.get("compact", False))
        self._grid = bool(view.get("grid", True))
        self._alt = bool(view.get("alt", True))
        self._indent = bool(view.get("indent", True))
        self._build()
        self.refresh()
        self.refresh_tnved()
        if db.migrated_from_old:
            QMessageBox.information(
                self, "База обновлена",
                "Формат базы обновлён.\n\nКлассификатор и наименования сохранены, но прежние отметки "
                "постановлений сброшены: в них нельзя отличить «код указан явно» от «вычислен по иерархии».\n\n"
                "Импортируйте PDF постановлений заново один раз.")

    def _build(self):
        central = QWidget()
        root = QVBoxLayout(central)
        root.setContentsMargins(14, 12, 14, 12)
        root.setSpacing(10)
        band = QWidget()
        band.setObjectName("HeaderBand")
        band.setStyleSheet(f"""
            #HeaderBand {{ background: qlineargradient(x1:0,y1:0,x2:1,y2:0,
                stop:0 #16233A, stop:0.55 {DEEP}, stop:1 {TEAL}); border-radius: 12px; }}
            #HeaderBand QLabel {{ background: transparent; color: #E8EEF9; }}
        """)
        bl = QHBoxLayout(band)
        bl.setContentsMargins(18, 12, 18, 12)
        tb = QVBoxLayout()
        tb.setSpacing(2)
        t = QLabel(f"{APP_NAME} · {APP_VERSION}")
        tf = QFont()
        tf.setPointSize(15)
        tf.setBold(True)
        t.setFont(tf)
        sub = QLabel(Path(self.db.db_path).name)
        sub.setStyleSheet("color: #B9C8E4; font-size: 12px;")
        tb.addWidget(t)
        tb.addWidget(sub)
        bl.addLayout(tb)
        bl.addStretch(1)
        legend = QHBoxLayout()
        legend.setSpacing(13)
        for key, text in (("full", "да"), ("inh", "по группе"), ("part", "частично"),
                          ("check", "требует проверки"), ("decin", "решение: входит"),
                          ("decout", "решение: не входит")):
            chip = QLabel(f"● {text}")
            chip.setStyleSheet(f"color: {LEGEND_FG[key]}; font-weight: 600;")
            legend.addWidget(chip)
        bl.addLayout(legend)
        root.addWidget(band)
        hint = QLabel("Ширины колонок тянутся мышью и запоминаются · двойной клик по границе заголовка — "
                      "автоширина · правый клик по заголовку — меню колонок · правый клик по строке — действия")
        hint.setStyleSheet(f"color: {MUTED}; font-size: 12px;")
        hint.setWordWrap(True)
        root.addWidget(hint)
        self.tabs = QTabWidget()
        self.tabs.addTab(self._build_okrb_tab(), "ОКРБ · постановления")
        self.tabs.addTab(self._build_tnved_tab(), "ТН ВЭД · каталог")
        root.addWidget(self.tabs, 1)
        self.setCentralWidget(central)
        self.setWindowTitle(f"{APP_NAME} {APP_VERSION} — {self.db.db_path}")
        win = ui_state().get("window", {})
        self.resize(int(win.get("w", 1360)), int(win.get("h", 870)))
        self.statusBar().showMessage(f"База: {self.db.db_path}")
        self._build_menus()
        for seq, slot in (("Ctrl+F", lambda: self.s_name.setFocus()), ("Ctrl+I", self.import_pdf),
                          ("Ctrl+N", self.add_code), ("Ctrl+E", self.edit_current),
                          ("Ctrl+D", self.decision), ("F5", self.refresh_all),
                          ("Delete", self.delete_current), ("Ctrl+R", self.recompute),
                          ("Ctrl+Shift+F", lambda: self.cols.autofit_all())):
            sc = QShortcut(QKeySequence(seq), self)
            sc.activated.connect(slot)
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(250)
        self._timer.timeout.connect(self.refresh)
        self.s_code.textChanged.connect(lambda _t: self._timer.start())
        self.s_name.textChanged.connect(lambda _t: self._timer.start())
        self._ttimer = QTimer(self)
        self._ttimer.setSingleShot(True)
        self._ttimer.setInterval(250)
        self._ttimer.timeout.connect(self.refresh_tnved)
        self.t_code.textChanged.connect(lambda _t: self._ttimer.start())
        self.t_name.textChanged.connect(lambda _t: self._ttimer.start())

    def _build_okrb_tab(self) -> QWidget:
        page = QWidget()
        root = QVBoxLayout(page)
        r = QHBoxLayout()
        r.addWidget(QLabel("Код:"))
        self.s_code = QLineEdit()
        self.s_code.setClearButtonEnabled(True)
        self.s_code.setPlaceholderText("13.92.29")
        r.addWidget(self.s_code, 1)
        r.addWidget(QLabel("Наименование / товар:"))
        self.s_name = QLineEdit()
        self.s_name.setPlaceholderText("ищет и в классификаторе, и в позициях постановлений")
        self.s_name.setClearButtonEnabled(True)
        r.addWidget(self.s_name, 2)
        root.addLayout(r)
        f = QHBoxLayout()
        self.c_filter: Dict[str, QComboBox] = {}
        for d in DOC_FLAGS:
            f.addWidget(QLabel(DOC_SHORT[d] + ":"))
            c = QComboBox()
            for t2, v in (("не важно", FLT_ANY), ("входит (да)", FLT_IN),
                          ("указан явно", FLT_EXPLICIT), ("частично", FLT_PARTIAL),
                          ("требует проверки", FLT_CHECK), ("не входит", FLT_OUT),
                          ("решение: входит", FLT_DEC_IN), ("решение: не входит", FLT_DEC_OUT)):
                c.addItem(t2, v)
            c.currentIndexChanged.connect(lambda _i: self.refresh())
            f.addWidget(c)
            self.c_filter[d] = c
        root.addLayout(f)
        f2 = QHBoxLayout()
        self.chk_pos = QCheckBox("показывать позиции и справки")
        self.chk_pos.setChecked(bool(ui_state().setdefault("view", {}).get("positions", True)))
        self.chk_pos.stateChanged.connect(lambda _s: (self._save_view(), self.refresh()))
        f2.addWidget(self.chk_pos)
        self.chk_empty = QCheckBox("без наименования")
        self.chk_empty.stateChanged.connect(lambda _s: self.refresh())
        f2.addWidget(self.chk_empty)
        b = QPushButton("Очередь проверки")
        b.clicked.connect(self.check_queue)
        f2.addWidget(b)
        b = QPushButton("Сбросить фильтры")
        b.clicked.connect(self.reset_filters)
        f2.addWidget(b)
        f2.addStretch(1)
        root.addLayout(f2)
        self.table = QTableWidget(0, 5)
        self.table.setHorizontalHeaderLabels(
            ["Код ОКРБ", "Наименование / позиция", "Куда включён", "Основание", "Подкодов"])
        hh = self.table.horizontalHeader()
        hh.setSectionsClickable(True)
        hh.sectionClicked.connect(self.sort_by)
        self.table.verticalHeader().setVisible(False)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.doubleClicked.connect(lambda _i: self.edit_current())
        self.table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._okrb_menu)
        root.addWidget(self.table, 1)
        self.cols = TableColumns(self.table, "main", [140, 430, 300, 270, 100])
        self._apply_view()
        b = QHBoxLayout()
        for t2, s in (("Импорт PDF", self.import_pdf), ("Классификатор ОКРБ", self.import_xlsx),
                      ("Добавить код", self.add_code), ("Редактировать", self.edit_current),
                      ("Позиции…", self.positions), ("Решение…", self.decision),
                      ("Удалить", self.delete_current), ("Пересчитать", self.recompute),
                      ("Показать ещё", self.more)):
            btn = QPushButton(t2)
            btn.clicked.connect(s)
            b.addWidget(btn)
            if t2 == "Показать ещё":
                self.b_more = btn
        b.addStretch(1)
        self.lbl = QLabel("")
        self.lbl.setStyleSheet(f"color: {MUTED}; font-weight: 600;")
        b.addWidget(self.lbl)
        root.addLayout(b)
        return page

    def _build_tnved_tab(self) -> QWidget:
        page = QWidget()
        root = QVBoxLayout(page)
        r = QHBoxLayout()
        r.addWidget(QLabel("Код ТН ВЭД:"))
        self.t_code = QLineEdit()
        self.t_code.setClearButtonEnabled(True)
        self.t_code.setPlaceholderText("4412 или 4412 51 000 1")
        r.addWidget(self.t_code, 1)
        r.addWidget(QLabel("Наименование:"))
        self.t_name = QLineEdit()
        self.t_name.setClearButtonEnabled(True)
        self.t_name.setPlaceholderText("например фанера")
        r.addWidget(self.t_name, 2)
        root.addLayout(r)
        f = QHBoxLayout()
        f.addWidget(QLabel("Искать в:"))
        self.t_mode = QComboBox()
        self.t_mode.addItem("собственном наименовании", "name")
        self.t_mode.addItem("всём пути иерархии", "path")
        self.t_mode.currentIndexChanged.connect(lambda _i: self.refresh_tnved())
        f.addWidget(self.t_mode)
        f.addWidget(QLabel("Группа:"))
        self.t_grp = QComboBox()
        self.t_grp.addItem("все", "")
        self.t_grp.setMinimumWidth(260)
        self.t_grp.currentIndexChanged.connect(lambda _i: self.refresh_tnved())
        f.addWidget(self.t_grp)
        self.t_leaf = QCheckBox("только 10-значные")
        self.t_leaf.stateChanged.connect(lambda _s: self.refresh_tnved())
        f.addWidget(self.t_leaf)
        self.t_trace = QCheckBox("только прослеживаемые")
        self.t_trace.stateChanged.connect(lambda _s: self.refresh_tnved())
        f.addWidget(self.t_trace)
        self.t_indent = QCheckBox("отступы по уровням")
        self.t_indent.setChecked(self._indent)
        self.t_indent.stateChanged.connect(lambda _s: (self._save_view(), self.refresh_tnved()))
        f.addWidget(self.t_indent)
        f.addStretch(1)
        root.addLayout(f)
        f2 = QHBoxLayout()
        self.t_branch_lbl = QLabel("")
        self.t_branch_lbl.setStyleSheet(f"color: {ACCENT}; font-weight: 600;")
        f2.addWidget(self.t_branch_lbl)
        b = QPushButton("Ветка выбранного кода")
        b.setToolTip("Показать выбранный код и все его подкоды")
        b.clicked.connect(self.tnved_branch)
        f2.addWidget(b)
        b = QPushButton("Сбросить всё")
        b.clicked.connect(self.reset_tnved)
        f2.addWidget(b)
        f2.addStretch(1)
        root.addLayout(f2)
        self.ttable = QTableWidget(0, 6)
        self.ttable.setHorizontalHeaderLabels(
            ["Код ТН ВЭД", "Наименование", "Ур.", "Группа", "Прослеж.", "Полный путь"])
        self.ttable.verticalHeader().setVisible(False)
        self.ttable.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.ttable.setSelectionMode(QTableWidget.SelectionMode.SingleSelection)
        self.ttable.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.ttable.doubleClicked.connect(lambda _i: self.tnved_edit())
        self.ttable.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.ttable.customContextMenuRequested.connect(self._tnved_menu)
        root.addWidget(self.ttable, 1)
        self.tcols = TableColumns(self.ttable, "tnved", [150, 430, 50, 70, 80, 520])
        self.ttable.setShowGrid(self._grid)
        self.ttable.setAlternatingRowColors(self._alt)
        self.ttable.verticalHeader().setDefaultSectionSize(23 if self._compact else 30)
        b = QHBoxLayout()
        for t2, s in (("Импорт XLSX / CSV", self.import_tnved), ("Добавить код", self.tnved_add),
                      ("Редактировать", self.tnved_edit), ("Удалить", self.tnved_del),
                      ("Экспорт CSV", self.export_tnved), ("Показать ещё", self.tnved_more)):
            btn = QPushButton(t2)
            btn.clicked.connect(s)
            b.addWidget(btn)
            if t2 == "Показать ещё":
                self.tb_more = btn
        b.addStretch(1)
        self.tlbl = QLabel("")
        self.tlbl.setStyleSheet(f"color: {MUTED}; font-weight: 600;")
        b.addWidget(self.tlbl)
        root.addLayout(b)
        return page

    def _build_menus(self):
        m = self.menuBar().addMenu("Файл")
        for t2, s in (("Открыть базу…", self.open_db), ("Создать базу…", self.new_db),
                      ("Резервная копия…", self.backup),
                      ("Экспорт ОКРБ (каталог) CSV…", self.export_catalog),
                      ("Экспорт ОКРБ (позиции) CSV…", self.export_positions),
                      ("Экспорт ОКРБ (решения) CSV…", self.export_decisions),
                      ("Экспорт ТН ВЭД CSV…", self.export_tnved)):
            a = QAction(t2, self)
            a.triggered.connect(s)
            m.addAction(a)
        m.addSeparator()
        a = QAction("Выход", self)
        a.triggered.connect(self.close)
        m.addAction(a)
        mv = self.menuBar().addMenu("Вид")
        self.a_compact = QAction("Компактные строки", self, checkable=True)
        self.a_compact.setChecked(self._compact)
        self.a_compact.triggered.connect(self.toggle_compact)
        mv.addAction(self.a_compact)
        self.a_grid = QAction("Показывать сетку", self, checkable=True)
        self.a_grid.setChecked(self._grid)
        self.a_grid.triggered.connect(self.toggle_grid)
        mv.addAction(self.a_grid)
        self.a_alt = QAction("Чередовать фон строк", self, checkable=True)
        self.a_alt.setChecked(self._alt)
        self.a_alt.triggered.connect(self.toggle_alt)
        mv.addAction(self.a_alt)
        mv.addSeparator()
        mv.addAction("Подогнать все колонки (текущая вкладка)").triggered.connect(
            lambda: (self.cols if self.tabs.currentIndex() == 0 else self.tcols).autofit_all())
        mv.addAction("Сбросить ширины колонок (текущая вкладка)").triggered.connect(
            lambda: (self.cols if self.tabs.currentIndex() == 0 else self.tcols).reset())
        mt = self.menuBar().addMenu("ТН ВЭД")
        mt.addAction("Перестроить иерархию").triggered.connect(self.tnved_rebuild)
        mt.addAction("Импорт XLSX / CSV…").triggered.connect(self.import_tnved)
        mi = self.menuBar().addMenu("Справка")
        mi.addAction("Статистика").triggered.connect(self.stats)
        mi.addAction("О программе").triggered.connect(self.about)

    def _apply_view(self):
        h = 23 if self._compact else 30
        for t in (self.table, getattr(self, "ttable", None)):
            if t is None:
                continue
            t.setShowGrid(self._grid)
            t.setAlternatingRowColors(self._alt)
            t.verticalHeader().setDefaultSectionSize(h)

    def _save_view(self):
        ui_state()["view"] = {"compact": self._compact, "grid": self._grid, "alt": self._alt,
                              "positions": self.chk_pos.isChecked(),
                              "indent": self.t_indent.isChecked() if hasattr(self, "t_indent") else True}
        save_ui_state()

    def toggle_compact(self):
        self._compact = self.a_compact.isChecked()
        self._apply_view()
        self._save_view()

    def toggle_grid(self):
        self._grid = self.a_grid.isChecked()
        self._apply_view()
        self._save_view()

    def toggle_alt(self):
        self._alt = self.a_alt.isChecked()
        self._apply_view()
        self._save_view()

    # -- ОКРБ ----------------------------------------------------------------
    def filters(self):
        return {d: int(self.c_filter[d].currentData()) for d in DOC_FLAGS}

    def reset_filters(self):
        for c in self.c_filter.values():
            c.setCurrentIndex(0)
        self.chk_empty.setChecked(False)
        self.s_code.clear()
        self.s_name.clear()
        self.refresh()

    def check_queue(self):
        for d in DOC_FLAGS:
            self.c_filter[d].setCurrentIndex(self.c_filter[d].findData(FLT_CHECK))
        self.s_code.clear()
        self.s_name.clear()
        self.refresh()

    def sort_by(self, section: int):
        key = {0: "code", 1: "name"}.get(section)
        if not key:
            return
        self._desc = not self._desc if self._order == key else False
        self._order = key
        self.refresh()

    def refresh_all(self):
        self.refresh()
        self.refresh_tnved()

    def refresh(self):
        try:
            recs = self.db.search(self.s_code.text(), self.s_name.text(), self.filters(),
                                  self.chk_empty.isChecked(), False, limit=self._limit,
                                  order_by=self._order, desc=self._desc)
            matched = self.db.count(self.s_code.text(), self.s_name.text(), self.filters(),
                                    self.chk_empty.isChecked(), False)
            total = self.db.count_all()
            show = self.chk_pos.isChecked()
            codes = [r.okrb_code for r in recs]
            pos = self.db.positions_for(codes) if show else {}
            decs = self.db.decisions_for(codes) if show else {}
            anc = self.db.partial_ancestors(codes) if show else {}
            anc_pos = self.db.positions_for(sorted({a for m in anc.values() for a in m.values()})) if anc else {}
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка базы", str(e))
            return
        self.fill(recs, pos, decs, anc, anc_pos)
        self.b_more.setEnabled(len(recs) < matched)
        self.lbl.setText(f"Показано {len(recs)} из {matched} · всего {total}")

    def fill(self, recs: List[OkrbRecord], pos: Dict[str, List[Position]],
             decs: Dict[str, List[Decision]], anc: Dict[str, Dict[str, str]],
             anc_pos: Dict[str, List[Position]]):
        t = self.table
        sub_font = QFont()
        sub_font.setItalic(True)
        bold = QFont()
        bold.setBold(True)
        rows: List[Tuple] = []
        for rec in recs:
            rows.append(("main", rec, None, "", ""))
            if not self.chk_pos.isChecked():
                continue
            plist = pos.get(rec.okrb_code, [])
            for d in rec.partial_docs():
                for p in [x for x in plist if x.doc == d]:
                    rows.append(("pos", rec, p, "", d))
                inc = [x for x in plist if x.doc == d and x.kind == K_IN]
                exc = [x for x in plist if x.doc == d and x.kind == K_OUT]
                if inc:
                    rows.append(("calc_out", rec, None,
                                 f"    ✘ За исключением: прочие товары кода {rec.okrb_code} "
                                 f"(кроме перечисленных выше)", d))
                if exc:
                    rows.append(("calc_in", rec, None,
                                 f"    ✔ Включено: все товары кода {rec.okrb_code}, "
                                 f"кроме перечисленных выше", d))
                if not inc and not exc:
                    rows.append(("calc", rec, None,
                                 "    ⚠ Позиции не заданы — добавьте товар кнопкой «Позиции…»", d))
            amap = anc.get(rec.okrb_code, {})
            dmap = {x.doc: x for x in decs.get(rec.okrb_code, [])}
            for d in rec.decidable_docs():
                g = amap.get(d, "")
                if g:
                    gp = [x for x in anc_pos.get(g, []) if x.doc == d]
                    for p in gp[:3]:
                        mark = "✔ включено" if p.kind == K_IN else "✘ исключено"
                        rows.append(("ref", rec, None,
                                     f"    ↳ из группы {g}: {mark}: {p.name}", d))
                    if len(gp) > 3:
                        rows.append(("ref", rec, None,
                                     f"    ↳ …и ещё {len(gp) - 3} позиций группы {g}", d))
                    if not gp:
                        rows.append(("ref", rec, None,
                                     f"    ↳ группа {g} включена частично, позиции не заданы", d))
                dec = dmap.get(d)
                if dec:
                    word = "входит" if dec.verdict == D_IN else "не входит"
                    rows.append(("dec", rec, None,
                                 f"    ⚖ Решение: {word} — {dec.reason or 'без обоснования'}"
                                 + (f" ({dec.decided_at})" if dec.decided_at else ""), d))
                else:
                    rows.append(("dec", rec, None,
                                 "    ⚖ Решение не задано — кнопка «Решение…» или Ctrl+D", d))
        t.setUpdatesEnabled(False)
        t.blockSignals(True)
        try:
            t.clearContents()
            t.setRowCount(len(rows))
            for i, (kind, rec, p, calc, doc) in enumerate(rows):
                if kind == "main":
                    vals = [rec.okrb_code, rec.product_name, rec.inclusion_text(),
                            rec.basis_text(), str(rec.children_included or "")]
                    st_key = rec.status()
                else:
                    if kind == "pos":
                        mark = "✔ Включено" if p.kind == K_IN else "✘ Исключено"
                        vals = ["", f"    {mark}: {p.name}", DOC_SHORT.get(doc, doc),
                                f"стр. {p.page}, {p.source_file}", ""]
                    else:
                        vals = ["", calc, DOC_SHORT.get(doc, doc),
                                "вычислено" if kind.startswith("calc") else
                                ("справка группы" if kind == "ref" else "решение"), ""]
                for c, v in enumerate(vals):
                    it = QTableWidgetItem(v)
                    it.setData(ROLE_CODE, rec.okrb_code)
                    it.setData(ROLE_POS, p.id if p else 0)
                    it.setData(ROLE_TYPE, kind)
                    it.setData(ROLE_REF, "")
                    it.setToolTip(v)
                    if kind == "main":
                        if c == 0:
                            it.setFont(bold)
                        elif c == 2:
                            it.setForeground(QBrush(QColor(STATUS_FG[st_key])))
                            it.setBackground(QBrush(QColor(STATUS_BG[st_key])))
                            it.setFont(bold)
                        elif c == 4:
                            it.setForeground(QBrush(QColor(ACCENT if rec.children_included else MUTED)))
                        else:
                            it.setForeground(QBrush(QColor(INK if c == 1 else MUTED)))
                    else:
                        if kind == "pos":
                            bg = SUB_BG["in"] if p.kind == K_IN else SUB_BG["out"]
                            fg = STATUS_FG["full"] if p.kind == K_IN else "#B4232A"
                        elif kind == "ref":
                            bg, fg = SUB_BG["ref"], DEEP
                        elif kind == "dec":
                            bg, fg = SUB_BG["dec"], STATUS_FG["check"]
                        else:
                            bg = SUB_BG["out"] if kind == "calc_out" else (
                                SUB_BG["in"] if kind == "calc_in" else SUB_BG["calc"])
                            fg = MUTED
                        it.setBackground(QBrush(QColor(bg)))
                        it.setFont(sub_font)
                        it.setForeground(QBrush(QColor(fg if c in (1, 2) else MUTED)))
                    t.setItem(i, c, it)
        finally:
            t.blockSignals(False)
            t.setUpdatesEnabled(True)

    def _cur(self) -> Tuple[Optional[str], int, str]:
        r = self.table.currentRow()
        if r < 0:
            return None, 0, ""
        it = self.table.item(r, 0)
        return it.data(ROLE_CODE), int(it.data(ROLE_POS) or 0), str(it.data(ROLE_TYPE) or "main")

    def _okrb_menu(self, pos):
        code, _pid, _kind = self._cur()
        if not code:
            return
        m = QMenu(self.table)
        m.addAction("Редактировать код").triggered.connect(self.edit_current)
        m.addAction("Позиции…").triggered.connect(self.positions)
        m.addAction("Решение… (Ctrl+D)").triggered.connect(self.decision)
        m.addSeparator()
        m.addAction("Копировать код").triggered.connect(lambda: QApplication.clipboard().setText(code))
        m.addAction("Копировать строку").triggered.connect(self.copy_row)
        m.addSeparator()
        m.addAction("Удалить").triggered.connect(self.delete_current)
        m.exec(self.table.viewport().mapToGlobal(pos))

    def copy_row(self):
        r = self.table.currentRow()
        if r < 0:
            return
        QApplication.clipboard().setText("\t".join(
            self.table.item(r, c).text() if self.table.item(r, c) else ""
            for c in range(self.table.columnCount())))
        self.statusBar().showMessage("Строка скопирована", 3000)

    def more(self):
        self._limit += PAGE_SIZE
        self.refresh()

    def add_code(self):
        dlg = CodeDialog(self.db, self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        code, name, modes = dlg.result_data()
        try:
            self.db.save_catalog(code, name, overwrite=True)
            self.db.set_mentions(code, modes)
            self.db.recompute()
            self.refresh()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def edit_current(self):
        code, pid, kind = self._cur()
        if not code:
            QMessageBox.information(self, "Правка", "Выберите строку.")
            return
        if kind == "dec":
            self.decision()
            return
        if pid:
            p = next((x for x in self.db.positions_for([code]).get(code, []) if x.id == pid), None)
            if p:
                dlg = PositionDialog(self, code, p)
                if dlg.exec() == QDialog.DialogCode.Accepted:
                    _c, doc, k, name, page, _f = dlg.data()
                    self.db.update_position(pid, doc, k, name, page)
                    self.db.recompute()
                    self.refresh()
            return
        rec = self.db.get(code)
        if rec is None:
            return
        dlg = CodeDialog(self.db, self, rec)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        new_code, name, modes = dlg.result_data()
        try:
            if new_code != code:
                self.db.rename_code(code, new_code)
            self.db.save_catalog(new_code, name, overwrite=True)
            self.db.set_mentions(new_code, modes)
            self.db.recompute()
            self.refresh()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))

    def positions(self):
        code, _pid, _k = self._cur()
        if not code:
            QMessageBox.information(self, "Позиции", "Выберите код в таблице.")
            return
        PositionsDialog(self.db, code, self).exec()
        self.db.recompute()
        self.refresh()

    def decision(self):
        code, _pid, _k = self._cur()
        if not code:
            QMessageBox.information(self, "Решение", "Выберите код в таблице.")
            return
        dlg = DecisionDialog(self.db, code, self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            try:
                dlg.save()
                self.db.recompute()
            except RuntimeError as e:
                QMessageBox.critical(self, "Ошибка", str(e))
                return
            self.refresh()

    def delete_current(self):
        code, pid, _k = self._cur()
        if not code:
            return
        if pid:
            if QMessageBox.question(self, "Удаление позиции", "Удалить эту позицию постановления?",
                                    QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                    QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
                self.db.delete_position(pid)
                self.db.recompute()
                self.refresh()
            return
        if QMessageBox.question(self, "Удаление кода",
                                f"Удалить код {code} вместе с отметками, позициями и решениями?",
                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
            self.db.delete(code)
            self.db.recompute()
            self.refresh()

    def recompute(self):
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            info = self.db.recompute()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        finally:
            QApplication.restoreOverrideCursor()
        self.refresh()
        self.statusBar().showMessage(
            f"Пересчитано: кодов {info['codes']}, отметок {info['mentions']}, решений {info['decisions']}", 6000)

    # -- ТН ВЭД --------------------------------------------------------------
    def _reload_tnved_groups(self):
        cur = self.t_grp.currentData() or ""
        self.t_grp.blockSignals(True)
        self.t_grp.clear()
        self.t_grp.addItem("все", "")
        for g, name in self.db.tnved_group_list():
            self.t_grp.addItem(f"{g} — {name[:60]}" if name else g, g)
        idx = self.t_grp.findData(cur)
        self.t_grp.setCurrentIndex(idx if idx >= 0 else 0)
        self.t_grp.blockSignals(False)

    def reset_tnved(self):
        self.t_code.clear()
        self.t_name.clear()
        self.t_mode.setCurrentIndex(0)
        self.t_grp.setCurrentIndex(0)
        self.t_leaf.setChecked(False)
        self.t_trace.setChecked(False)
        self._t_prefix = ""
        self._tlimit = PAGE_SIZE
        self.refresh_tnved()

    def _t_args(self):
        return dict(code_q=self.t_code.text(), name_q=self.t_name.text(),
                    mode=str(self.t_mode.currentData()), grp=str(self.t_grp.currentData() or ""),
                    only_leaf=self.t_leaf.isChecked(), only_trace=self.t_trace.isChecked(),
                    prefix=self._t_prefix)

    def refresh_tnved(self):
        try:
            self._reload_tnved_groups()
            a = self._t_args()
            recs = self.db.tnved_search(limit=self._tlimit, **a)
            matched = self.db.tnved_count(**a)
            total = self.db.tnved_count_all()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка базы", str(e))
            return
        self._indent = self.t_indent.isChecked()
        self.t_branch_lbl.setText(f"Ветка: {format_tnved(self._t_prefix)}" if self._t_prefix else "")
        t = self.ttable
        bold = QFont()
        bold.setBold(True)
        t.setUpdatesEnabled(False)
        t.blockSignals(True)
        try:
            t.clearContents()
            t.setRowCount(len(recs))
            for i, r in enumerate(recs):
                name = ("    " * min(r.depth, 8) + r.name) if self._indent else r.name
                vals = [format_tnved(r.code), name, str(r.depth), r.grp,
                        "да" if r.traceable else "", r.path]
                for c, v in enumerate(vals):
                    it = QTableWidgetItem(v)
                    it.setData(ROLE_CODE, r.code)
                    it.setToolTip(r.path if c in (1, 5) else v)
                    if c == 0:
                        it.setFont(bold)
                        it.setForeground(QBrush(QColor(INK if r.digits == 10 else DEEP)))
                    elif c == 1:
                        if r.digits < 10:
                            it.setFont(bold)
                        it.setForeground(QBrush(QColor(INK)))
                    elif c == 3:
                        it.setForeground(QBrush(QColor(TEAL)))
                        if r.grp_name:
                            it.setToolTip(f"Группа {r.grp}: {r.grp_name}")
                    elif c == 4:
                        it.setForeground(QBrush(QColor("#0E7C5A" if r.traceable else MUTED)))
                        if r.traceable:
                            it.setBackground(QBrush(QColor("#E6F6EF")))
                    else:
                        it.setForeground(QBrush(QColor(MUTED)))
                    t.setItem(i, c, it)
        finally:
            t.blockSignals(False)
            t.setUpdatesEnabled(True)
        self.tb_more.setEnabled(len(recs) < matched)
        self.tlbl.setText(f"Показано {len(recs)} из {matched} · всего {total}")

    def tnved_more(self):
        self._tlimit += PAGE_SIZE
        self.refresh_tnved()

    def _tcur(self) -> Optional[str]:
        r = self.ttable.currentRow()
        if r < 0:
            return None
        return self.ttable.item(r, 0).data(ROLE_CODE)

    def tnved_branch(self):
        code = self._tcur()
        if not code:
            QMessageBox.information(self, "Ветка", "Выберите код в таблице.")
            return
        self._t_prefix = code
        self.t_code.clear()
        self.t_name.clear()
        self.t_leaf.setChecked(False)
        self._tlimit = PAGE_SIZE
        self.refresh_tnved()

    def _tnved_menu(self, pos):
        code = self._tcur()
        if not code:
            return
        m = QMenu(self.ttable)
        m.addAction("Редактировать").triggered.connect(self.tnved_edit)
        m.addAction("Ветка этого кода").triggered.connect(self.tnved_branch)
        m.addAction("Копировать код (без пробелов)").triggered.connect(
            lambda: QApplication.clipboard().setText(code))
        m.addAction("Копировать код (с пробелами)").triggered.connect(
            lambda: QApplication.clipboard().setText(format_tnved(code)))
        m.addAction("Копировать строку").triggered.connect(self.tnved_copy)
        m.addSeparator()
        m.addAction("Удалить").triggered.connect(self.tnved_del)
        m.exec(self.ttable.viewport().mapToGlobal(pos))

    def tnved_copy(self):
        r = self.ttable.currentRow()
        if r < 0:
            return
        QApplication.clipboard().setText("\t".join(
            self.ttable.item(r, c).text() if self.ttable.item(r, c) else ""
            for c in range(self.ttable.columnCount())))
        self.statusBar().showMessage("Строка скопирована", 3000)

    def tnved_add(self):
        dlg = TnvedDialog(self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            code, name, trace = dlg.data()
            try:
                self.db.tnved_save(code, name, trace)
            except RuntimeError as e:
                QMessageBox.critical(self, "Ошибка", str(e))
                return
            self.refresh_tnved()

    def tnved_edit(self):
        code = self._tcur()
        if not code:
            QMessageBox.information(self, "Правка", "Выберите строку.")
            return
        rec = self.db.tnved_get(code)
        if rec is None:
            return
        dlg = TnvedDialog(self, rec)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            new_code, name, trace = dlg.data()
            try:
                if new_code != code:
                    self.db.tnved_delete(code)
                self.db.tnved_save(new_code, name, trace)
            except RuntimeError as e:
                QMessageBox.critical(self, "Ошибка", str(e))
                return
            self.refresh_tnved()

    def tnved_del(self):
        code = self._tcur()
        if not code:
            return
        if QMessageBox.question(self, "Удаление", f"Удалить код ТН ВЭД {format_tnved(code)}?",
                                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                QMessageBox.StandardButton.No) == QMessageBox.StandardButton.Yes:
            self.db.tnved_delete(code)
            self.refresh_tnved()

    def tnved_rebuild(self):
        QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
        try:
            n = self.db.tnved_rebuild()
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        finally:
            QApplication.restoreOverrideCursor()
        self.refresh_tnved()
        QMessageBox.information(self, "Готово", f"Иерархия перестроена для {n} кодов.")

    def import_tnved(self):
        if openpyxl is None:
            QMessageBox.critical(self, "Ошибка", "Установите openpyxl: pip install openpyxl")
            return
        path, _ = QFileDialog.getOpenFileName(self, "Файл каталога ТН ВЭД", str(APP_DIR),
                                              "Каталог (*.xlsx *.xlsm *.csv)")
        if path:
            ImportXlsxDialog(self.db, path, self, kind="tnved").exec()
            self._tlimit = PAGE_SIZE
            self.refresh_tnved()

    def import_pdf(self):
        if fitz is None:
            QMessageBox.critical(self, "Ошибка", "Установите PyMuPDF: pip install \"PyMuPDF>=1.24\"")
            return
        files, _ = QFileDialog.getOpenFileNames(self, "PDF перечней", "", "PDF (*.pdf)")
        ImportPdfDialog(self.db, self, files).exec()
        self.refresh()

    def import_xlsx(self):
        if openpyxl is None:
            QMessageBox.critical(self, "Ошибка", "Установите openpyxl: pip install openpyxl")
            return
        path, _ = QFileDialog.getOpenFileName(self, "Классификатор ОКРБ", str(APP_DIR),
                                              "Классификатор (*.xlsx *.xlsm *.csv)")
        if path:
            ImportXlsxDialog(self.db, path, self, kind="okrb").exec()
            self.refresh()

    # -- экспорт -------------------------------------------------------------
    def _save_dialog(self, title: str, prefix: str) -> str:
        path, _ = QFileDialog.getSaveFileName(
            self, title, str(APP_DIR / f"{prefix}_{datetime.now():%Y%m%d_%H%M}.csv"), "CSV (*.csv)")
        return path

    def export_catalog(self):
        path = self._save_dialog("Экспорт каталога ОКРБ", "okrb_catalog")
        if not path:
            return
        try:
            recs = self.db.search(self.s_code.text(), self.s_name.text(), self.filters(),
                                  self.chk_empty.isChecked(), False, limit=None,
                                  order_by=self._order, desc=self._desc)
            with open(path, "w", encoding="utf-8-sig", newline="") as fh:
                w = csv.writer(fh, delimiter=";")
                w.writerow(["Код ОКРБ", "Наименование"] + [DOC_TITLES[d] for d in DOC_FLAGS]
                           + ["Основание", "Включённых подкодов"])
                for r in recs:
                    w.writerow([r.okrb_code, r.product_name]
                               + [FLAG_LABEL[r.flag(d)] for d in DOC_FLAGS]
                               + [r.basis_text(), r.children_included])
        except (OSError, RuntimeError) as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        QMessageBox.information(self, "Готово", f"Выгружено строк: {len(recs)}\n{path}")

    def export_positions(self):
        path = self._save_dialog("Экспорт позиций", "okrb_positions")
        if not path:
            return
        try:
            recs = self.db.search(self.s_code.text(), self.s_name.text(), self.filters(),
                                  self.chk_empty.isChecked(), False, limit=None)
            pos = self.db.positions_for([r.okrb_code for r in recs])
            names = {r.okrb_code: r.product_name for r in recs}
            n = 0
            with open(path, "w", encoding="utf-8-sig", newline="") as fh:
                w = csv.writer(fh, delimiter=";")
                w.writerow(["Код ОКРБ", "Наименование по классификатору", "Документ",
                            "Вид позиции", "Товар из постановления", "Страница", "Файл"])
                for r in recs:
                    for p in pos.get(r.okrb_code, []):
                        w.writerow([p.code, names.get(p.code, ""), DOC_TITLES.get(p.doc, p.doc),
                                    "включено" if p.kind == K_IN else "за исключением",
                                    p.name, p.page, p.source_file])
                        n += 1
        except (OSError, RuntimeError) as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        QMessageBox.information(self, "Готово", f"Выгружено позиций: {n}\n{path}")

    def export_decisions(self):
        path = self._save_dialog("Экспорт решений", "okrb_decisions")
        if not path:
            return
        try:
            recs = self.db.search(self.s_code.text(), self.s_name.text(), self.filters(),
                                  self.chk_empty.isChecked(), False, limit=None)
            decs = self.db.decisions_for([r.okrb_code for r in recs])
            anc = self.db.partial_ancestors([r.okrb_code for r in recs])
            names = {r.okrb_code: r.product_name for r in recs}
            n = 0
            with open(path, "w", encoding="utf-8-sig", newline="") as fh:
                w = csv.writer(fh, delimiter=";")
                w.writerow(["Код ОКРБ", "Наименование", "Документ", "Группа-основание",
                            "Решение", "Обоснование", "Дата", "Итоговый статус"])
                for r in recs:
                    for d in decs.get(r.okrb_code, []):
                        w.writerow([d.code, names.get(d.code, ""), DOC_TITLES.get(d.doc, d.doc),
                                    anc.get(d.code, {}).get(d.doc, ""),
                                    "входит" if d.verdict == D_IN else "не входит",
                                    d.reason, d.decided_at, FLAG_LABEL[r.flag(d.doc)]])
                        n += 1
        except (OSError, RuntimeError) as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        QMessageBox.information(self, "Готово", f"Выгружено решений: {n}\n{path}")

    def export_tnved(self):
        path = self._save_dialog("Экспорт ТН ВЭД", "tnved")
        if not path:
            return
        try:
            recs = self.db.tnved_search(limit=None, **self._t_args())
            with open(path, "w", encoding="utf-8-sig", newline="") as fh:
                w = csv.writer(fh, delimiter=";")
                w.writerow(["Код ТН ВЭД", "Код без пробелов", "Наименование", "Уровень",
                            "Группа", "Название группы", "Прослеживаемый", "Код-предок", "Полный путь"])
                for r in recs:
                    w.writerow([format_tnved(r.code), r.code, r.name, r.depth, r.grp,
                                r.grp_name, "да" if r.traceable else "", format_tnved(r.parent), r.path])
        except (OSError, RuntimeError) as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        QMessageBox.information(self, "Готово", f"Выгружено строк: {len(recs)}\n{path}")

    def backup(self):
        path, _ = QFileDialog.getSaveFileName(
            self, "Резервная копия", str(APP_DIR / f"okrb_backup_{datetime.now():%Y%m%d_%H%M}.db"),
            "SQLite (*.db)")
        if path:
            try:
                self.db.backup(path)
                QMessageBox.information(self, "Готово", f"Копия сохранена:\n{path}")
            except RuntimeError as e:
                QMessageBox.critical(self, "Ошибка", str(e))

    def _switch(self, path: str):
        try:
            db = DatabaseManager(path)
        except RuntimeError as e:
            QMessageBox.critical(self, "Ошибка", str(e))
            return
        self.db.close()
        self.db = db
        self.setWindowTitle(f"{APP_NAME} {APP_VERSION} — {self.db.db_path}")
        self._limit = self._tlimit = PAGE_SIZE
        self._t_prefix = ""
        self.refresh_all()

    def open_db(self):
        p, _ = QFileDialog.getOpenFileName(self, "Открыть базу", str(APP_DIR), "SQLite (*.db)")
        if p:
            self._switch(p)

    def new_db(self):
        p, _ = QFileDialog.getSaveFileName(self, "Создать базу", str(APP_DIR / DB_FILENAME), "SQLite (*.db)")
        if p:
            self._switch(p)

    def stats(self):
        s = self.db.stats()
        lines = [f"Кодов ОКРБ: {s['total']}",
                 f"Без наименования: {s['empty_name']}",
                 f"Не найдены ни в одном реестре: {s['nowhere']}",
                 f"Явных отметок: {s['mentions']}",
                 f"Позиций постановлений: {s['positions']}",
                 f"Решений: {s['decisions']}", "",
                 f"Кодов ТН ВЭД: {s['tnved']} (10-значных: {s['tnved_leaf']})",
                 f"Прослеживаемых: {s['tnved_trace']}",
                 f"Названий групп: {s['tnved_groups']}", ""]
        for d in DOC_FLAGS:
            lines.append(f"{DOC_TITLES[d]}: да {s[d+'_full']}, частично {s[d+'_part']}, "
                         f"по группе {s[d+'_inh']}, требует проверки {s[d+'_check']}, "
                         f"решение «входит» {s[d+'_din']}, решение «не входит» {s[d+'_dout']}")
        QMessageBox.information(self, "Статистика", "\n".join(lines))

    def about(self):
        QMessageBox.information(
            self, "О программе",
            f"{APP_NAME} {APP_VERSION}\n\n"
            "ОКРБ — статусы: да / да (по группе) / частично / требует проверки /\n"
            "да или не входит (по решению).\n\n"
            "ТН ВЭД — иерархический каталог: коды 2/4/6/8/9/10 цифр,\n"
            "уровень по кодам-предкам, контекст из строк без кода,\n"
            "признак прослеживаемости, названия групп.\n\n"
            f"База: {self.db.db_path}\nНастройки интерфейса: {UI_PATH}\n"
            f"Лог: {APP_DIR / 'okrb_app.log'}")

    def closeEvent(self, e):
        self.cols.save()
        self.tcols.save()
        self._save_view()
        ui_state()["window"] = {"w": self.width(), "h": self.height()}
        save_ui_state()
        self.db.close()
        super().closeEvent(e)


# ---------------------------------------------------------------------------
# Самотест
# ---------------------------------------------------------------------------
def run_selftests() -> int:
    import shutil
    import tempfile
    ok = True

    def check(title, cond):
        nonlocal ok
        print(("  OK   " if cond else "  FAIL ") + title)
        ok = ok and cond

    print("Коды ОКРБ и иерархия:")
    check("дата не код", not is_code_shape("27.02.2019", 2))
    check("27.12.3 — валидный", is_code_shape("27.12.3", 2))
    check("уровни 27.12.31.700",
          expand_okrb_code("27.12.31.700") ==
          ["27", "27.1", "27.12", "27.12.3", "27.12.31", "27.12.31.7", "27.12.31.70", "27.12.31.700"])
    p = PDFParser()
    items = p.extract_items_from_text("из 10.11.11\nМясо крупного рогатого скота\n10.11.12\nМясо овец")
    check("парсер: 2 кода", len(items) == 2)
    check("парсер: «из» и наименование", bool(items) and items[0].partial and items[0].name.startswith("Мясо"))
    check("«Изделия» не обрезается", p.clean_name("Изделия хлебобулочные") == "Изделия хлебобулочные")
    check("диапазоны страниц", parse_page_ranges("3-12, 15", 30) == [(3, 12), (15, 15)])

    print("ТН ВЭД: коды и уровни:")
    check("пробелы убраны", normalize_tnved("4412 49 000 1") == "4412490001")
    check("10 цифр", tnved_shape("4412490001"))
    check("9 цифр", tnved_shape("441251000"))
    check("6 цифр", tnved_shape("110429"))
    check("4 цифры", tnved_shape("2914"))
    check("5 цифр — не код", not tnved_shape("12345"))
    check("форматирование 10", format_tnved("4412490001") == "4412 49 000 1")
    check("форматирование 9", format_tnved("441251000") == "4412 51 000")
    check("уровень по тире", tnved_dash_level("-- прочие, имеющие") == 2)
    check("тире убраны", strip_tnved_dashes("--- прочие") == "прочие")
    check("длинное тире считается", tnved_dash_level(chr(0x2013) * 4 + " для производства") == 4)
    # Старый формат со стрелками не используем.
    # Каталог ТН ВЭД v.2 разбирается по кодам, тире и строкам-контексту.

    print("ТН ВЭД: разбор структуры файла:")
    src = [
        [None, "ГРУППА 44. ДРЕВЕСИНА И ИЗДЕЛИЯ ИЗ НЕЕ; ДРЕВЕСНЫЙ УГОЛЬ"],
        ["4412", "Фанера клееная, панели фанерованные:"],
        ["4412 51 000", "-- имеющие наружный слой из древесины тропических пород:"],
        ["4412 51 000 1", "- указанных в дополнительном примечании 1"],
        [None, "- прочие:"],
        ["4412 51 000 2", "- лиственных пород"],
        ["прослеживаемый", None],
        ["4412 51 000 9", "- прочие"],
    ]
    tmpd = Path(tempfile.mkdtemp(prefix="okrb5src_"))
    try:
        csvp = tmpd / "t.csv"
        with open(csvp, "w", encoding="utf-8-sig", newline="") as fh:
            w = csv.writer(fh, delimiter=";")
            for r in src:
                w.writerow(["" if v is None else v for v in r])
        rows, groups, st, _w = parse_tnved_source(str(csvp), [], 0, 1, 0)
        by = {r.code: r for r in rows}
        check("найдено 5 кодов", len(rows) == 5)
        check("группа 44 названа", "ДРЕВЕСИНА" in groups.get("44", "").upper())
        check("корень без предка", by.get("4412") is not None and by["4412"].parent == "")
        check("9 цифр — предок 4412", by.get("441251000") and by["441251000"].parent == "4412")
        check("10 цифр — предок 9 цифр",
              by.get("4412510001") and by["4412510001"].parent == "441251000")
        check("глубина 2 у 10-значного", by["4412510001"].depth == 2)
        check("контекст «прочие» попал в путь",
              "прочие" in by["4412510002"].path and "лиственных пород" in by["4412510002"].path)
        check("прослеживаемость привязана", by["4412510002"].traceable == 1)
        check("сосед не прослеживаемый", by["4412510009"].traceable == 0)
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)

    print("База, наследование, решения:")
    tmp = Path(tempfile.mkdtemp(prefix="okrb5_"))
    db = DatabaseManager(tmp / "t.db")
    try:
        for c, n in (("13.92", "Изделия текстильные"), ("13.92.29", "Прочие готовые изделия"),
                     ("13.92.29.100", "Маски и полумаски"), ("13.92.29.200", "Спасательные жилеты и пояса")):
            db.save_catalog(c, n)
        db.set_mentions("13.92.29", {"in_168_app3": M_PARTIAL})
        db.add_position("13.92.29", "in_168_app3", K_IN,
                        "Средства защиты органов дыхания (маски, полумаски, повязки), фильтры", 14, "168.pdf")
        db.recompute()
        check("группа частично", db.get("13.92.29").flag("in_168_app3") == F_PARTIAL)
        check("подкоды требуют проверки", db.get("13.92.29.200").flag("in_168_app3") == F_CHECK)
        check("родитель не наследует", db.get("13.92").flag("in_168_app3") == F_NONE)
        check("найдена группа-основание",
              db.partial_ancestors(["13.92.29.200"]).get("13.92.29.200", {}).get("in_168_app3") == "13.92.29")
        db.set_decision("13.92.29.200", "in_168_app3", D_OUT, "не соответствует ограничению группы")
        db.set_decision("13.92.29.100", "in_168_app3", D_IN, "соответствует ограничению группы")
        db.recompute()
        check("решение «не входит»", db.get("13.92.29.200").flag("in_168_app3") == F_DEC_OUT)
        check("решение «входит»", db.get("13.92.29.100").flag("in_168_app3") == F_DEC_IN)
        check("очередь проверки пуста", db.count(filters={"in_168_app3": FLT_CHECK}) == 0)
        check("фильтр «решение: не входит»", db.count(filters={"in_168_app3": FLT_DEC_OUT}) == 1)
        check("наименование кода не изменилось",
              db.get("13.92.29.200").product_name == "Спасательные жилеты и пояса")
        db.set_decision("13.92.29.200", "in_168_app3", D_NONE)
        db.recompute()
        check("снятие решения возвращает проверку", db.get("13.92.29.200").flag("in_168_app3") == F_CHECK)
        db.set_mentions("13.92.29", {"in_decree_80": M_FULL})
        db.recompute()
        check("полная группа даёт ДА подкодам", db.get("13.92.29.200").flag("in_decree_80") == F_FULL_INH)
        n_new, _n_upd, n_pos = db.import_pdf_rows(
            [PdfImportRow("13.92.29.300", "товар X", "in_168_app3", M_PARTIAL, K_IN, 5, "таблица", "168.pdf")],
            reset_docs=["in_168_app3"])
        db.recompute()
        check("импорт создаёт код и позицию", n_new == 1 and n_pos == 1)
        check("сброс документа снял решения",
              not db.decisions_for(["13.92.29.100"]).get("13.92.29.100"))
        check("поиск по товару постановления", db.count(name_q="товар X") == 1)
        check("поиск без регистра", db.count(name_q="СПАСАТЕЛЬНЫЕ") == 1)

        tr = [TnvedRow(code="4412", name="Фанера клееная:", dashes=0, ord=0),
              TnvedRow(code="441251000", name="имеющие тропических пород:", dashes=2, ord=1),
              TnvedRow(code="4412510002", name="лиственных пород", dashes=1, ord=2,
                       ctx=[(1, "прочие")], traceable=1)]
        build_tnved_paths(tr)
        nn, nu = db.tnved_import(tr, {"44": "Древесина и изделия из нее"}, True)
        check("ТН ВЭД импорт", nn == 3 and db.tnved_count_all() == 3)
        rec = db.tnved_get("4412510002")
        check("ТН ВЭД путь собран", rec is not None and "прочие" in rec.path and "Фанера" in rec.path)
        check("ТН ВЭД уровень", rec is not None and rec.depth == 2)
        check("ТН ВЭД прослеживаемость", rec is not None and rec.traceable == 1)
        check("ТН ВЭД название группы", rec is not None and "Древесина" in rec.grp_name)
        check("ТН ВЭД поиск по коду", len(db.tnved_search(code_q="4412 51")) == 2)
        check("ТН ВЭД поиск по своему наименованию", len(db.tnved_search(name_q="ЛИСТВЕННЫХ")) == 1)
        check("ТН ВЭД поиск по всему пути", len(db.tnved_search(name_q="фанера", mode="path")) == 3)
        check("ТН ВЭД только 10-значные", len(db.tnved_search(only_leaf=True)) == 1)
        check("ТН ВЭД только прослеживаемые", len(db.tnved_search(only_trace=True)) == 1)
        check("ТН ВЭД ветка", len(db.tnved_search(prefix="441251")) == 2)
        check("ТН ВЭД группы", [g for g, _n in db.tnved_group_list()] == ["44"])
    finally:
        db.close()
        shutil.rmtree(tmp, ignore_errors=True)

    print("\n" + ("Все тесты пройдены." if ok else "ЕСТЬ ОШИБКИ — пришлите этот вывод."))
    return 0 if ok else 1


def main() -> int:
    setup_logging()
    if "--selftest" in sys.argv:
        return run_selftests()

    def hook(t, v, tb):
        logging.error("Необработанное исключение", exc_info=(t, v, tb))
        sys.__excepthook__(t, v, tb)

    sys.excepthook = hook
    app = QApplication.instance() or QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setStyleSheet(APP_QSS)

    # Иконка окна и панели задач: внутри сборки или рядом с exe/скриптом
    from PyQt6.QtGui import QIcon
    _base = Path(getattr(sys, "_MEIPASS", "") or Path(__file__).resolve().parent)
    for _cand in (_base / "okrb.ico", APP_DIR / "okrb.ico"):
        if _cand.is_file():
            app.setWindowIcon(QIcon(str(_cand)))
            break
    try:
        db = DatabaseManager(APP_DIR / DB_FILENAME)
    except RuntimeError as e:
        QMessageBox.critical(None, "Ошибка базы", str(e))
        return 1
    win = MainWindow(db)
    win.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())

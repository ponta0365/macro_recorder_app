from __future__ import annotations

import copy
import json
import os
import re
import queue
import threading
import time
from datetime import datetime
from pathlib import Path
import unicodedata
import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog, ttk

try:
    import pyautogui
except ImportError:  # pragma: no cover - handled at runtime
    pyautogui = None

try:
    import pyperclip
except ImportError:  # pragma: no cover - handled at runtime
    pyperclip = None

try:
    from pynput import keyboard, mouse
except ImportError:  # pragma: no cover - handled at runtime
    keyboard = None
    mouse = None


MODIFIER_KEYS = {
    "ctrl",
    "alt",
    "shift",
    "win",
}

SPECIAL_STOP_KEYS = {"esc"}

TEXT_BREAK_KEYS = {
    "enter",
    "tab",
    "esc",
    "backspace",
    "delete",
    "up",
    "down",
    "left",
    "right",
    "home",
    "end",
    "pageup",
    "pagedown",
}

IME_TOGGLE_KEYS = {
    "kana",
    "hiragana",
    "katakana",
    "henkan",
    "muhenkan",
    "convert",
    "nonconvert",
    "zenkaku_hankaku",
    "alphanumeric",
    "japanese_hiragana",
    "japanese_katakana",
}


def _now_iso() -> str:
    return datetime.now().astimezone().isoformat(timespec="seconds")


def _clamp_float(value: str, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _clamp_int(value: str, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def _is_printable_char(char: str) -> bool:
    return bool(char) and len(char) == 1 and char.isprintable() and char not in {"\x00", "\r"}


def _input_mode_for_char(char: str) -> str:
    if not char:
        return "ascii"
    if len(char) != 1:
        return "mixed"
    if ord(char) < 128:
        return "ascii"
    width = unicodedata.east_asian_width(char)
    if width == "H":
        return "halfwidth"
    if width in {"F", "W"}:
        return "japanese"
    if char.isdigit() or char.isalpha():
        return "mixed"
    return "japanese"


def _input_mode_for_text(text: str) -> str:
    modes = {_input_mode_for_char(ch) for ch in text if ch.strip() or ch == " "}
    if not modes:
        return "ascii"
    if len(modes) == 1:
        return next(iter(modes))
    if modes <= {"ascii", "halfwidth"}:
        return "ascii"
    return "mixed"


def _pretty_modifier(name: str) -> str:
    mapping = {
        "ctrl": "Ctrl",
        "alt": "Alt",
        "shift": "Shift",
        "win": "Win",
    }
    return mapping.get(name.lower(), name)


def _pretty_key_name(name: str) -> str:
    if len(name) == 1:
        return name.upper()
    mapping = {
        "enter": "Enter",
        "tab": "Tab",
        "esc": "Esc",
        "backspace": "Backspace",
        "delete": "Delete",
        "space": "Space",
        "up": "Up",
        "down": "Down",
        "left": "Left",
        "right": "Right",
        "home": "Home",
        "end": "End",
        "pageup": "PageUp",
        "pagedown": "PageDown",
        "insert": "Insert",
    }
    if name.startswith("f") and name[1:].isdigit():
        return name.upper()
    return mapping.get(name.lower(), name)


def _normalize_hotkey_name(name: str) -> str:
    name = name.lower()
    if name in {"control", "ctrl_l", "ctrl_r"}:
        return "ctrl"
    if name in {"alt_l", "alt_r", "alt gr"}:
        return "alt"
    if name in {"shift_l", "shift_r"}:
        return "shift"
    if name in {"cmd", "cmd_l", "cmd_r", "windows", "left windows", "right windows", "super"}:
        return "win"
    return name


def _pyautogui_key_name(name: str) -> str:
    name = _normalize_hotkey_name(name)
    if name == "win":
        return "winleft"
    if name == "pageup":
        return "pageup"
    if name == "pagedown":
        return "pagedown"
    return name


def _default_project_hotkey(number: int | None = None) -> str:
    number = 1 if number is None else max(1, min(9, int(number)))
    return f"ctrl+alt+{number}"


def _pretty_project_hotkey(hotkey: str) -> str:
    if not hotkey:
        return "-"
    parts = hotkey.lower().split("+")
    pretty = []
    for part in parts:
        if part in {"ctrl", "alt", "shift", "win"}:
            pretty.append(_pretty_modifier(part))
        else:
            pretty.append(part.upper() if part.isdigit() else _pretty_key_name(part))
    return " + ".join(pretty)


def _hotkey_digit(hotkey: str) -> int | None:
    if not hotkey:
        return None
    parts = hotkey.lower().split("+")
    if parts[:2] == ["ctrl", "alt"] and len(parts) == 3 and parts[2].isdigit():
        digit = int(parts[2])
        if 1 <= digit <= 9:
            return digit
    return None


class RecorderApp:
    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        self.root.title("キーボード・マウス操作記録アプリ")
        self.root.geometry("1500x860")
        self.app_dir = Path(__file__).resolve().parent
        self.recent_index_path = self.app_dir / ".macro_recorder_recent.json"

        self.ui_queue: queue.Queue[tuple[str, object]] = queue.Queue()

        self.project = self._new_project()
        self.current_path: Path | None = None
        self.recent_project_paths: list[str] = self._load_recent_project_paths()

        self.recording = False
        self.playing = False

        self.recording_stop_event = threading.Event()
        self.playback_stop_event = threading.Event()
        self.recording_thread: threading.Thread | None = None
        self.playback_thread: threading.Thread | None = None
        self.playback_hotkey_listener = None
        self.project_hotkey_listener = None
        self.project_hotkey_ctrl_down = False
        self.project_hotkey_alt_down = False
        self.project_hotkey_armed_digit: int | None = None
        self.shortcut_drag_row_id: str | None = None
        self.shortcut_row_map: dict[str, dict[str, object]] = {}

        self.recording_start_monotonic = 0.0
        self.last_committed_ts: float | None = None
        self.text_buffer = ""
        self.text_buffer_mode: str | None = None
        self.text_buffer_start_ts: float | None = None
        self.text_buffer_last_ts: float | None = None
        self.active_modifiers: set[str] = set()
        self.last_click_step_index: int | None = None
        self.last_click_signature: tuple[str, int, int, int] | None = None
        self.last_click_ts: float | None = None
        self.last_move_ts: float | None = None
        self.last_move_point: tuple[int, int] | None = None
        self.record_mouse_move_var = tk.BooleanVar(value=False)

        self._build_ui()
        self._start_project_hotkey_listener()
        self._refresh_tree()
        self._poll_ui_queue()
        self._refresh_status()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    def _new_project(self) -> dict:
        try:
            width, height = pyautogui.size() if pyautogui else (0, 0)
        except Exception:
            width, height = (0, 0)
        return {
            "schema_version": 1,
            "project_name": f"project_{datetime.now().strftime('%Y%m%d_%H%M%S')}",
            "project_hotkey": "",
            "created_at": _now_iso(),
            "updated_at": _now_iso(),
            "workflow_enabled": False,
            "workflow": [],
            "screen": {
                "width": width,
                "height": height,
                "dpi_scale": 1.0,
            },
            "launcher": {
                "type": "url",
                "target": "",
                "args": "",
                "working_dir": "",
                "wait_seconds": 0.0,
                "enabled": False,
            },
            "settings": {
                "shortcut_timeout_seconds": 1.0,
                "double_click_threshold_seconds": 0.4,
                "test_playback_step_limit": 5,
                "countdown_seconds": 3,
                "stop_key": "esc",
                "record_mouse_move": False,
                "confirm_before_playback": True,
            },
            "steps": [],
            "execution_log": [],
        }

    def _load_recent_project_paths(self) -> list[str]:
        try:
            if self.recent_index_path.exists():
                with self.recent_index_path.open("r", encoding="utf-8") as f:
                    data = json.load(f)
                paths = data.get("recent_paths", [])
                if isinstance(paths, list):
                    return [str(path) for path in paths if path]
        except Exception:
            pass
        return []

    def _save_recent_project_paths(self) -> None:
        payload = {
            "version": 1,
            "recent_paths": self.recent_project_paths[:50],
        }
        try:
            with self.recent_index_path.open("w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _touch_recent_project(self, path: Path) -> None:
        normalized = str(path.resolve())
        self.recent_project_paths = [p for p in self.recent_project_paths if p != normalized]
        self.recent_project_paths.insert(0, normalized)
        self._save_recent_project_paths()

    def _available_project_files(self) -> list[Path]:
        files: list[Path] = []
        seen: set[str] = set()

        def add_path(path: Path) -> None:
            normalized = str(path.resolve())
            if normalized in seen:
                return
            if not path.exists():
                return
            seen.add(normalized)
            files.append(path)

        if self.current_path is not None:
            add_path(self.current_path)
        for raw_path in self.recent_project_paths:
            try:
                add_path(Path(raw_path))
            except Exception:
                continue
        for path in sorted(self.app_dir.glob("*.json")):
            if path.name == self.recent_index_path.name:
                continue
            add_path(path)
        return files

    def _sorted_project_files(self) -> list[Path]:
        recent_lookup = {p: idx for idx, p in enumerate(self.recent_project_paths)}
        return sorted(
            self._available_project_files(),
            key=lambda path: (
                0 if str(path.resolve()) in recent_lookup else 1,
                recent_lookup.get(str(path.resolve()), 10**9),
                path.name.lower(),
            ),
        )

    def _sorted_project_files_by_hotkey(self) -> list[Path]:
        keyed: list[tuple[int, int, str, Path]] = []
        fallback: list[Path] = []
        for path in self._available_project_files():
            digit = _hotkey_digit(self._project_hotkey_from_path(path))
            if digit is None:
                fallback.append(path)
                continue
            keyed.append((digit, 0 if str(path.resolve()) in self.recent_project_paths else 1, path.name.lower(), path))
        keyed.sort(key=lambda item: (item[0], item[1], item[2]))
        fallback.sort(key=lambda path: path.name.lower())
        return [item[3] for item in keyed] + fallback

    def _normalize_project_hotkey(self, hotkey: str) -> str:
        text = str(hotkey or "").strip().lower().replace(" ", "")
        if not text:
            return ""
        parts = [part for part in text.split("+") if part]
        if len(parts) != 3:
            return ""
        if parts[:2] != ["ctrl", "alt"]:
            return ""
        if not parts[2].isdigit():
            return ""
        digit = int(parts[2])
        if not 1 <= digit <= 9:
            return ""
        return f"ctrl+alt+{digit}"

    def _project_hotkey_used_by_other(self, hotkey: str, ignore_path: Path | None = None) -> tuple[bool, Path | None]:
        target = self._normalize_project_hotkey(hotkey)
        if not target:
            return False, None
        ignore_norm = str(ignore_path.resolve()) if ignore_path is not None else None
        current_norm = str(self.current_path.resolve()) if self.current_path is not None else None
        if self._normalize_project_hotkey(self.project.get("project_hotkey", "")) == target:
            if current_norm is None or current_norm != ignore_norm:
                return True, self.current_path
        for path in self._available_project_files():
            normalized = str(path.resolve())
            if ignore_norm is not None and normalized == ignore_norm:
                continue
            if self._project_hotkey_from_path(path) == target:
                return True, path
        return False, None

    def _project_hotkey_from_path(self, path: Path) -> str:
        try:
            with path.open("r", encoding="utf-8") as f:
                data = json.load(f)
            return self._normalize_project_hotkey(data.get("project_hotkey", ""))
        except Exception:
            return ""

    def _project_hotkey_candidates(self, ignore_path: Path | None = None) -> list[int]:
        used = set()
        ignore_norm = str(ignore_path.resolve()) if ignore_path is not None else None
        current_norm = str(self.current_path.resolve()) if self.current_path is not None else None
        current_hotkey = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
        if current_hotkey:
            if ignore_norm is None or current_norm != ignore_norm:
                digit = _hotkey_digit(current_hotkey)
                if digit is not None:
                    used.add(digit)
        for path in self._available_project_files():
            normalized = str(path.resolve())
            if ignore_norm is not None and normalized == ignore_norm:
                continue
            digit = _hotkey_digit(self._project_hotkey_from_path(path))
            if digit is not None:
                used.add(digit)
        return [digit for digit in range(1, 10) if digit not in used]

    def _ensure_project_hotkey(self, ignore_path: Path | None = None) -> str:
        current = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
        if current:
            return current
        candidates = self._project_hotkey_candidates(ignore_path=ignore_path)
        if not candidates:
            return ""
        hotkey = _default_project_hotkey(candidates[0])
        self.project["project_hotkey"] = hotkey
        self._sync_project_hotkey_var()
        return hotkey

    def _sync_project_hotkey_var(self) -> None:
        if hasattr(self, "project_hotkey_var"):
            self.project_hotkey_var.set(_pretty_project_hotkey(self.project.get("project_hotkey", "")))

    def _project_hotkey_target(self, number: int) -> Path | None:
        if number < 1:
            return None
        hotkey = _default_project_hotkey(number)
        for path in self._sorted_project_files_by_hotkey():
            if self._project_hotkey_from_path(path) == hotkey:
                return path
        return None

    def _start_project_hotkey_listener(self) -> None:
        if keyboard is None:
            return

        if self.project_hotkey_listener is not None:
            try:
                self.project_hotkey_listener.stop()
            except Exception:
                pass
            self.project_hotkey_listener = None

        hotkeys: dict[str, object] = {}

        for number in range(1, 10):
            hotkey = f"<ctrl>+<alt>+{number}"

            def make_callback(n: int) -> callable:
                def callback() -> None:
                    try:
                        if self.recording or self.playing:
                            return
                        assigned = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
                        if assigned == _default_project_hotkey(n):
                            self.root.after(0, lambda: self._play_current_project_from_hotkey(n))
                            return
                        target = self._project_hotkey_target(n)
                        if target is None:
                            self.root.after(0, lambda: self._append_log(f"{_pretty_project_hotkey(_default_project_hotkey(n))}: 対象のプロジェクトがありません"))
                            return
                        self.root.after(0, lambda p=target, digit=n: self._play_project_from_hotkey(p, digit))
                    except Exception as exc:
                        self.root.after(0, lambda e=exc: self._append_log(f"ホットキー処理エラー: {e}"))

                return callback

            hotkeys[hotkey] = make_callback(number)

        listener = keyboard.GlobalHotKeys(hotkeys)
        listener.daemon = True
        listener.start()
        self.project_hotkey_listener = listener

    def _play_project_from_hotkey(self, path: Path, number: int) -> None:
        if self.recording or self.playing:
            return
        self._append_log(f"{_pretty_project_hotkey(_default_project_hotkey(number))}: {path.stem} を再生します")
        if self._load_project_from_path(path):
            self.start_playback(test_mode=False)

    def _play_current_project_from_hotkey(self, number: int) -> None:
        if self.recording or self.playing:
            return
        self._append_log(f"{_pretty_project_hotkey(_default_project_hotkey(number))}: 現在のプロジェクトを再生します")
        self.start_playback(test_mode=False)

    def _project_summary(self, path: Path) -> dict:
        summary = {
            "path": str(path),
            "project_name": path.stem,
            "updated_at": "",
            "steps": 0,
            "recent_rank": None,
            "project_hotkey": "",
        }
        try:
            with path.open("r", encoding="utf-8") as f:
                data = json.load(f)
            summary["project_name"] = data.get("project_name", path.stem)
            summary["updated_at"] = data.get("updated_at", "")
            summary["steps"] = len(data.get("steps", []))
            summary["project_hotkey"] = self._normalize_project_hotkey(data.get("project_hotkey", ""))
        except Exception:
            pass
        normalized = str(path.resolve())
        if normalized in self.recent_project_paths:
            summary["recent_rank"] = self.recent_project_paths.index(normalized) + 1
        return summary

    def _build_ui(self) -> None:
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(1, weight=1)

        top = ttk.Frame(self.root, padding=8)
        top.grid(row=0, column=0, sticky="ew")
        top.columnconfigure(1, weight=1)
        top.columnconfigure(3, weight=1)

        ttk.Label(top, text="プロジェクト名").grid(row=0, column=0, sticky="w")
        self.project_name_var = tk.StringVar(value=self.project["project_name"])
        ttk.Entry(top, textvariable=self.project_name_var, width=24).grid(row=0, column=1, sticky="w", padx=(6, 12))
        ttk.Label(top, text="ショートカット").grid(row=0, column=2, sticky="w")
        self.project_hotkey_var = tk.StringVar(value=_pretty_project_hotkey(self.project.get("project_hotkey", "")))
        ttk.Entry(top, textvariable=self.project_hotkey_var, width=16, state="readonly").grid(row=0, column=3, sticky="ew", padx=(6, 12))
        ttk.Button(top, text="設定", command=self.edit_project_hotkey).grid(row=0, column=4, sticky="w", padx=(0, 12))
        ttk.Checkbutton(
            top,
            text="マウス移動を記録",
            variable=self.record_mouse_move_var,
            command=self._toggle_record_mouse_move,
        ).grid(row=0, column=5, sticky="w", padx=(0, 12))
        self.playback_confirm_var = tk.BooleanVar(value=bool(self.project["settings"].get("confirm_before_playback", True)))
        ttk.Checkbutton(
            top,
            text="再生前確認",
            variable=self.playback_confirm_var,
            command=self._toggle_playback_confirm,
        ).grid(row=0, column=6, sticky="w", padx=(0, 12))

        actions = ttk.Frame(top)
        actions.grid(row=1, column=0, columnspan=6, sticky="w", pady=(8, 0))

        ttk.Button(actions, text="記録開始", command=self.start_recording).pack(side="left", padx=4)
        ttk.Button(actions, text="記録停止", command=self.stop_recording).pack(side="left", padx=4)
        ttk.Button(actions, text="再生", command=lambda: self.start_playback(test_mode=False)).pack(side="left", padx=4)
        ttk.Button(actions, text="テスト再生", command=lambda: self.start_playback(test_mode=True)).pack(side="left", padx=4)
        ttk.Button(actions, text="フロー", command=self.edit_workflow).pack(side="left", padx=4)
        ttk.Button(actions, text="保存", command=self.save_project).pack(side="left", padx=4)
        ttk.Button(actions, text="一覧", command=self.open_project_browser).pack(side="left", padx=4)
        ttk.Button(actions, text="読み込み", command=self.load_project).pack(side="left", padx=4)
        ttk.Button(actions, text="起動設定", command=self.edit_launcher).pack(side="left", padx=4)

        main = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main.grid(row=1, column=0, sticky="nsew")

        left = ttk.Frame(main, padding=8)
        left.columnconfigure(0, weight=1)
        left.rowconfigure(1, weight=1)
        main.add(left, weight=3)

        columns = ("no", "auto_label", "display_name", "action", "content", "coords", "wait", "enabled")
        self.tree = ttk.Treeview(left, columns=columns, show="headings", selectmode="browse", height=18)
        headings = {
            "no": "No",
            "auto_label": "自動ラベル",
            "display_name": "表示名",
            "action": "操作",
            "content": "内容",
            "coords": "座標",
            "wait": "待機",
            "enabled": "有効",
        }
        widths = {
            "no": 50,
            "auto_label": 120,
            "display_name": 190,
            "action": 100,
            "content": 220,
            "coords": 110,
            "wait": 70,
            "enabled": 60,
        }
        for key in columns:
            self.tree.heading(key, text=headings[key])
            self.tree.column(key, width=widths[key], anchor="w", stretch=True)
        self.tree.grid(row=1, column=0, sticky="nsew")
        self.tree.bind("<<TreeviewSelect>>", self._on_step_select)
        self.tree.bind("<ButtonRelease-1>", self._on_tree_click)

        yscroll = ttk.Scrollbar(left, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=yscroll.set)
        yscroll.grid(row=1, column=1, sticky="ns")

        edit = ttk.LabelFrame(main, text="選択中の操作", padding=8)
        main.add(edit, weight=2)
        edit.columnconfigure(1, weight=1)

        self.selected_step_id: str | None = None
        self.selected_step_index: int | None = None
        self.display_name_entry: ttk.Entry | None = None
        self.content_entry: ttk.Entry | None = None
        self.wait_entry: ttk.Entry | None = None
        self.inline_editor: tk.Toplevel | None = None
        self.inline_editor_entry: ttk.Entry | None = None
        self.inline_editor_item: str | None = None
        self.inline_editor_column: str | None = None
        self.inline_editor_step_id: str | None = None

        self.step_type_var = tk.StringVar(value="-")
        self.auto_label_var = tk.StringVar(value="-")
        self.display_name_var = tk.StringVar()
        self.content_var = tk.StringVar()
        self.wait_var = tk.StringVar(value="0.0")
        self.enabled_var = tk.BooleanVar(value=True)
        self.confirm_var = tk.BooleanVar(value=False)
        self.step_confirm_note_var = tk.StringVar(value="")
        self.step_meta_var = tk.StringVar(value="")

        row = 0
        for label, var, widget in [
            ("種別", self.step_type_var, ttk.Label),
            ("自動ラベル", self.auto_label_var, ttk.Label),
            ("表示名", self.display_name_var, ttk.Entry),
            ("内容", self.content_var, ttk.Entry),
            ("待機秒", self.wait_var, ttk.Entry),
        ]:
            ttk.Label(edit, text=label).grid(row=row, column=0, sticky="w", pady=4)
            if widget is ttk.Entry:
                entry = widget(edit, textvariable=var)
                entry.grid(row=row, column=1, sticky="ew", pady=4)
                if label == "表示名":
                    self.display_name_entry = entry
                elif label == "内容":
                    self.content_entry = entry
                elif label == "待機秒":
                    self.wait_entry = entry
            else:
                widget(edit, textvariable=var).grid(row=row, column=1, sticky="w", pady=4)
            row += 1

        ttk.Checkbutton(edit, text="有効", variable=self.enabled_var).grid(row=row, column=0, sticky="w", pady=4)
        ttk.Checkbutton(edit, text="実行時確認", variable=self.confirm_var).grid(row=row, column=1, sticky="w", pady=4)
        row += 1

        ttk.Button(edit, text="変更を適用", command=self.apply_step_edit).grid(row=row, column=0, sticky="ew", pady=(8, 4))
        ttk.Button(edit, text="削除", command=self.delete_selected_step).grid(row=row, column=1, sticky="ew", pady=(8, 4))
        row += 1
        ttk.Label(edit, textvariable=self.step_meta_var, wraplength=340, justify="left").grid(row=row, column=0, columnspan=2, sticky="w", pady=(8, 4))
        row += 1

        ttk.Separator(edit).grid(row=row, column=0, columnspan=2, sticky="ew", pady=8)
        row += 1
        ttk.Button(edit, text="表示名を入力", command=self.rename_project).grid(row=row, column=0, sticky="ew", pady=4)
        ttk.Button(edit, text="全体を新規", command=self.new_project_action).grid(row=row, column=1, sticky="ew", pady=4)
        ttk.Label(edit, textvariable=self.step_confirm_note_var, wraplength=340, justify="left").grid(row=row + 1, column=0, columnspan=2, sticky="w", pady=(4, 0))

        self.display_name_entry.bind("<Return>", lambda _event: self.apply_step_edit())
        self.content_entry.bind("<Return>", lambda _event: self.apply_step_edit())
        self.wait_entry.bind("<Return>", lambda _event: self.apply_step_edit())

        bottom = ttk.LabelFrame(self.root, text="実行ログ", padding=8)
        bottom.grid(row=2, column=0, sticky="nsew")
        self.root.rowconfigure(2, weight=0)
        bottom.columnconfigure(0, weight=1)
        bottom.rowconfigure(0, weight=1)

        self.log_text = tk.Text(bottom, height=10, wrap="word")
        self.log_text.grid(row=0, column=0, sticky="nsew")
        log_scroll = ttk.Scrollbar(bottom, orient="vertical", command=self.log_text.yview)
        log_scroll.grid(row=0, column=1, sticky="ns")
        self.log_text.configure(yscrollcommand=log_scroll.set)

        status = ttk.Frame(self.root, padding=(8, 0, 8, 8))
        status.grid(row=3, column=0, sticky="ew")
        self.status_var = tk.StringVar(value="")
        ttk.Label(status, textvariable=self.status_var).grid(row=0, column=0, sticky="w")

    def _refresh_status(self) -> None:
        mode = "記録中" if self.recording else "再生中" if self.playing else "待機中"
        self.status_var.set(
            f"{mode} | steps={len(self.project['steps'])} | 移動記録={'ON' if self.record_mouse_move_var.get() else 'OFF'} | Ctrl+Alt+1..9でプロジェクト再生 | Escで停止 | {self.project['project_name']}"
        )
        self._sync_project_hotkey_var()
        self._refresh_shortcut_list()

    def _refresh_shortcut_list(self) -> None:
        if not hasattr(self, "shortcut_tree"):
            return
        self.shortcut_tree.delete(*self.shortcut_tree.get_children())
        self.shortcut_row_map = {}

        def add_row(
            iid: str,
            slot: str,
            hotkey: str,
            name: str,
            recent: str,
            status: str,
            path_label: str,
            tag: str,
        ) -> None:
            self.shortcut_tree.insert(
                "",
                "end",
                iid=iid,
                values=(
                    slot,
                    hotkey or "-",
                    name,
                    recent,
                    status,
                    path_label,
                ),
                tags=(tag,),
            )
            self.shortcut_row_map[iid] = {
                "slot": slot,
                "hotkey": hotkey or "",
                "path": path_label,
                "status": status,
                "tag": tag,
            }

        current_hotkey = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
        current_recent = ""
        if self.current_path is not None:
            normalized = str(self.current_path.resolve())
            if normalized in self.recent_project_paths:
                current_recent = f"#{self.recent_project_paths.index(normalized) + 1}"

        current_path_text = str(self.current_path) if self.current_path is not None else "(未保存)"
        current_status = "割当済み" if current_hotkey else "未割当"
        add_row(
            "current",
            "現在",
            _pretty_project_hotkey(current_hotkey),
            self.project.get("project_name", "project"),
            current_recent,
            current_status,
            current_path_text,
            "current" if current_hotkey else "unassigned",
        )

        slot_owner: dict[int, dict[str, object]] = {}
        for path in self._available_project_files():
            summary = self._project_summary(path)
            digit = _hotkey_digit(summary.get("project_hotkey", ""))
            if digit is None:
                continue
            if digit not in slot_owner:
                slot_owner[digit] = summary

        current_norm = str(self.current_path.resolve()) if self.current_path is not None else None
        for digit in range(1, 10):
            owner = slot_owner.get(digit)
            if owner is None and current_hotkey == _default_project_hotkey(digit):
                owner = {
                    "path": str(self.current_path) if self.current_path is not None else "",
                    "project_name": self.project.get("project_name", "project"),
                    "recent_rank": current_recent[1:] if current_recent.startswith("#") else "",
                    "project_hotkey": current_hotkey,
                }
            if owner is None:
                add_row(
                    f"slot_{digit}",
                    str(digit),
                    _pretty_project_hotkey(_default_project_hotkey(digit)),
                    "",
                    "",
                    "未割当",
                    "",
                    "slot_empty",
                )
            else:
                path_text = str(owner.get("path", ""))
                if current_norm is not None and path_text and str(Path(path_text).resolve()) == current_norm:
                    path_text = current_path_text
                recent_rank = owner.get("recent_rank")
                recent = f"#{recent_rank}" if recent_rank else ""
                add_row(
                    f"slot_{digit}",
                    str(digit),
                    _pretty_project_hotkey(_default_project_hotkey(digit)),
                    str(owner.get("project_name", "")),
                    recent,
                    "割当済み",
                    path_text,
                    "slot_assigned",
                )

        assigned_paths = {str(owner.get("path", "")) for owner in slot_owner.values() if owner.get("path")}
        if self.current_path is not None and current_hotkey and str(self.current_path.resolve()) not in assigned_paths:
            assigned_paths.add(str(self.current_path.resolve()))
        for path in self._sorted_project_files_by_hotkey():
            normalized = str(path.resolve())
            if normalized == current_norm:
                continue
            summary = self._project_summary(path)
            if _hotkey_digit(summary.get("project_hotkey", "")) is not None:
                if normalized in assigned_paths:
                    continue
            recent = f"#{summary['recent_rank']}" if summary["recent_rank"] is not None else ""
            status = "未割当" if not summary.get("project_hotkey") or _hotkey_digit(summary.get("project_hotkey", "")) is None else "重複"
            add_row(
                normalized,
                "",
                summary["project_name"],
                recent,
                status,
                summary["path"],
                "unassigned",
            )

    def _open_shortcut_row(self, event: tk.Event) -> None:
        if self.recording or self.playing:
            return
        row_id = self.shortcut_tree.identify_row(event.y)
        if not row_id:
            return
        if row_id == "current":
            self.start_playback(test_mode=False)
            return
        values = self.shortcut_tree.item(row_id, "values")
        if len(values) < 6:
            return
        path_text = str(values[5])
        if not path_text or path_text == "(未保存)":
            self.start_playback(test_mode=False)
            return
        path = Path(path_text)
        if self._load_project_from_path(path):
            self.start_playback(test_mode=False)

    def _on_shortcut_tree_press(self, event: tk.Event) -> None:
        if self.recording or self.playing:
            return
        row_id = self.shortcut_tree.identify_row(event.y)
        if not row_id:
            self.shortcut_drag_row_id = None
            return
        self.shortcut_drag_row_id = row_id

    def _on_shortcut_tree_drag(self, _event: tk.Event) -> None:
        return

    def _on_shortcut_tree_release(self, event: tk.Event) -> None:
        if self.recording or self.playing:
            self.shortcut_drag_row_id = None
            return
        source_id = self.shortcut_drag_row_id
        self.shortcut_drag_row_id = None
        if not source_id:
            return
        target_id = self.shortcut_tree.identify_row(event.y)
        if not target_id or target_id == source_id:
            return
        source = self.shortcut_row_map.get(source_id)
        target = self.shortcut_row_map.get(target_id)
        if not source or not target:
            return
        source_slot = self._row_slot_number(source_id)
        target_slot = self._row_slot_number(target_id)
        if target_slot is None:
            if source_slot is not None:
                self._clear_shortcut_slot(source_slot)
            return
        if source_slot is None:
            self._move_shortcut_to_slot(source_id, target_slot)
        else:
            self._swap_shortcut_slots(source_slot, target_slot)

    def _row_slot_number(self, row_id: str) -> int | None:
        if not row_id.startswith("slot_"):
            return None
        parts = row_id.split("_", 1)
        if len(parts) != 2 or not parts[1].isdigit():
            return None
        number = int(parts[1])
        if 1 <= number <= 9:
            return number
        return None

    def _load_project_data(self, path: Path) -> dict | None:
        try:
            with path.open("r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as exc:
            messagebox.showerror("読み込み失敗", str(exc))
            return None

    def _save_project_data(self, path: Path, data: dict) -> None:
        with path.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    def _apply_project_hotkey_to_path(self, path: Path, hotkey: str) -> None:
        data = self._load_project_data(path)
        if data is None:
            return
        data["project_hotkey"] = self._normalize_project_hotkey(hotkey)
        data["updated_at"] = _now_iso()
        self._save_project_data(path, data)
        if self.current_path is not None and path.resolve() == self.current_path.resolve():
            self.project["project_hotkey"] = data["project_hotkey"]
            self._sync_project_hotkey_var()

    def _set_current_project_hotkey(self, hotkey: str) -> None:
        self.project["project_hotkey"] = self._normalize_project_hotkey(hotkey)
        self.project["updated_at"] = _now_iso()
        self._sync_project_hotkey_var()

    def _slot_project_path(self, slot_number: int) -> Path | None:
        hotkey = _default_project_hotkey(slot_number)
        if self.current_path is not None and self._normalize_project_hotkey(self.project.get("project_hotkey", "")) == hotkey:
            return self.current_path
        for path in self._available_project_files():
            if self._project_hotkey_from_path(path) == hotkey:
                return path
        return None

    def _clear_shortcut_slot(self, slot_number: int) -> None:
        path = self._slot_project_path(slot_number)
        if path is None:
            return
        if self.current_path is not None and path.resolve() == self.current_path.resolve():
            self._set_current_project_hotkey("")
        else:
            self._apply_project_hotkey_to_path(path, "")
        self._refresh_status()
        self._append_log(f"ショートカットを解除しました: {_pretty_project_hotkey(_default_project_hotkey(slot_number))}")

    def _move_shortcut_to_slot(self, source_row_id: str, slot_number: int) -> None:
        source = self.shortcut_row_map.get(source_row_id)
        if not source:
            return
        source_path_text = str(source.get("path", ""))
        source_is_current = source_row_id == "current"
        if not source_is_current and (not source_path_text or source_path_text == "(未保存)"):
            return
        source_path = self.current_path if source_is_current else Path(source_path_text)
        target_path = self._slot_project_path(slot_number)
        target_hotkey = _default_project_hotkey(slot_number)
        if target_path is not None and (source_path is None or source_path.resolve() != target_path.resolve()):
            self._apply_project_hotkey_to_path(target_path, "")
        if source_is_current:
            self._set_current_project_hotkey(target_hotkey)
        else:
            self._apply_project_hotkey_to_path(source_path, target_hotkey)
        self._refresh_status()
        self._append_log(f"割り当てを変更しました: {_pretty_project_hotkey(target_hotkey)}")

    def _swap_shortcut_slots(self, source_slot: int, target_slot: int) -> None:
        if source_slot == target_slot:
            return
        source_path = self._slot_project_path(source_slot)
        target_path = self._slot_project_path(target_slot)
        source_hotkey = _default_project_hotkey(source_slot)
        target_hotkey = _default_project_hotkey(target_slot)
        if source_path is None and target_path is None:
            return
        if source_path is not None:
            if self.current_path is not None and source_path.resolve() == self.current_path.resolve():
                self._set_current_project_hotkey(target_hotkey)
            else:
                self._apply_project_hotkey_to_path(source_path, target_hotkey)
        if target_path is not None:
            if self.current_path is not None and target_path.resolve() == self.current_path.resolve():
                self._set_current_project_hotkey(source_hotkey)
            else:
                self._apply_project_hotkey_to_path(target_path, source_hotkey)
        self._refresh_status()
        self._append_log(
            f"ショートカットを入れ替えました: {_pretty_project_hotkey(source_hotkey)} <-> {_pretty_project_hotkey(target_hotkey)}"
        )

    def _queue(self, kind: str, payload: object = None) -> None:
        self.ui_queue.put((kind, payload))

    def _poll_ui_queue(self) -> None:
        try:
            while True:
                kind, payload = self.ui_queue.get_nowait()
                if kind == "log":
                    self._append_log(str(payload))
                elif kind == "refresh":
                    self._refresh_tree()
                elif kind == "status":
                    self._refresh_status()
                elif kind == "error":
                    messagebox.showerror("エラー", str(payload))
                elif kind == "info":
                    messagebox.showinfo("情報", str(payload))
                elif kind == "recording_done":
                    self.recording = False
                    self._set_recording_controls(False)
                    self._append_log("記録を終了しました")
                    self._refresh_tree()
                    self._refresh_status()
                elif kind == "playback_done":
                    self.playing = False
                    self._set_playback_controls(False)
                    self._append_log(str(payload))
                    self._refresh_status()
                elif kind == "load_project":
                    self._apply_loaded_project(payload)  # type: ignore[arg-type]
                elif kind == "selection":
                    self._load_selected_step_into_editor()
                elif kind == "focus_step":
                    self._focus_step_by_id(str(payload))
        except queue.Empty:
            pass
        self.root.after(100, self._poll_ui_queue)

    def _append_log(self, text: str) -> None:
        self.log_text.insert("end", f"[{_now_iso()}] {text}\n")
        self.log_text.see("end")

    def _set_recording_controls(self, active: bool) -> None:
        self.recording = active
        self._refresh_status()

    def _set_playback_controls(self, active: bool) -> None:
        self.playing = active
        self._refresh_status()

    def new_project_action(self) -> None:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は新規作成できません。")
            return
        if self.project["steps"] and not messagebox.askyesno("新規作成", "現在の操作ログを破棄して新規作成しますか？"):
            return
        self.project = self._new_project()
        self.project_name_var.set(self.project["project_name"])
        self._sync_project_hotkey_var()
        self.record_mouse_move_var.set(False)
        self.current_path = None
        self._refresh_tree()
        self._refresh_status()
        self._append_log("新規プロジェクトを作成しました")

    def rename_project(self) -> None:
        name = simpledialog.askstring("プロジェクト名", "プロジェクト名を入力してください", initialvalue=self.project_name_var.get())
        if not name:
            return
        self.project_name_var.set(name.strip())
        self.project["project_name"] = name.strip()
        self.project["updated_at"] = _now_iso()
        self._refresh_status()

    def edit_launcher(self) -> None:
        dlg = tk.Toplevel(self.root)
        dlg.title("起動設定")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        launcher = self.project["launcher"]
        type_var = tk.StringVar(value=launcher.get("type", "url"))
        target_var = tk.StringVar(value=launcher.get("target", ""))
        args_var = tk.StringVar(value=launcher.get("args", ""))
        wd_var = tk.StringVar(value=launcher.get("working_dir", ""))
        wait_var = tk.StringVar(value=str(launcher.get("wait_seconds", 0.0)))
        enabled_var = tk.BooleanVar(value=bool(launcher.get("enabled", False)))

        frame = ttk.Frame(dlg, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)
        fields = [
            ("種別", ttk.Combobox(frame, textvariable=type_var, values=["url", "exe", "bat", "cmd", "powershell", "folder"], state="readonly")),
            ("URL/パス", ttk.Entry(frame, textvariable=target_var, width=50)),
            ("引数", ttk.Entry(frame, textvariable=args_var, width=50)),
            ("作業フォルダ", ttk.Entry(frame, textvariable=wd_var, width=50)),
            ("待機秒", ttk.Entry(frame, textvariable=wait_var, width=20)),
        ]
        for idx, (label, widget) in enumerate(fields):
            ttk.Label(frame, text=label).grid(row=idx, column=0, sticky="w", pady=4)
            widget.grid(row=idx, column=1, sticky="ew", pady=4)
        ttk.Checkbutton(frame, text="有効", variable=enabled_var).grid(row=len(fields), column=0, columnspan=2, sticky="w", pady=(4, 8))

        def save_launcher() -> None:
            self.project["launcher"] = {
                "type": type_var.get(),
                "target": target_var.get().strip(),
                "args": args_var.get().strip(),
                "working_dir": wd_var.get().strip(),
                "wait_seconds": _clamp_float(wait_var.get(), 0.0),
                "enabled": bool(enabled_var.get()),
            }
            self.project["updated_at"] = _now_iso()
            dlg.destroy()
            self._append_log("起動設定を更新しました")

        ttk.Button(frame, text="保存", command=save_launcher).grid(row=len(fields) + 1, column=0, sticky="ew", pady=4)
        ttk.Button(frame, text="キャンセル", command=dlg.destroy).grid(row=len(fields) + 1, column=1, sticky="ew", pady=4)

    def edit_project_hotkey(self) -> None:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は設定できません。")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("ショートカット設定")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        current_hotkey = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
        current_digit = _hotkey_digit(current_hotkey)
        if current_digit is None:
            candidates = self._project_hotkey_candidates(ignore_path=self.current_path)
            current_digit = candidates[0] if candidates else 1

        digit_var = tk.StringVar(value=str(current_digit))
        preview_var = tk.StringVar(value="")
        note_var = tk.StringVar(value="")

        frame = ttk.Frame(dlg, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)

        ttk.Label(frame, text="割り当て").grid(row=0, column=0, sticky="w", pady=4)
        digit_box = ttk.Combobox(frame, textvariable=digit_var, values=[str(i) for i in range(1, 10)], state="readonly", width=8)
        digit_box.grid(row=0, column=1, sticky="w", pady=4)
        ttk.Label(frame, textvariable=preview_var).grid(row=1, column=0, columnspan=2, sticky="w", pady=4)
        ttk.Label(frame, textvariable=note_var, foreground="#aa0000").grid(row=2, column=0, columnspan=2, sticky="w", pady=(2, 8))

        def update_preview(_event: tk.Event | None = None) -> None:
            digit = _clamp_int(digit_var.get(), 1)
            digit = max(1, min(9, digit))
            hotkey = _default_project_hotkey(digit)
            conflict, conflict_path = self._project_hotkey_used_by_other(hotkey, ignore_path=self.current_path)
            preview_var.set(f"設定されるショートカット: {_pretty_project_hotkey(hotkey)}")
            if conflict and conflict_path is not None:
                note_var.set(f"使用中: {conflict_path}")
            else:
                note_var.set("空きです")

        def save_hotkey() -> None:
            digit = _clamp_int(digit_var.get(), 1)
            if not 1 <= digit <= 9:
                messagebox.showwarning("入力エラー", "1〜9 の数字を選んでください。")
                return
            hotkey = _default_project_hotkey(digit)
            conflict, conflict_path = self._project_hotkey_used_by_other(hotkey, ignore_path=self.current_path)
            if conflict and conflict_path is not None:
                messagebox.showerror("競合", f"そのショートカットは既に使用されています。\n{conflict_path}")
                return
            self.project["project_hotkey"] = hotkey
            self.project["updated_at"] = _now_iso()
            self._sync_project_hotkey_var()
            self._refresh_status()
            dlg.destroy()
            self._append_log(f"ショートカットを設定しました: {_pretty_project_hotkey(hotkey)}")

        digit_box.bind("<<ComboboxSelected>>", update_preview)
        ttk.Button(frame, text="保存", command=save_hotkey).grid(row=3, column=0, sticky="ew", pady=4)
        ttk.Button(frame, text="キャンセル", command=dlg.destroy).grid(row=3, column=1, sticky="ew", pady=4)
        update_preview()

    def edit_workflow(self) -> None:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は編集できません。")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("実行フロー")
        dlg.geometry("1180x720")
        dlg.transient(self.root)
        dlg.grab_set()

        frame = ttk.Frame(dlg, padding=10)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(0, weight=2)
        frame.columnconfigure(1, weight=1)
        frame.rowconfigure(1, weight=1)

        enabled_var = tk.BooleanVar(value=bool(self.project.get("workflow_enabled", False)))
        ttk.Checkbutton(frame, text="実行フローを使う", variable=enabled_var).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8))

        columns = ("no", "type", "summary")
        tree = ttk.Treeview(frame, columns=columns, show="headings", selectmode="browse")
        tree.heading("no", text="No")
        tree.heading("type", text="種別")
        tree.heading("summary", text="内容")
        tree.column("no", width=60, anchor="w", stretch=False)
        tree.column("type", width=150, anchor="w", stretch=False)
        tree.column("summary", width=700, anchor="w", stretch=True)
        tree.grid(row=1, column=0, sticky="nsew")
        scroll = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        scroll.grid(row=1, column=1, sticky="ns")
        tree.configure(yscrollcommand=scroll.set)
        tree.tag_configure("drop_target", background="#dff0ff")

        editor = ttk.LabelFrame(frame, text="選択中のノード", padding=10)
        editor.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        editor.columnconfigure(1, weight=1)

        node_type_var = tk.StringVar(value="-")
        node_summary_var = tk.StringVar(value="-")
        node_scope_var = tk.StringVar(value="-")
        node_enabled_var = tk.BooleanVar(value=True)
        drag_hint_var = tk.StringVar(value="ドラッグでノードを並べ替えできます。")
        ttk.Label(editor, text="種別").grid(row=0, column=0, sticky="w", pady=2)
        ttk.Label(editor, textvariable=node_type_var).grid(row=0, column=1, sticky="w", pady=2)
        ttk.Label(editor, text="内容").grid(row=1, column=0, sticky="w", pady=2)
        ttk.Label(editor, textvariable=node_summary_var, wraplength=920, justify="left").grid(row=1, column=1, sticky="w", pady=2)
        ttk.Label(editor, text="位置").grid(row=2, column=0, sticky="w", pady=2)
        ttk.Label(editor, textvariable=node_scope_var).grid(row=2, column=1, sticky="w", pady=2)
        ttk.Label(editor, text="有効").grid(row=3, column=0, sticky="w", pady=2)
        node_enabled_widget = ttk.Checkbutton(editor, text="有効", variable=node_enabled_var)
        node_enabled_widget.grid(row=3, column=1, sticky="w", pady=2)
        ttk.Label(frame, textvariable=drag_hint_var, foreground="#356").grid(row=4, column=0, columnspan=2, sticky="w", pady=(6, 0))

        nodes: list[dict] = copy.deepcopy(self.project.get("workflow", []))
        item_map: dict[str, dict] = {}
        node_to_iid: dict[int, str] = {}
        drag_state: dict[str, object | None] = {"iid": None, "node": None, "start_y": None, "target": None}

        def node_type_label(node: dict) -> str:
            kind = node.get("type", "")
            return {
                "project": "プロジェクト",
                "condition": "条件",
                "elif": "Elif",
                "loop": "ループ",
            }.get(kind, str(kind))

        def node_summary(node: dict) -> str:
            kind = node.get("type", "")
            prefix = "" if node.get("enabled", True) else "[無効] "
            if kind == "project":
                path = str(node.get("project_path", ""))
                name = str(node.get("name", "")) or (Path(path).stem if path else "(未指定)")
                return f"{prefix}{name} -> {path or '(未指定)'}"
            if kind == "condition":
                source = str(node.get("source", "clipboard"))
                op = str(node.get("operator", "contains"))
                subject = "clipboard" if source == "clipboard" else (
                    str(node.get("file_path", "")) if source == "file" else str(node.get("text", ""))
                )
                value = str(node.get("value", ""))
                return f"{prefix}{source}:{subject} {op} '{value}'"
            if kind == "elif":
                source = str(node.get("source", "clipboard"))
                op = str(node.get("operator", "contains"))
                subject = "clipboard" if source == "clipboard" else (
                    str(node.get("file_path", "")) if source == "file" else str(node.get("text", ""))
                )
                value = str(node.get("value", ""))
                return f"{prefix}{source}:{subject} {op} '{value}'"
            if kind == "loop":
                mode = str(node.get("mode", "count"))
                if mode == "while":
                    source = str(node.get("source", "clipboard"))
                    subject = "clipboard" if source == "clipboard" else (
                        str(node.get("file_path", "")) if source == "file" else str(node.get("text", ""))
                    )
                    op = str(node.get("operator", "contains"))
                    value = str(node.get("value", ""))
                    return f"{prefix}while {source}:{subject} {op} '{value}'"
                return f"{prefix}{int(node.get('repeat_count', 1))}回繰り返し"
            return ""

        def branch_list(node: dict, branch: str, create: bool = False) -> list[dict]:
            if branch not in {"then", "elif", "else", "body"}:
                return []
            if branch not in node and create:
                node[branch] = []
            value = node.get(branch, [])
            if not isinstance(value, list):
                value = []
                if create:
                    node[branch] = value
            return value

        def tree_label_for_branch(branch: str) -> str:
            return {"then": "Then", "elif": "Elif", "else": "Else", "body": "Body"}.get(branch, branch)

        def render_nodes(current_nodes: list[dict], parent_iid: str = "", path_prefix: str = "r") -> None:
            for idx, node in enumerate(current_nodes):
                node_iid = f"{path_prefix}{idx}"
                item_map[node_iid] = {"kind": "node", "node": node, "container": current_nodes, "index": idx, "path": node_iid}
                node_to_iid[id(node)] = node_iid
                tree.insert(parent_iid, "end", iid=node_iid, values=(len(item_map), node_type_label(node), node_summary(node)))
                kind = node.get("type", "")
                if kind == "condition":
                    then_iid = f"{node_iid}.then"
                    elif_iid = f"{node_iid}.elif"
                    else_iid = f"{node_iid}.else"
                    tree.insert(node_iid, "end", iid=then_iid, values=("", "Then", f"{len(branch_list(node, 'then'))}件"))
                    tree.insert(node_iid, "end", iid=elif_iid, values=("", "Elif", f"{len(branch_list(node, 'elif'))}件"))
                    tree.insert(node_iid, "end", iid=else_iid, values=("", "Else", f"{len(branch_list(node, 'else'))}件"))
                    item_map[then_iid] = {"kind": "branch", "node": node, "branch": "then", "container": branch_list(node, "then", True), "path": then_iid}
                    item_map[elif_iid] = {"kind": "branch", "node": node, "branch": "elif", "container": branch_list(node, "elif", True), "path": elif_iid}
                    item_map[else_iid] = {"kind": "branch", "node": node, "branch": "else", "container": branch_list(node, "else", True), "path": else_iid}
                    render_nodes(branch_list(node, "then", True), then_iid, f"{node_iid}.t")
                    render_nodes(branch_list(node, "elif", True), elif_iid, f"{node_iid}.l")
                    render_nodes(branch_list(node, "else", True), else_iid, f"{node_iid}.e")
                elif kind == "loop":
                    body_iid = f"{node_iid}.body"
                    tree.insert(node_iid, "end", iid=body_iid, values=("", "Body", f"{len(branch_list(node, 'body'))}件"))
                    item_map[body_iid] = {"kind": "branch", "node": node, "branch": "body", "container": branch_list(node, "body", True), "path": body_iid}
                    render_nodes(branch_list(node, "body", True), body_iid, f"{node_iid}.b")
                elif kind == "elif":
                    then_iid = f"{node_iid}.then"
                    tree.insert(node_iid, "end", iid=then_iid, values=("", "Then", f"{len(branch_list(node, 'then'))}件"))
                    item_map[then_iid] = {"kind": "branch", "node": node, "branch": "then", "container": branch_list(node, "then", True), "path": then_iid}
                    render_nodes(branch_list(node, "then", True), then_iid, f"{node_iid}.t")

        def rebuild_tree() -> None:
            tree.delete(*tree.get_children())
            item_map.clear()
            render_nodes(nodes)

        def selection_ref() -> dict | None:
            sel = tree.selection()
            if not sel:
                return None
            return item_map.get(sel[0])

        def update_editor() -> None:
            ref = selection_ref()
            if ref is None:
                node_type_var.set("-")
                node_summary_var.set("-")
                node_scope_var.set("-")
                node_enabled_var.set(True)
                node_enabled_widget.state(["disabled"])
                return
            if ref["kind"] == "node":
                node = ref["node"]
                node_type_var.set(node_type_label(node))
                node_summary_var.set(node_summary(node))
                node_scope_var.set(f"root / index {ref['index'] + 1}")
                node_enabled_var.set(bool(node.get("enabled", True)))
                node_enabled_widget.state(["!disabled"])
            else:
                node = ref["node"]
                branch = ref["branch"]
                node_type_var.set(f"{node_type_label(node)}:{tree_label_for_branch(branch)}")
                node_summary_var.set(f"{tree_label_for_branch(branch)} ブランチ")
                node_scope_var.set(f"{node_type_label(node)} の {tree_label_for_branch(branch)}")
                node_enabled_var.set(True)
                node_enabled_widget.state(["disabled"])

        def select_item(iid: str) -> None:
            if iid in item_map:
                tree.selection_set(iid)
                tree.see(iid)
                update_editor()

        def select_node_object(node: dict) -> None:
            iid = node_to_iid.get(id(node))
            if iid:
                select_item(iid)

        def clear_drag_target() -> None:
            target_iid = drag_state.get("target")
            if target_iid and target_iid in item_map:
                try:
                    tree.item(str(target_iid), tags=())
                except Exception:
                    pass
            drag_state["target"] = None
            drag_hint_var.set("ドラッグでノードを並べ替えできます。")

        def set_drag_target(iid: str | None) -> None:
            if drag_state.get("target") == iid:
                return
            clear_drag_target()
            if not iid or iid not in item_map:
                return
            try:
                tree.item(iid, tags=("drop_target",))
            except Exception:
                return
            drag_state["target"] = iid
            ref = item_map.get(iid)
            if ref is None:
                drag_hint_var.set("ドロップ先を選択中")
            elif ref["kind"] == "branch":
                drag_hint_var.set(f"ドロップ先: {tree_label_for_branch(ref['branch'])}")
            else:
                drag_hint_var.set(f"ドロップ先: {node_type_label(ref['node'])} {ref['index'] + 1}")

        def target_container(default_branch: str | None = None) -> tuple[list[dict], dict | None]:
            ref = selection_ref()
            if ref is None:
                return nodes, None
            if ref["kind"] == "branch":
                return ref["container"], ref["node"]
            node = ref["node"]
            kind = node.get("type", "")
            if default_branch is not None:
                if kind == "condition" and default_branch in {"then", "elif", "else"}:
                    return branch_list(node, default_branch, True), node
                if kind == "loop" and default_branch == "body":
                    return branch_list(node, default_branch, True), node
            if kind == "condition":
                return branch_list(node, "then", True), node
            if kind == "loop":
                return branch_list(node, "body", True), node
            return ref["container"], None

        def add_project_node() -> None:
            container, _ = target_container()
            path = filedialog.askopenfilename(title="呼び出すプロジェクトを選択", initialdir=str(self.app_dir), filetypes=[("JSON", "*.json")])
            if not path:
                return
            p = Path(path)
            name = p.stem
            try:
                with p.open("r", encoding="utf-8") as f:
                    data = json.load(f)
                name = str(data.get("project_name", name))
            except Exception:
                pass
            container.append({
                "type": "project",
                "name": name,
                "project_path": str(p),
                "enabled": True,
            })
            rebuild_tree()

        def add_condition_node() -> None:
            container, _ = target_container()
            container.append({
                "type": "condition",
                "name": "条件",
                "source": "clipboard",
                "operator": "contains",
                "text": "",
                "file_path": "",
                "file_encoding": "utf-8",
                "value": "",
                "then": [],
                "elif": [],
                "else": [],
                "enabled": True,
            })
            rebuild_tree()

        def add_loop_node() -> None:
            container, _ = target_container()
            container.append({
                "type": "loop",
                "name": "ループ",
                "mode": "count",
                "repeat_count": 2,
                "body": [],
                "source": "clipboard",
                "operator": "contains",
                "text": "",
                "file_path": "",
                "file_encoding": "utf-8",
                "value": "",
                "enabled": True,
            })
            rebuild_tree()

        def add_to_branch(branch: str) -> None:
            container, node = target_container(default_branch=branch)
            if node is None and branch not in {"then", "elif", "else", "body"}:
                return
            if node is None:
                container = nodes
            if branch == "body" and node is not None and node.get("type") != "loop":
                return
            if branch == "elif" and node is not None and node.get("type") != "condition":
                return
            if branch == "then" and node is not None and node.get("type") not in {"condition", "elif"}:
                return
            if branch == "else" and node is not None and node.get("type") != "condition":
                return
            new_node = {"type": "project", "name": "新しいプロジェクト", "project_path": "", "enabled": True}
            container.append(new_node)
            rebuild_tree()

        def edit_selected_node() -> None:
            ref = selection_ref()
            if ref is None or ref["kind"] != "node":
                return
            node = ref["node"]
            kind = node.get("type", "")
            if kind == "project":
                self._edit_workflow_project_node(node)
            elif kind == "condition":
                self._edit_workflow_condition_node(node)
            elif kind == "elif":
                self._edit_workflow_condition_node(node)
            elif kind == "loop":
                self._edit_workflow_loop_node(node)
            rebuild_tree()
            select_item(ref["path"])

        def delete_selected_node() -> None:
            ref = selection_ref()
            if ref is None or ref["kind"] != "node":
                return
            container = ref["container"]
            index = ref["index"]
            del container[index]
            rebuild_tree()
            if container:
                next_index = min(index, len(container) - 1)
                select_node_object(container[next_index])

        def move_selected(delta: int) -> None:
            ref = selection_ref()
            if ref is None or ref["kind"] != "node":
                return
            container = ref["container"]
            index = ref["index"]
            new_index = index + delta
            if not (0 <= new_index < len(container)):
                return
            container[index], container[new_index] = container[new_index], container[index]
            rebuild_tree()
            select_node_object(container[new_index])

        def toggle_selected_enabled() -> None:
            ref = selection_ref()
            if ref is None or ref["kind"] != "node":
                return
            ref["node"]["enabled"] = bool(node_enabled_var.get())
            rebuild_tree()
            select_node_object(ref["node"])

        def load_template() -> None:
            if nodes and not messagebox.askyesno("テンプレート", "現在のフローをテンプレートで置き換えますか？"):
                return
            nodes[:] = self._default_workflow_template()
            rebuild_tree()

        def _drop_target_container(target_ref: dict | None) -> tuple[list[dict], int]:
            if target_ref is None:
                return nodes, len(nodes)
            if target_ref["kind"] == "branch":
                return target_ref["container"], len(target_ref["container"])
            return target_ref["container"], target_ref["index"]

        def _move_node(node: dict, source_container: list[dict], source_index: int, target_container: list[dict], target_index: int) -> None:
            if source_container is target_container and source_index < target_index:
                target_index -= 1
            item = source_container.pop(source_index)
            target_container.insert(target_index, item)

        def on_tree_press(event: tk.Event) -> None:
            if self.recording or self.playing:
                return
            iid = tree.identify_row(event.y)
            ref = item_map.get(iid)
            if not ref or ref["kind"] != "node":
                drag_state["iid"] = None
                drag_state["node"] = None
                drag_state["start_y"] = None
                clear_drag_target()
                return
            drag_state["iid"] = iid
            drag_state["node"] = ref["node"]
            drag_state["start_y"] = event.y
            set_drag_target(iid)

        def on_tree_motion(event: tk.Event) -> None:
            if self.recording or self.playing or not drag_state.get("iid"):
                return
            iid = tree.identify_row(event.y)
            ref = item_map.get(iid)
            if ref is None:
                clear_drag_target()
                return
            set_drag_target(iid)

        def on_tree_release(event: tk.Event) -> None:
            if self.recording or self.playing:
                return
            drag_iid = drag_state.get("iid")
            drag_node = drag_state.get("node")
            if not drag_iid or drag_node is None:
                clear_drag_target()
                return
            source_ref = item_map.get(str(drag_iid))
            if not source_ref or source_ref["kind"] != "node":
                drag_state["iid"] = None
                drag_state["node"] = None
                drag_state["start_y"] = None
                clear_drag_target()
                return
            target_ref = item_map.get(tree.identify_row(event.y))
            target_container, target_index = _drop_target_container(target_ref)
            source_container = source_ref["container"]
            source_index = source_ref["index"]
            if source_container is target_container and source_index == target_index:
                drag_state["iid"] = None
                drag_state["node"] = None
                drag_state["start_y"] = None
                clear_drag_target()
                return
            _move_node(drag_node, source_container, source_index, target_container, target_index)
            rebuild_tree()
            select_node_object(drag_node)
            drag_state["iid"] = None
            drag_state["node"] = None
            drag_state["start_y"] = None
            clear_drag_target()

        def save_workflow() -> None:
            self.project["workflow_enabled"] = bool(enabled_var.get())
            self.project["workflow"] = copy.deepcopy(nodes)
            self.project["updated_at"] = _now_iso()
            self._refresh_status()
            dlg.destroy()
            self._append_log("実行フローを保存しました")

        tree.bind("<<TreeviewSelect>>", lambda _event: update_editor())
        tree.bind("<Double-1>", lambda _event: edit_selected_node())
        tree.bind("<ButtonPress-1>", on_tree_press, add="+")
        tree.bind("<B1-Motion>", on_tree_motion, add="+")
        tree.bind("<ButtonRelease-1>", on_tree_release, add="+")
        node_enabled_widget.configure(command=toggle_selected_enabled)

        button_row = ttk.Frame(frame)
        button_row.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        ttk.Button(button_row, text="追加: プロジェクト", command=add_project_node).pack(side="left", padx=3)
        ttk.Button(button_row, text="追加: 条件", command=add_condition_node).pack(side="left", padx=3)
        ttk.Button(button_row, text="追加: ループ", command=add_loop_node).pack(side="left", padx=3)
        ttk.Button(button_row, text="Thenへ追加", command=lambda: add_to_branch("then")).pack(side="left", padx=3)
        ttk.Button(button_row, text="Elseへ追加", command=lambda: add_to_branch("else")).pack(side="left", padx=3)
        ttk.Button(button_row, text="本体へ追加", command=lambda: add_to_branch("body")).pack(side="left", padx=3)
        ttk.Button(button_row, text="編集", command=edit_selected_node).pack(side="left", padx=3)
        ttk.Button(button_row, text="削除", command=delete_selected_node).pack(side="left", padx=3)
        ttk.Button(button_row, text="上へ", command=lambda: move_selected(-1)).pack(side="left", padx=3)
        ttk.Button(button_row, text="下へ", command=lambda: move_selected(1)).pack(side="left", padx=3)
        ttk.Button(button_row, text="テンプレート", command=load_template).pack(side="left", padx=3)
        ttk.Button(button_row, text="保存", command=save_workflow).pack(side="right", padx=3)
        ttk.Button(button_row, text="閉じる", command=dlg.destroy).pack(side="right", padx=3)

        rebuild_tree()
        if item_map:
            select_item(next(iter(item_map.keys())))

    def _edit_workflow_project_node(self, node: dict) -> None:
        dlg = tk.Toplevel(self.root)
        dlg.title("プロジェクト呼び出し")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        name_var = tk.StringVar(value=str(node.get("name", "")))
        path_var = tk.StringVar(value=str(node.get("project_path", "")))

        frame = ttk.Frame(dlg, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)

        ttk.Label(frame, text="表示名").grid(row=0, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=name_var, width=40).grid(row=0, column=1, sticky="ew", pady=4)
        ttk.Label(frame, text="JSONパス").grid(row=1, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=path_var, width=50).grid(row=1, column=1, sticky="ew", pady=4)

        def browse() -> None:
            path = filedialog.askopenfilename(title="呼び出すプロジェクトを選択", initialdir=str(self.app_dir), filetypes=[("JSON", "*.json")])
            if path:
                path_var.set(path)
                try:
                    with Path(path).open("r", encoding="utf-8") as f:
                        data = json.load(f)
                    if not name_var.get().strip():
                        name_var.set(str(data.get("project_name", Path(path).stem)))
                except Exception:
                    if not name_var.get().strip():
                        name_var.set(Path(path).stem)

        def save() -> None:
            path_text = path_var.get().strip()
            if not path_text:
                messagebox.showwarning("入力エラー", "JSONパスを指定してください。")
                return
            node["type"] = "project"
            node["name"] = name_var.get().strip() or Path(path_text).stem
            node["project_path"] = path_text
            dlg.destroy()

        ttk.Button(frame, text="参照", command=browse).grid(row=1, column=2, sticky="w", padx=(8, 0))
        ttk.Button(frame, text="保存", command=save).grid(row=2, column=0, sticky="ew", pady=(8, 4))
        ttk.Button(frame, text="キャンセル", command=dlg.destroy).grid(row=2, column=1, sticky="ew", pady=(8, 4))

    def _edit_workflow_condition_node(self, node: dict) -> None:
        dlg = tk.Toplevel(self.root)
        dlg.title("条件分岐" if node.get("type", "condition") == "condition" else "Elif条件")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        source_var = tk.StringVar(value=str(node.get("source", "clipboard")))
        operator_var = tk.StringVar(value=str(node.get("operator", "contains")))
        text_var = tk.StringVar(value=str(node.get("text", "")))
        file_path_var = tk.StringVar(value=str(node.get("file_path", "")))
        file_encoding_var = tk.StringVar(value=str(node.get("file_encoding", "utf-8")))
        value_var = tk.StringVar(value=str(node.get("value", "")))
        jump_true_var = tk.StringVar(value=str(node.get("jump_true", 1)))
        jump_false_var = tk.StringVar(value=str(node.get("jump_false", 1)))
        name_var = tk.StringVar(value=str(node.get("name", "条件")))
        as_elif_var = tk.BooleanVar(value=str(node.get("type", "condition")) == "elif")

        frame = ttk.Frame(dlg, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)

        fields = [
            ("表示名", ttk.Entry(frame, textvariable=name_var, width=40)),
            ("対象", ttk.Combobox(frame, textvariable=source_var, values=["clipboard", "text", "file"], state="readonly")),
            ("判定", ttk.Combobox(frame, textvariable=operator_var, values=["contains", "not_contains", "equals", "not_equals", "startswith", "endswith", "regex", "is_empty", "not_empty"], state="readonly")),
            ("文字列", ttk.Entry(frame, textvariable=text_var, width=50)),
            ("ファイルパス", ttk.Entry(frame, textvariable=file_path_var, width=50)),
            ("文字コード", ttk.Entry(frame, textvariable=file_encoding_var, width=20)),
            ("比較値", ttk.Entry(frame, textvariable=value_var, width=50)),
            ("真なら進む数", ttk.Entry(frame, textvariable=jump_true_var, width=10)),
            ("偽なら進む数", ttk.Entry(frame, textvariable=jump_false_var, width=10)),
        ]
        for idx, (label, widget) in enumerate(fields):
            ttk.Label(frame, text=label).grid(row=idx, column=0, sticky="w", pady=4)
            widget.grid(row=idx, column=1, sticky="ew", pady=4)

        ttk.Checkbutton(frame, text="Elifとして使う", variable=as_elif_var).grid(row=len(fields), column=0, columnspan=2, sticky="w", pady=(4, 0))
        ttk.Label(frame, text="clipboard は現在のクリップボード文字列、text はここで入力した文字列、file はファイル内容を使います。regex は正規表現です。").grid(row=len(fields) + 1, column=0, columnspan=2, sticky="w", pady=(4, 8))

        def save() -> None:
            node["type"] = "elif" if as_elif_var.get() else "condition"
            node["name"] = name_var.get().strip() or ("Elif" if as_elif_var.get() else "条件")
            node["source"] = source_var.get()
            node["operator"] = operator_var.get()
            node["text"] = text_var.get()
            node["file_path"] = file_path_var.get().strip()
            node["file_encoding"] = file_encoding_var.get().strip() or "utf-8"
            node["value"] = value_var.get()
            if not as_elif_var.get():
                node["jump_true"] = _clamp_int(jump_true_var.get(), 1)
                node["jump_false"] = _clamp_int(jump_false_var.get(), 1)
            dlg.destroy()

        ttk.Button(frame, text="保存", command=save).grid(row=len(fields) + 2, column=0, sticky="ew", pady=4)
        ttk.Button(frame, text="キャンセル", command=dlg.destroy).grid(row=len(fields) + 2, column=1, sticky="ew", pady=4)

    def _edit_workflow_loop_node(self, node: dict) -> None:
        dlg = tk.Toplevel(self.root)
        dlg.title("ループ")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        mode_var = tk.StringVar(value=str(node.get("mode", "count")))
        repeat_var = tk.StringVar(value=str(node.get("repeat_count", 2)))
        source_var = tk.StringVar(value=str(node.get("source", "clipboard")))
        operator_var = tk.StringVar(value=str(node.get("operator", "contains")))
        text_var = tk.StringVar(value=str(node.get("text", "")))
        file_path_var = tk.StringVar(value=str(node.get("file_path", "")))
        file_encoding_var = tk.StringVar(value=str(node.get("file_encoding", "utf-8")))
        value_var = tk.StringVar(value=str(node.get("value", "")))
        name_var = tk.StringVar(value=str(node.get("name", "ループ")))

        frame = ttk.Frame(dlg, padding=12)
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)

        fields = [
            ("表示名", ttk.Entry(frame, textvariable=name_var, width=40)),
            ("モード", ttk.Combobox(frame, textvariable=mode_var, values=["count", "while"], state="readonly")),
            ("繰り返し回数", ttk.Entry(frame, textvariable=repeat_var, width=10)),
            ("対象", ttk.Combobox(frame, textvariable=source_var, values=["clipboard", "text", "file"], state="readonly")),
            ("判定", ttk.Combobox(frame, textvariable=operator_var, values=["contains", "not_contains", "equals", "not_equals", "startswith", "endswith", "regex", "is_empty", "not_empty"], state="readonly")),
            ("文字列", ttk.Entry(frame, textvariable=text_var, width=50)),
            ("ファイルパス", ttk.Entry(frame, textvariable=file_path_var, width=50)),
            ("文字コード", ttk.Entry(frame, textvariable=file_encoding_var, width=20)),
            ("比較値", ttk.Entry(frame, textvariable=value_var, width=50)),
        ]
        for idx, (label, widget) in enumerate(fields):
            ttk.Label(frame, text=label).grid(row=idx, column=0, sticky="w", pady=4)
            widget.grid(row=idx, column=1, sticky="ew", pady=4)

        ttk.Label(frame, text="count は回数ループ、while は条件が真の間だけ繰り返します。file はファイル内容を使います。regex は正規表現です。").grid(row=len(fields), column=0, columnspan=2, sticky="w", pady=(4, 8))

        def save() -> None:
            node["type"] = "loop"
            node["name"] = name_var.get().strip() or "ループ"
            node["mode"] = mode_var.get()
            node["repeat_count"] = max(1, _clamp_int(repeat_var.get(), 2))
            node["source"] = source_var.get()
            node["operator"] = operator_var.get()
            node["text"] = text_var.get()
            node["file_path"] = file_path_var.get().strip()
            node["file_encoding"] = file_encoding_var.get().strip() or "utf-8"
            node["value"] = value_var.get()
            node.setdefault("body", [])
            dlg.destroy()

        ttk.Button(frame, text="保存", command=save).grid(row=len(fields) + 1, column=0, sticky="ew", pady=4)
        ttk.Button(frame, text="キャンセル", command=dlg.destroy).grid(row=len(fields) + 1, column=1, sticky="ew", pady=4)

    def _default_workflow_template(self) -> list[dict]:
        return [
            {
                "type": "condition",
                "name": "クリップボード判定",
                "source": "clipboard",
                "operator": "contains",
                "text": "",
                "file_path": "",
                "file_encoding": "utf-8",
                "value": "OK",
                "enabled": True,
                "then": [
                    {
                        "type": "loop",
                        "name": "2回繰り返し",
                        "mode": "count",
                        "repeat_count": 2,
                        "source": "clipboard",
                        "operator": "contains",
                        "text": "",
                        "file_path": "",
                        "file_encoding": "utf-8",
                        "value": "",
                        "enabled": True,
                        "body": [
                            {
                                "type": "project",
                                "name": "ここにプロジェクトを指定",
                                "project_path": "",
                                "enabled": True,
                            }
                        ],
                    }
                ],
                "elif": [
                    {
                        "type": "elif",
                        "name": "代替条件",
                        "source": "file",
                        "operator": "contains",
                        "text": "",
                        "file_path": "",
                        "value": "READY",
                        "then": [
                            {
                                "type": "project",
                                "name": "Elif 用プロジェクト",
                                "project_path": "",
                                "enabled": True,
                            }
                        ],
                        "enabled": True,
                    }
                ],
                "else": [
                    {
                        "type": "project",
                        "name": "代替プロジェクト",
                        "project_path": "",
                        "enabled": True,
                    }
                ],
            }
        ]

    def _refresh_tree(self) -> None:
        self.tree.delete(*self.tree.get_children())
        for idx, step in enumerate(self.project["steps"], start=1):
            content = self._step_content(step)
            coords = self._step_coords(step)
            self.tree.insert(
                "",
                "end",
                iid=step["id"],
                values=(
                    idx,
                    step.get("auto_label", ""),
                    step.get("display_name", ""),
                    self._display_action_name(step),
                    content,
                    coords,
                    f"{float(step.get('wait_before', 0.0)):.3f}",
                    "○" if step.get("enabled", True) else "×",
                ),
            )
        self._refresh_status()

    def _display_action_name(self, step: dict) -> str:
        action = step.get("action", "")
        if action == "click":
            button = step.get("button", "left")
            count = int(step.get("click_count", 1))
            if count >= 2:
                return "ダブルクリック"
            if button == "right":
                return "右クリック"
            if button == "middle":
                return "中クリック"
            return "左クリック"
        if action == "wheel":
            return "ホイール"
        if action == "key":
            if step.get("modifiers"):
                return "ショートカット"
            return "キー"
        if action == "text_input":
            return "文字入力"
        if action == "move":
            return "マウス移動"
        return action

    def _step_content(self, step: dict) -> str:
        action = step.get("action", "")
        if action == "text_input":
            text = str(step.get("text", ""))
            mode = str(step.get("input_mode", ""))
            if mode and mode != "ascii":
                return f"{text} [{mode}]"
            return text
        if action == "click":
            return f"{step.get('button', 'left')} x{int(step.get('click_count', 1))}"
        if action == "wheel":
            direction = step.get("direction", "down")
            delta = step.get("delta", 0)
            axis = step.get("axis", "vertical")
            return f"{axis} {direction} {delta}"
        if action == "key":
            modifiers = [ _pretty_modifier(m) for m in step.get("modifiers", []) ]
            key_name = _pretty_key_name(str(step.get("key_name", "")))
            if modifiers:
                return " + ".join(modifiers + [key_name])
            return key_name
        if action == "move":
            return ""
        return ""

    def _step_coords(self, step: dict) -> str:
        x = step.get("x")
        y = step.get("y")
        if x is None or y is None:
            return ""
        return f"{x}, {y}"

    def _on_step_select(self, _event: tk.Event) -> None:
        selection = self.tree.selection()
        if not selection:
            return
        self.selected_step_id = selection[0]
        for idx, step in enumerate(self.project["steps"]):
            if step["id"] == self.selected_step_id:
                self.selected_step_index = idx
                self._load_step_into_editor(step)
                break

    def _on_tree_click(self, event: tk.Event) -> None:
        if self.recording or self.playing:
            return
        row_id = self.tree.identify_row(event.y)
        column = self.tree.identify_column(event.x)
        if not row_id or column == "#0":
            return
        self.tree.selection_set(row_id)
        self.selected_step_id = row_id
        self.selected_step_index = next((idx for idx, step in enumerate(self.project["steps"]) if step["id"] == row_id), None)
        if self.selected_step_index is None:
            return
        step = self.project["steps"][self.selected_step_index]
        self._load_step_into_editor(step)
        self.root.after_idle(lambda: self._edit_tree_cell(row_id, column))

    def _edit_tree_cell(self, row_id: str, column: str) -> None:
        self._close_inline_editor()
        step = next((s for s in self.project["steps"] if s["id"] == row_id), None)
        if step is None:
            return

        editable_map = {
            "#3": "display_name",
            "#5": "content",
            "#6": "coords",
            "#7": "wait",
            "#8": "enabled",
        }
        field = editable_map.get(column)
        if field is None:
            return

        if field == "enabled":
            step["enabled"] = not bool(step.get("enabled", True))
            self.project["updated_at"] = _now_iso()
            self._refresh_tree()
            self._load_step_into_editor(step)
            return

        bbox = self.tree.bbox(row_id, column)
        if not bbox:
            return
        x, y, width, height = bbox
        value = ""
        if field == "display_name":
            value = str(step.get("display_name", ""))
        elif field == "content":
            value = self._step_content(step)
        elif field == "coords":
            value = self._coords_input_value(step)
        elif field == "wait":
            value = str(step.get("wait_before", 0.0))

        popup = tk.Toplevel(self.root)
        popup.overrideredirect(True)
        popup.attributes("-topmost", True)
        popup.geometry(f"{max(width, 120)}x{height + 8}+{self.tree.winfo_rootx() + x}+{self.tree.winfo_rooty() + y}")
        frame = ttk.Frame(popup, padding=2)
        frame.pack(fill="both", expand=True)
        helper = ttk.Label(frame, text=self._inline_edit_helper(step, field), justify="left")
        helper.pack(fill="x", padx=2, pady=(0, 2))
        entry = ttk.Entry(frame)
        entry.insert(0, value)
        entry.pack(fill="both", expand=True)
        entry.focus_set()
        entry.selection_range(0, "end")

        self.inline_editor = popup
        self.inline_editor_entry = entry
        self.inline_editor_item = row_id
        self.inline_editor_column = field
        self.inline_editor_step_id = row_id

        def commit() -> None:
            self._commit_inline_edit()

        def cancel(_event: tk.Event | None = None) -> None:
            self._close_inline_editor()

        entry.bind("<Return>", lambda _event: commit())
        entry.bind("<Escape>", cancel)
        entry.bind("<FocusOut>", cancel)

    def _close_inline_editor(self) -> None:
        if self.inline_editor is not None:
            try:
                self.inline_editor.destroy()
            except Exception:
                pass
        self.inline_editor = None
        self.inline_editor_entry = None
        self.inline_editor_item = None
        self.inline_editor_column = None
        self.inline_editor_step_id = None

    def _commit_inline_edit(self) -> None:
        if self.inline_editor_entry is None or self.inline_editor_step_id is None or self.inline_editor_column is None:
            self._close_inline_editor()
            return
        step = next((s for s in self.project["steps"] if s["id"] == self.inline_editor_step_id), None)
        if step is None:
            self._close_inline_editor()
            return
        value = self.inline_editor_entry.get().strip()
        field = self.inline_editor_column
        try:
            if field == "display_name":
                step["display_name"] = value
            elif field == "content":
                self._apply_inline_content_edit(step, value)
            elif field == "coords":
                self._apply_coords_edit(step, value)
            elif field == "wait":
                step["wait_before"] = max(0.0, _clamp_float(value, float(step.get("wait_before", 0.0))))
        except ValueError as exc:
            messagebox.showwarning("入力エラー", str(exc))
            return
        self.project["updated_at"] = _now_iso()
        self._refresh_tree()
        self._load_step_into_editor(step)
        self._focus_step_by_id(step["id"])
        self._append_log(f"操作を更新しました: {step.get('auto_label', '')}")
        self._close_inline_editor()

    def _apply_inline_content_edit(self, step: dict, value: str) -> None:
        action = step.get("action")
        if action == "text_input":
            step["text"] = value
            step["input_mode"] = _input_mode_for_text(value)
            return
        if action == "key":
            self._apply_key_content_edit_from_text(step, value)
            return
        if action == "wheel":
            self._apply_wheel_content_edit(step, value)
            return
        if action == "click":
            self._apply_click_content_edit(step, value)

    def _apply_coords_edit(self, step: dict, value: str) -> None:
        text = value.strip().replace("，", ",")
        if not text:
            return
        parts = [part.strip() for part in text.replace(",", " ").split() if part.strip()]
        if len(parts) < 2:
            raise ValueError("座標は 'x, y' 形式で入力してください")
        step["x"] = _clamp_int(parts[0], int(step.get("x", 0)))
        step["y"] = _clamp_int(parts[1], int(step.get("y", 0)))

    def _coords_input_value(self, step: dict) -> str:
        x = step.get("x")
        y = step.get("y")
        if x is None or y is None:
            return ""
        return f"{x}, {y}"

    def _inline_edit_helper(self, step: dict, field: str) -> str:
        action = step.get("action", "")
        if field == "display_name":
            return "表示名を入力します。例: 検索ボタン"
        if field == "content":
            if action == "text_input":
                return "文字列を入力します。日本語/全角も可。例: 検索 キーワード"
            if action == "key":
                return "キー入力を指定します。例: Ctrl + C / Enter / F5"
            if action == "wheel":
                return "ホイール操作を指定します。例: vertical down 3 / horizontal up 2"
            if action == "click":
                return "クリック内容を指定します。例: left x1 / right x1 / middle x1"
            return "内容を入力します。"
        if field == "coords":
            return "座標を入力します。例: 320, 240"
        if field == "wait":
            return "待機秒を入力します。例: 0.5"
        return ""

    def _apply_key_content_edit_from_text(self, step: dict, value: str) -> None:
        text = value.strip()
        if not text:
            return
        parts = [part.strip() for part in text.split("+")]
        if len(parts) == 1:
            step["key_name"] = parts[0].lower()
            step["modifiers"] = []
            return
        step["key_name"] = parts[-1].lower()
        step["modifiers"] = [_normalize_hotkey_name(part) for part in parts[:-1]]

    def _apply_wheel_content_edit(self, step: dict, value: str) -> None:
        text = value.strip().lower()
        if not text:
            return
        parts = text.replace(",", " ").split()
        if len(parts) >= 3:
            if parts[0] in {"vertical", "horizontal"}:
                step["axis"] = parts[0]
                direction = parts[1]
                delta = _clamp_int(parts[2], int(step.get("delta", 0)))
            else:
                step["axis"] = "vertical"
                direction = parts[0]
                delta = _clamp_int(parts[1], int(step.get("delta", 0))) if len(parts) > 1 else int(step.get("delta", 0))
        elif len(parts) == 2:
            step["axis"] = "vertical"
            direction = parts[0]
            delta = _clamp_int(parts[1], int(step.get("delta", 0)))
        else:
            return
        step["direction"] = direction if direction in {"up", "down"} else ("up" if delta > 0 else "down")
        step["delta"] = delta

    def _apply_click_content_edit(self, step: dict, value: str) -> None:
        text = value.strip().lower()
        if not text:
            return
        parts = text.replace("x", " x ").split()
        if parts:
            button = parts[0]
            if button in {"left", "right", "middle"}:
                step["button"] = button
        if "x" in parts:
            idx = parts.index("x")
            if idx + 1 < len(parts):
                step["click_count"] = max(1, _clamp_int(parts[idx + 1], int(step.get("click_count", 1))))

    def _load_step_into_editor(self, step: dict) -> None:
        self.step_type_var.set(self._display_action_name(step))
        self.auto_label_var.set(step.get("auto_label", ""))
        self.display_name_var.set(step.get("display_name", ""))
        self.content_var.set(self._step_content(step))
        self.wait_var.set(str(step.get("wait_before", 0.0)))
        self.enabled_var.set(bool(step.get("enabled", True)))
        self.confirm_var.set(bool(step.get("confirm_before_playback", False)))
        self.step_confirm_note_var.set("このチェックは現在のステップを再生中に個別確認したい場合に使います。")
        self.step_meta_var.set(
            f"id={step.get('id', '')}\n"
            f"action={step.get('action', '')}\n"
            f"order={step.get('order', '')}\n"
            f"stop_key={self.project['settings'].get('stop_key', 'esc')}"
        )
        self.root.after_idle(self._focus_edit_field)

    def _focus_edit_field(self) -> None:
        if self.display_name_entry is None:
            return
        try:
            self.display_name_entry.focus_set()
            self.display_name_entry.selection_range(0, "end")
        except Exception:
            pass

    def _load_selected_step_into_editor(self) -> None:
        if self.selected_step_id is None:
            return
        for step in self.project["steps"]:
            if step["id"] == self.selected_step_id:
                self._load_step_into_editor(step)
                return

    def apply_step_edit(self) -> None:
        if self.selected_step_id is None:
            messagebox.showwarning("未選択", "編集する操作を選択してください。")
            return
        step = next((s for s in self.project["steps"] if s["id"] == self.selected_step_id), None)
        if step is None:
            return
        step["display_name"] = self.display_name_var.get().strip()
        step["wait_before"] = max(0.0, _clamp_float(self.wait_var.get(), 0.0))
        step["enabled"] = bool(self.enabled_var.get())
        step["confirm_before_playback"] = bool(self.confirm_var.get())
        if step.get("action") == "text_input":
            step["text"] = self.content_var.get()
            step["input_mode"] = _input_mode_for_text(step["text"])
        elif step.get("action") == "key":
            self._apply_key_content_edit(step)
        self.project["updated_at"] = _now_iso()
        self._refresh_tree()
        self._focus_step_by_id(step["id"])
        self._append_log(f"操作を更新しました: {step.get('auto_label', '')}")

    def _apply_key_content_edit(self, step: dict) -> None:
        text = self.content_var.get().strip()
        if not text:
            return
        parts = [part.strip() for part in text.split("+")]
        if len(parts) == 1:
            step["key_name"] = parts[0].lower()
            step["modifiers"] = []
            return
        step["key_name"] = parts[-1].lower()
        step["modifiers"] = [_normalize_hotkey_name(part) for part in parts[:-1]]

    def delete_selected_step(self) -> None:
        if self.selected_step_id is None:
            return
        step = next((s for s in self.project["steps"] if s["id"] == self.selected_step_id), None)
        if step is None:
            return
        if not messagebox.askyesno("削除", f"{step.get('auto_label', '')} を削除しますか？"):
            return
        self.project["steps"] = [s for s in self.project["steps"] if s["id"] != self.selected_step_id]
        self._rebuild_orders()
        self.project["updated_at"] = _now_iso()
        self.selected_step_id = None
        self.selected_step_index = None
        self._refresh_tree()
        self._append_log("操作を削除しました")

    def _rebuild_orders(self) -> None:
        for idx, step in enumerate(self.project["steps"], start=1):
            step["order"] = idx
        self._retitle_auto_labels()

    def _retitle_auto_labels(self) -> None:
        counters = {
            "click_left": 0,
            "click_right": 0,
            "click_middle": 0,
            "double_click": 0,
            "wheel": 0,
            "input": 0,
            "shortcut": 0,
            "key": 0,
            "move": 0,
        }
        for step in self.project["steps"]:
            if step.get("action") == "click":
                button = step.get("button", "left")
                count = int(step.get("click_count", 1))
                if count >= 2:
                    counters["double_click"] += 1
                    step["auto_label"] = f"ダブルクリック{counters['double_click']}"
                elif button == "right":
                    counters["click_right"] += 1
                    step["auto_label"] = f"右クリック{counters['click_right']}"
                elif button == "middle":
                    counters["click_middle"] += 1
                    step["auto_label"] = f"中クリック{counters['click_middle']}"
                else:
                    counters["click_left"] += 1
                    step["auto_label"] = f"マウスクリック{counters['click_left']}"
            elif step.get("action") == "wheel":
                counters["wheel"] += 1
                step["auto_label"] = f"ホイール操作{counters['wheel']}"
            elif step.get("action") == "text_input":
                counters["input"] += 1
                step["auto_label"] = f"入力欄{counters['input']}"
            elif step.get("action") == "key":
                if step.get("modifiers"):
                    counters["shortcut"] += 1
                    step["auto_label"] = f"ショートカット{counters['shortcut']}"
                else:
                    counters["key"] += 1
                    step["auto_label"] = f"キー操作{counters['key']}"
            elif step.get("action") == "move":
                counters["move"] += 1
                step["auto_label"] = f"マウス移動{counters['move']}"

    def _focus_step_by_id(self, step_id: str) -> None:
        if step_id not in self.tree.get_children():
            return
        self.tree.selection_set(step_id)
        self.tree.see(step_id)

    def start_recording(self) -> None:
        if keyboard is None or mouse is None:
            messagebox.showerror("依存関係不足", "pynput がインストールされていません。")
            return
        if self.recording or self.playing:
            return
        if self.project["steps"] and not messagebox.askyesno("記録開始", "既存の操作ログを破棄して新しく記録しますか？"):
            return

        self.project["steps"] = []
        self.project["execution_log"] = []
        self._rebuild_orders()
        self._refresh_tree()
        self._append_log("記録を開始します。Esc で終了します。")

        self.recording_stop_event = threading.Event()
        self.recording_start_monotonic = time.perf_counter()
        self.last_committed_ts = None
        self.text_buffer = ""
        self.text_buffer_mode = None
        self.text_buffer_start_ts = None
        self.text_buffer_last_ts = None
        self.active_modifiers = set()
        self.last_click_step_index = None
        self.last_click_signature = None
        self.last_click_ts = None
        self.last_move_ts = None
        self.last_move_point = None
        self._set_recording_controls(True)

        self.recording_thread = threading.Thread(target=self._record_worker, daemon=True)
        self.recording_thread.start()

    def stop_recording(self) -> None:
        if not self.recording:
            return
        self.recording_stop_event.set()
        self._append_log("記録停止要求を受け付けました")

    def _record_worker(self) -> None:
        mouse_listener = None
        keyboard_listener = None
        try:
            mouse_listener = mouse.Listener(on_move=self._on_record_mouse_move, on_click=self._on_record_click, on_scroll=self._on_record_scroll)
            keyboard_listener = keyboard.Listener(on_press=self._on_record_key_press, on_release=self._on_record_key_release)
            mouse_listener.start()
            keyboard_listener.start()
            while not self.recording_stop_event.is_set():
                time.sleep(0.05)
            self._flush_text_buffer(time.perf_counter() - self.recording_start_monotonic)
        except Exception as exc:
            self._queue("error", f"記録中にエラーが発生しました: {exc}")
        finally:
            try:
                if mouse_listener is not None:
                    mouse_listener.stop()
            except Exception:
                pass
            try:
                if keyboard_listener is not None:
                    keyboard_listener.stop()
            except Exception:
                pass
            self.project["updated_at"] = _now_iso()
            self._queue("recording_done")
            self._queue("refresh")

    def _event_ts(self) -> float:
        return time.perf_counter() - self.recording_start_monotonic

    def _wait_before_for(self, event_ts: float) -> float:
        if self.last_committed_ts is None:
            return 0.0
        return max(0.0, round(event_ts - self.last_committed_ts, 3))

    def _commit_step(self, step: dict, event_ts: float) -> None:
        step["wait_before"] = self._wait_before_for(event_ts)
        step["enabled"] = True
        step["confirm_before_playback"] = False
        step["order"] = len(self.project["steps"]) + 1
        self.project["steps"].append(step)
        self.last_committed_ts = event_ts
        self.project["updated_at"] = _now_iso()
        self._queue("refresh")

    def _step_id(self, prefix: str) -> str:
        idx = sum(1 for s in self.project["steps"] if str(s.get("id", "")).startswith(prefix)) + 1
        return f"{prefix}_{idx}"

    def _current_modifiers(self) -> list[str]:
        ordered = ["ctrl", "alt", "shift", "win"]
        return [m for m in ordered if m in self.active_modifiers]

    def _flush_text_buffer(self, event_ts: float | None = None) -> None:
        if not self.text_buffer:
            return
        if event_ts is None:
            event_ts = self._event_ts()
        step = {
            "id": self._step_id("input"),
            "auto_label": f"入力欄{sum(1 for s in self.project['steps'] if s.get('action') == 'text_input') + 1}",
            "display_name": f"入力欄{sum(1 for s in self.project['steps'] if s.get('action') == 'text_input') + 1}",
            "action": "text_input",
            "text": self.text_buffer,
            "input_mode": self.text_buffer_mode or _input_mode_for_text(self.text_buffer),
        }
        self._commit_step(step, self.text_buffer_start_ts or event_ts)
        self.last_committed_ts = self.text_buffer_last_ts or event_ts
        self.text_buffer = ""
        self.text_buffer_mode = None
        self.text_buffer_start_ts = None
        self.text_buffer_last_ts = None

    def _append_text_char(self, ch: str, event_ts: float) -> None:
        mode = _input_mode_for_char(ch)
        if not self.text_buffer:
            self.text_buffer_start_ts = event_ts
            self.text_buffer_mode = mode
        elif self.text_buffer_mode not in {None, mode} and self.text_buffer_mode != mode:
            self._flush_text_buffer(event_ts)
            self.text_buffer_start_ts = event_ts
            self.text_buffer_mode = mode
        self.text_buffer += ch
        self.text_buffer_mode = self.text_buffer_mode or mode
        self.text_buffer_last_ts = event_ts

    def _backspace_text(self, event_ts: float) -> None:
        if self.text_buffer:
            self.text_buffer = self.text_buffer[:-1]
            self.text_buffer_last_ts = event_ts

    def _record_shortcut_or_key(self, key_name: str, event_ts: float) -> None:
        modifiers = self._current_modifiers()
        if modifiers:
            step = {
                "id": self._step_id("shortcut"),
                "auto_label": f"ショートカット{sum(1 for s in self.project['steps'] if s.get('modifiers')) + 1}",
                "display_name": f"{' + '.join(_pretty_modifier(m) for m in modifiers + [key_name])}",
                "action": "key",
                "key_name": key_name,
                "key_event": "down",
                "modifiers": modifiers,
            }
        else:
            step = {
                "id": self._step_id("key"),
                "auto_label": f"キー操作{sum(1 for s in self.project['steps'] if s.get('action') == 'key' and not s.get('modifiers')) + 1}",
                "display_name": _pretty_key_name(key_name),
                "action": "key",
                "key_name": key_name,
                "key_event": "down",
                "modifiers": [],
            }
        self._commit_step(step, event_ts)

    def _on_record_mouse_move(self, x: int, y: int) -> None:
        if not self.record_mouse_move_var.get():
            return
        if self.recording_stop_event.is_set():
            return False
        event_ts = self._event_ts()
        if self.last_move_ts is not None and event_ts - self.last_move_ts < 0.25:
            if self.last_move_point is not None:
                if abs(self.last_move_point[0] - x) < 20 and abs(self.last_move_point[1] - y) < 20:
                    return
        self._flush_text_buffer(event_ts)
        step = {
            "id": self._step_id("move"),
            "auto_label": f"マウス移動{sum(1 for s in self.project['steps'] if s.get('action') == 'move') + 1}",
            "display_name": f"マウス移動{sum(1 for s in self.project['steps'] if s.get('action') == 'move') + 1}",
            "action": "move",
            "x": int(x),
            "y": int(y),
        }
        self._commit_step(step, event_ts)
        self.last_move_ts = event_ts
        self.last_move_point = (int(x), int(y))

    def _on_record_click(self, x: int, y: int, button, pressed: bool) -> None:
        if self.recording_stop_event.is_set():
            return False
        if not pressed:
            return
        event_ts = self._event_ts()
        self._flush_text_buffer(event_ts)
        button_name = getattr(button, "name", str(button)).lower()
        if button_name not in {"left", "right", "middle"}:
            button_name = "left"
        if (
            self.last_click_step_index is not None
            and self.last_click_signature is not None
            and self.last_click_signature[0] == button_name
            and abs(self.last_click_signature[1] - x) <= 4
            and abs(self.last_click_signature[2] - y) <= 4
            and event_ts - (self.last_click_ts or 0.0) <= float(self.project["settings"]["double_click_threshold_seconds"])
        ):
            prev = self.project["steps"][self.last_click_step_index]
            prev["click_count"] = int(prev.get("click_count", 1)) + 1
            prev["auto_label"] = f"ダブルクリック{sum(1 for s in self.project['steps'] if s.get('action') == 'click' and int(s.get('click_count', 1)) >= 2) }"
            prev["display_name"] = prev.get("display_name") or prev["auto_label"]
            self.last_committed_ts = event_ts
            self.last_click_ts = event_ts
            self.project["updated_at"] = _now_iso()
            self._queue("refresh")
            return
        step = {
            "id": self._step_id("click"),
            "auto_label": self._next_click_label(button_name),
            "display_name": self._next_click_label(button_name),
            "action": "click",
            "button": button_name,
            "click_count": 1,
            "x": int(x),
            "y": int(y),
        }
        self._commit_step(step, event_ts)
        self.last_click_step_index = len(self.project["steps"]) - 1
        self.last_click_signature = (button_name, int(x), int(y), 1)
        self.last_click_ts = event_ts

    def _next_click_label(self, button_name: str) -> str:
        if button_name == "right":
            count = sum(1 for s in self.project["steps"] if s.get("action") == "click" and s.get("button") == "right" and int(s.get("click_count", 1)) == 1) + 1
            return f"右クリック{count}"
        if button_name == "middle":
            count = sum(1 for s in self.project["steps"] if s.get("action") == "click" and s.get("button") == "middle" and int(s.get("click_count", 1)) == 1) + 1
            return f"中クリック{count}"
        count = sum(1 for s in self.project["steps"] if s.get("action") == "click" and s.get("button") == "left" and int(s.get("click_count", 1)) == 1) + 1
        return f"マウスクリック{count}"

    def _on_record_scroll(self, x: int, y: int, dx: int, dy: int) -> None:
        if self.recording_stop_event.is_set():
            return False
        event_ts = self._event_ts()
        self._flush_text_buffer(event_ts)
        if dx == 0 and dy == 0:
            return
        axis = "horizontal" if dx else "vertical"
        delta = int(dx if dx else dy)
        direction = "up" if delta > 0 else "down"
        step = {
            "id": self._step_id("wheel"),
            "auto_label": f"ホイール操作{sum(1 for s in self.project['steps'] if s.get('action') == 'wheel') + 1}",
            "display_name": f"ホイール操作{sum(1 for s in self.project['steps'] if s.get('action') == 'wheel') + 1}",
            "action": "wheel",
            "x": int(x),
            "y": int(y),
            "delta": delta,
            "direction": direction,
            "axis": axis,
        }
        self._commit_step(step, event_ts)

    def _on_record_key_press(self, key) -> bool | None:
        if self.recording_stop_event.is_set():
            return False
        event_ts = self._event_ts()
        key_name = self._key_name(key)
        if key_name in SPECIAL_STOP_KEYS:
            self.recording_stop_event.set()
            return False
        if key_name in IME_TOGGLE_KEYS:
            self._flush_text_buffer(event_ts)
            return
        if key_name in MODIFIER_KEYS:
            self._flush_text_buffer(event_ts)
            self.active_modifiers.add(key_name)
            return
        if key_name == "space" and not self._current_modifiers_interfere():
            self._append_text_char(" ", event_ts)
            return
        if key_name == "backspace" and not self._current_modifiers_interfere():
            if self.text_buffer:
                self._backspace_text(event_ts)
                return
        if _is_printable_char(self._char_from_key(key)):
            if not self._current_modifiers_interfere():
                self._append_text_char(self._char_from_key(key), event_ts)
                return
        self._flush_text_buffer(event_ts)
        self._record_shortcut_or_key(key_name, event_ts)

    def _on_record_key_release(self, key) -> None:
        if self.recording_stop_event.is_set():
            return False
        key_name = self._key_name(key)
        if key_name in MODIFIER_KEYS:
            self.active_modifiers.discard(key_name)

    def _current_modifiers_interfere(self) -> bool:
        return bool(self.active_modifiers.intersection({"ctrl", "alt", "win"}))

    def _char_from_key(self, key) -> str:
        try:
            if hasattr(key, "char") and key.char is not None:
                return str(key.char)
        except Exception:
            pass
        return ""

    def _key_name(self, key) -> str:
        if hasattr(key, "char") and key.char is not None:
            char = str(key.char)
            if char == " ":
                return "space"
            return char.lower()
        name = str(key).replace("Key.", "")
        return _normalize_hotkey_name(name)

    def start_playback(self, test_mode: bool = False) -> None:
        if pyautogui is None or keyboard is None:
            messagebox.showerror("依存関係不足", "pyautogui / pynput がインストールされていません。")
            return
        if self.recording or self.playing:
            return
        if not self._project_has_runnable_content(self.project):
            messagebox.showinfo("再生", "再生する操作がありません。")
            return
        if self.project["settings"].get("confirm_before_playback", True):
            if not messagebox.askyesno("再生確認", f"{'テスト再生' if test_mode else '再生'}を開始しますか？\nEsc または左上移動で停止できます。"):
                return
        else:
            self._append_log(f"{'テスト再生' if test_mode else '再生'}確認を省略しました")
        self.playback_stop_event = threading.Event()
        self.playing = True
        self._set_playback_controls(True)
        self._append_log(f"{'テスト再生' if test_mode else '再生'}を開始します")
        self.playback_thread = threading.Thread(target=self._playback_worker, args=(copy.deepcopy(self.project), test_mode), daemon=True)
        self.playback_thread.start()
        return

    def _start_playback_stop_listener(self) -> None:
        if keyboard is None:
            return

        def on_press(key) -> bool | None:
            if self._key_name(key) in SPECIAL_STOP_KEYS:
                self.playback_stop_event.set()
                return False
            return None

        listener = keyboard.Listener(on_press=on_press)
        listener.daemon = True
        listener.start()
        self.playback_hotkey_listener = listener

    def _playback_worker(self, project_data: dict, test_mode: bool) -> None:
        if pyautogui is None:
            self._queue("error", "pyautogui がありません。")
            self._queue("playback_done", "再生を終了しました")
            return
        pyautogui.FAILSAFE = True
        pyautogui.PAUSE = 0.0
        self._start_playback_stop_listener()
        try:
            self._play_project_payload(project_data, test_mode=test_mode, include_launcher=True, depth=0)
        except pyautogui.FailSafeException:
            self.playback_stop_event.set()
            self._queue("error", "PyAutoGUI FailSafe")
        except Exception as exc:
            self.playback_stop_event.set()
            self._queue("error", f"再生中にエラーが発生しました: {exc}")
        finally:
            if self.playback_hotkey_listener is not None:
                try:
                    self.playback_hotkey_listener.stop()
                except Exception:
                    pass
            self.project["updated_at"] = _now_iso()
            self._queue("playback_done", "再生を終了しました")

    def _project_has_runnable_content(self, project_data: dict) -> bool:
        if project_data.get("workflow_enabled") and self._workflow_has_nodes(project_data.get("workflow", [])):
            return True
        return any(step.get("enabled", True) for step in project_data.get("steps", []))

    def _workflow_has_nodes(self, nodes: list[dict]) -> bool:
        for node in nodes:
            if node.get("type") in {"project", "condition", "elif", "loop"}:
                return True
            if self._workflow_has_nodes(list(node.get("then", []))):
                return True
            if self._workflow_has_nodes(list(node.get("elif", []))):
                return True
            if self._workflow_has_nodes(list(node.get("else", []))):
                return True
            if self._workflow_has_nodes(list(node.get("body", []))):
                return True
        return False

    def _play_project_payload(
        self,
        project_data: dict,
        test_mode: bool,
        include_launcher: bool,
        depth: int,
    ) -> None:
        if self.playback_stop_event.is_set():
            return
        if depth > 8:
            raise RuntimeError("プロジェクトの連結が深すぎます")

        launcher = project_data.get("launcher", {})
        if include_launcher and launcher.get("enabled"):
            self._run_launcher(launcher)
            wait_seconds = float(launcher.get("wait_seconds", 0.0))
            if wait_seconds > 0:
                self._countdown_sleep(wait_seconds)

        if include_launcher:
            countdown = int(project_data.get("settings", {}).get("countdown_seconds", 3))
            self._countdown(countdown)

        if project_data.get("workflow_enabled") and project_data.get("workflow"):
            self._run_workflow_nodes(list(project_data.get("workflow", [])), test_mode=test_mode, depth=depth)
            return

        steps = [copy.deepcopy(step) for step in project_data.get("steps", []) if step.get("enabled", True)]
        if test_mode:
            limit = int(project_data.get("settings", {}).get("test_playback_step_limit", 5))
            steps = steps[:limit]
        for idx, step in enumerate(steps, start=1):
            if self.playback_stop_event.is_set():
                self._append_execution_log(step, False, "停止キーまたはFailSafe")
                break
            wait_before = float(step.get("wait_before", 0.0))
            if wait_before > 0:
                self._sleep_with_stop(wait_before)
            if self.playback_stop_event.is_set():
                self._append_execution_log(step, False, "停止キーまたはFailSafe")
                break
            try:
                if bool(step.get("confirm_before_playback", False)):
                    label = step.get("auto_label", "")
                    if not self._ask_yes_no_threadsafe("ステップ確認", f"{label} を実行しますか？"):
                        self.playback_stop_event.set()
                        self._append_execution_log(step, False, "ステップ確認で中止")
                        break
                self._play_step(step)
                self._append_execution_log(step, True, "")
                self._queue("log", f"実行 {idx}/{len(steps)}: {step.get('auto_label', '')}")
            except pyautogui.FailSafeException:
                self.playback_stop_event.set()
                self._append_execution_log(step, False, "PyAutoGUI FailSafe")
                break
            except Exception as exc:
                self.playback_stop_event.set()
                self._append_execution_log(step, False, str(exc))
                self._queue("error", f"再生中にエラーが発生しました: {exc}")
                break

    def _run_workflow_nodes(self, nodes: list[dict], test_mode: bool, depth: int) -> None:
        for index, node in enumerate(nodes, start=1):
            if self.playback_stop_event.is_set():
                return
            kind = str(node.get("type", ""))
            if not bool(node.get("enabled", True)):
                self._queue("log", f"フロー {index}/{len(nodes)}: {node.get('name', kind)} [無効]")
                continue
            self._queue("log", f"フロー {index}/{len(nodes)}: {node.get('name', kind)}")
            if kind == "project":
                self._run_workflow_project_node(node, test_mode=test_mode, depth=depth + 1)
                continue
            if kind == "condition":
                result = self._evaluate_workflow_condition(node)
                elif_nodes = list(node.get("elif", []))
                if "then" in node or "else" in node or elif_nodes:
                    branch = "then" if result else "else"
                    if result:
                        self._run_workflow_nodes(list(node.get(branch, [])), test_mode=test_mode, depth=depth + 1)
                    else:
                        handled = False
                        for elif_node in elif_nodes:
                            if self.playback_stop_event.is_set():
                                return
                            if not bool(elif_node.get("enabled", True)):
                                continue
                            if self._evaluate_workflow_condition(elif_node):
                                self._run_workflow_nodes(list(elif_node.get("then", [])), test_mode=test_mode, depth=depth + 1)
                                handled = True
                                break
                        if not handled:
                            self._run_workflow_nodes(list(node.get("else", [])), test_mode=test_mode, depth=depth + 1)
                else:
                    jump = _clamp_int(node.get("jump_true" if result else "jump_false", 1), 1)
                    if jump > 1:
                        self._queue("log", f"条件スキップ: +{jump - 1}")
                continue
            if kind == "elif":
                if self._evaluate_workflow_condition(node):
                    self._run_workflow_nodes(list(node.get("then", [])), test_mode=test_mode, depth=depth + 1)
                continue
            if kind == "loop":
                mode = str(node.get("mode", "count"))
                if mode == "while":
                    guard = 0
                    while not self.playback_stop_event.is_set():
                        if not self._evaluate_workflow_condition(node):
                            break
                        self._queue("log", f"ループ while {guard + 1}")
                        self._run_workflow_nodes(list(node.get("body", [])), test_mode=test_mode, depth=depth + 1)
                        guard += 1
                        if guard >= 1000:
                            raise RuntimeError("while ループが1000回を超えたため停止しました")
                else:
                    repeat_count = max(1, _clamp_int(node.get("repeat_count", 1), 1))
                    for loop_index in range(repeat_count):
                        if self.playback_stop_event.is_set():
                            return
                        self._queue("log", f"ループ {loop_index + 1}/{repeat_count}")
                        self._run_workflow_nodes(list(node.get("body", [])), test_mode=test_mode, depth=depth + 1)
                continue

    def _evaluate_workflow_condition(self, node: dict) -> bool:
        source = str(node.get("source", "clipboard"))
        operator = str(node.get("operator", "contains"))
        subject_text = str(node.get("text", ""))
        file_path = str(node.get("file_path", "")).strip()
        value = str(node.get("value", ""))
        if source == "clipboard":
            if pyperclip is None:
                raise RuntimeError("条件分岐の clipboard 判定には pyperclip が必要です")
            try:
                current = pyperclip.paste() or ""
            except Exception as exc:
                raise RuntimeError(f"クリップボードを取得できません: {exc}") from exc
        elif source == "file":
            if not file_path:
                raise RuntimeError("条件分岐の file 判定にはファイルパスが必要です")
            path = Path(file_path)
            if not path.exists():
                raise RuntimeError(f"条件分岐の file 判定対象が見つかりません: {path}")
            encoding = str(node.get("file_encoding", "utf-8")).strip() or "utf-8"
            try:
                current = path.read_text(encoding=encoding)
            except UnicodeDecodeError:
                current = path.read_text(encoding="cp932", errors="ignore")
            except Exception as exc:
                raise RuntimeError(f"条件分岐の file 判定対象を読み取れません: {exc}") from exc
        else:
            current = subject_text
        current_text = str(current)
        compare_text = str(value)
        if operator == "not_contains":
            return compare_text not in current_text
        if operator == "not_equals":
            return current_text != compare_text
        if operator == "equals":
            return current_text == compare_text
        if operator == "startswith":
            return current_text.startswith(compare_text)
        if operator == "endswith":
            return current_text.endswith(compare_text)
        if operator == "regex":
            try:
                return re.search(compare_text, current_text) is not None
            except re.error as exc:
                raise RuntimeError(f"正規表現が不正です: {exc}") from exc
        if operator == "is_empty":
            return current_text == ""
        if operator == "not_empty":
            return current_text != ""
        return compare_text in current_text

    def _run_workflow_project_node(self, node: dict, test_mode: bool, depth: int) -> None:
        path_text = str(node.get("project_path", "")).strip()
        if not path_text:
            raise RuntimeError("プロジェクトパスが指定されていません")
        if path_text == "__current__":
            project_data = copy.deepcopy(self.project)
        else:
            path = Path(path_text)
            project_data = self._load_project_data(path)
            if project_data is None:
                raise RuntimeError(f"読み込み失敗: {path}")
        self._play_project_payload(project_data, test_mode=test_mode, include_launcher=False, depth=depth)

    def _countdown_sleep(self, seconds: float) -> None:
        end = time.time() + seconds
        while time.time() < end and not self.playback_stop_event.is_set():
            time.sleep(0.1)

    def _countdown(self, seconds: int) -> None:
        if seconds <= 0:
            return
        self._queue("log", f"{seconds} 秒後に再生を開始します")
        for remaining in range(seconds, 0, -1):
            if self.playback_stop_event.is_set():
                return
            self._queue("status", None)
            self._queue("log", f"{remaining}...")
            time.sleep(1.0)

    def _sleep_with_stop(self, seconds: float) -> None:
        end = time.time() + seconds
        while time.time() < end:
            if self.playback_stop_event.is_set():
                return
            time.sleep(min(0.05, max(0.01, end - time.time())))

    def _run_launcher(self, launcher: dict) -> None:
        import os
        import subprocess
        import webbrowser

        target = launcher.get("target", "")
        launch_type = launcher.get("type", "url")
        args = launcher.get("args", "")
        wd = launcher.get("working_dir", "") or None
        if not target:
            return
        self._queue("log", f"起動: {launch_type} {target}")
        if launch_type == "url":
            webbrowser.open(target)
            return
        if launch_type == "folder":
            subprocess.Popen(["explorer", target], cwd=wd)
            return
        if launch_type in {"exe", "bat", "cmd", "powershell"}:
            if launch_type == "powershell":
                cmd = ["powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", target]
                if args:
                    cmd.extend(args.split())
            elif launch_type in {"bat", "cmd"}:
                cmd = ["cmd", "/c", target]
                if args:
                    cmd.extend(args.split())
            else:
                cmd = [target]
                if args:
                    cmd.extend(args.split())
            subprocess.Popen(cmd, cwd=wd if wd else os.path.dirname(target) or None)

    def _play_step(self, step: dict) -> None:
        action = step.get("action")
        if action == "click":
            self._play_click(step)
        elif action == "wheel":
            self._play_wheel(step)
        elif action == "text_input":
            self._play_text(step.get("text", ""))
        elif action == "key":
            self._play_key(step)
        elif action == "move":
            self._play_move(step)

    def _play_click(self, step: dict) -> None:
        x = int(step.get("x", 0))
        y = int(step.get("y", 0))
        button = _pyautogui_key_name(str(step.get("button", "left")))
        click_count = int(step.get("click_count", 1))
        pyautogui.moveTo(x, y, duration=0)
        if click_count >= 2:
            pyautogui.click(x=x, y=y, clicks=click_count, button=button)
        else:
            pyautogui.click(x=x, y=y, button=button)

    def _play_wheel(self, step: dict) -> None:
        x = int(step.get("x", 0))
        y = int(step.get("y", 0))
        delta = int(step.get("delta", 0))
        pyautogui.moveTo(x, y, duration=0)
        if step.get("axis") == "horizontal":
            pyautogui.hscroll(delta)
        else:
            pyautogui.scroll(delta)

    def _play_move(self, step: dict) -> None:
        pyautogui.moveTo(int(step.get("x", 0)), int(step.get("y", 0)), duration=0)

    def _play_key(self, step: dict) -> None:
        modifiers = [ _pyautogui_key_name(m) for m in step.get("modifiers", []) ]
        key_name = _pyautogui_key_name(str(step.get("key_name", "")))
        if modifiers:
            pyautogui.hotkey(*modifiers, key_name)
            return
        pyautogui.press(key_name)

    def _play_text(self, text: str) -> None:
        if not text:
            return
        input_mode = _input_mode_for_text(text)
        if input_mode != "ascii":
            if pyperclip is None:
                raise RuntimeError("日本語または全角文字の再生には pyperclip が必要です")
            clipboard_text = text
            try:
                old_value = pyperclip.paste()
            except Exception:
                old_value = None
            try:
                pyperclip.copy(clipboard_text)
                pyautogui.hotkey("ctrl", "v")
            finally:
                if old_value is not None:
                    try:
                        pyperclip.copy(old_value)
                    except Exception:
                        pass
            return
        pyautogui.write(text, interval=0)

    def _append_execution_log(self, step: dict, success: bool, message: str) -> None:
        self.project["execution_log"].append(
            {
                "time": _now_iso(),
                "step_id": step.get("id", ""),
                "auto_label": step.get("auto_label", ""),
                "success": bool(success),
                "message": message,
            }
        )

    def _ask_yes_no_threadsafe(self, title: str, message: str) -> bool:
        result = {"done": False, "value": False}

        def ask() -> None:
            try:
                result["value"] = bool(messagebox.askyesno(title, message))
            finally:
                result["done"] = True

        self.root.after(0, ask)
        while not result["done"]:
            if self.playback_stop_event.is_set():
                return False
            time.sleep(0.05)
        return bool(result["value"])

    def _refresh_tree_selection_after_reload(self) -> None:
        if self.selected_step_id and self.selected_step_id in self.tree.get_children():
            self.tree.selection_set(self.selected_step_id)

    def open_project_browser(self) -> None:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は一覧を開けません。")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("プロジェクト一覧")
        dlg.geometry("1280x860")
        dlg.transient(self.root)
        dlg.grab_set()

        frame = ttk.Frame(dlg, padding=10)
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(0, weight=1)
        frame.rowconfigure(2, weight=1)

        sort_var = tk.StringVar(value="hotkey")

        shortcut_box = ttk.LabelFrame(frame, text="プロジェクトショートカット", padding=8)
        shortcut_box.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0, 10))
        shortcut_box.columnconfigure(0, weight=1)

        shortcut_columns = ("slot", "hotkey", "name", "recent", "status", "path")
        shortcut_tree = ttk.Treeview(shortcut_box, columns=shortcut_columns, show="headings", selectmode="browse", height=8)
        shortcut_headings = {
            "slot": "スロット",
            "hotkey": "ショートカット",
            "name": "プロジェクト名",
            "recent": "最近",
            "status": "状態",
            "path": "保存先",
        }
        shortcut_widths = {
            "slot": 70,
            "hotkey": 130,
            "name": 240,
            "recent": 70,
            "status": 90,
            "path": 560,
        }
        for key in shortcut_columns:
            shortcut_tree.heading(key, text=shortcut_headings[key])
            shortcut_tree.column(key, width=shortcut_widths[key], anchor="w", stretch=True)
        shortcut_tree.grid(row=0, column=0, sticky="ew")
        shortcut_scroll = ttk.Scrollbar(shortcut_box, orient="vertical", command=shortcut_tree.yview)
        shortcut_scroll.grid(row=0, column=1, sticky="ns")
        shortcut_tree.configure(yscrollcommand=shortcut_scroll.set)
        shortcut_tree.tag_configure("unassigned", background="#fff4e6")
        shortcut_tree.tag_configure("current", background="#e9ffe9")

        columns = ("hotkey", "recent", "name", "steps", "updated", "status", "path")
        tree = ttk.Treeview(frame, columns=columns, show="headings", selectmode="browse")
        headings = {
            "hotkey": "ショートカット",
            "recent": "最近",
            "name": "プロジェクト名",
            "steps": "操作数",
            "updated": "更新日時",
            "status": "状態",
            "path": "保存先",
        }
        widths = {
            "hotkey": 130,
            "recent": 70,
            "name": 220,
            "steps": 80,
            "updated": 180,
            "status": 90,
            "path": 380,
        }
        for key in columns:
            tree.heading(key, text=headings[key])
            tree.column(key, width=widths[key], anchor="w", stretch=True)
        tree.grid(row=2, column=0, sticky="nsew")

        scroll = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        scroll.grid(row=2, column=1, sticky="ns")
        tree.configure(yscrollcommand=scroll.set)
        tree.tag_configure("unassigned", background="#fff4e6")
        tree.tag_configure("current", background="#e9ffe9")

        def load_selected() -> None:
            selection = tree.selection() or shortcut_tree.selection()
            if not selection:
                messagebox.showinfo("選択", "開くプロジェクトを一覧から選択してください。")
                return
            source_tree = tree if tree.selection() else shortcut_tree
            values = source_tree.item(selection[0], "values")
            if len(values) < 7:
                return
            selected_path = str(values[6]).strip()
            if not selected_path or selected_path == "(未保存)":
                self._append_log("未保存の現在プロジェクトは一覧からは開けません。")
                return
            path = Path(selected_path)
            dlg.destroy()
            self._load_project_from_path(path)

        def refresh_list() -> None:
            tree.delete(*tree.get_children())
            current_path_text = str(self.current_path) if self.current_path is not None else "(未保存)"
            current_hotkey = _pretty_project_hotkey(self.project.get("project_hotkey", ""))
            current_recent = ""
            if self.current_path is not None:
                normalized = str(self.current_path.resolve())
                if normalized in self.recent_project_paths:
                    current_recent = f"#{self.recent_project_paths.index(normalized) + 1}"
            tree.insert(
                "",
                "end",
                values=(
                    current_hotkey,
                    current_recent,
                    self.project.get("project_name", "project"),
                    len(self.project.get("steps", [])),
                    self.project.get("updated_at", ""),
                    "編集中" if self.current_path is None else "現在",
                    current_path_text,
                ),
                tags=("current",) if self.current_path is not None else ("unassigned",),
            )
            if sort_var.get() == "recent":
                paths = self._sorted_project_files()
            else:
                paths = self._sorted_project_files_by_hotkey()
            for path in paths:
                if self.current_path is not None and path.resolve() == self.current_path.resolve():
                    continue
                summary = self._project_summary(path)
                recent = f"#{summary['recent_rank']}" if summary["recent_rank"] is not None else ""
                hotkey = _pretty_project_hotkey(summary["project_hotkey"])
                status = "割当済み" if summary["project_hotkey"] else "未割当"
                tree.insert(
                    "",
                    "end",
                    tags=("unassigned",) if not summary["project_hotkey"] else (),
                    values=(
                        hotkey,
                        recent,
                        summary["project_name"],
                        summary["steps"],
                        summary["updated_at"],
                        status,
                        summary["path"],
                    ),
                )

        def refresh_shortcuts() -> None:
            shortcut_tree.delete(*shortcut_tree.get_children())
            current_hotkey = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
            current_recent = ""
            if self.current_path is not None:
                normalized = str(self.current_path.resolve())
                if normalized in self.recent_project_paths:
                    current_recent = f"#{self.recent_project_paths.index(normalized) + 1}"
            shortcut_tree.insert(
                "",
                "end",
                values=(
                    "現在",
                    _pretty_project_hotkey(current_hotkey),
                    self.project.get("project_name", "project"),
                    current_recent,
                    "割当済み" if current_hotkey else "未割当",
                    str(self.current_path) if self.current_path is not None else "(未保存)",
                ),
                tags=("current",) if current_hotkey else ("unassigned",),
            )

            slot_owner: dict[int, dict[str, object]] = {}
            for path in self._available_project_files():
                summary = self._project_summary(path)
                digit = _hotkey_digit(summary.get("project_hotkey", ""))
                if digit is None:
                    continue
                if digit not in slot_owner:
                    slot_owner[digit] = summary

            current_norm = str(self.current_path.resolve()) if self.current_path is not None else None
            for digit in range(1, 10):
                owner = slot_owner.get(digit)
                if owner is None and current_hotkey == _default_project_hotkey(digit):
                    owner = {
                        "path": str(self.current_path) if self.current_path is not None else "",
                        "project_name": self.project.get("project_name", "project"),
                        "recent_rank": current_recent[1:] if current_recent.startswith("#") else "",
                        "project_hotkey": current_hotkey,
                    }
                if owner is None:
                    shortcut_tree.insert(
                        "",
                        "end",
                        values=(
                            str(digit),
                            _pretty_project_hotkey(_default_project_hotkey(digit)),
                            "",
                            "",
                            "未割当",
                            "",
                        ),
                        tags=("unassigned",),
                    )
                else:
                    path_text = str(owner.get("path", ""))
                    if current_norm is not None and path_text and str(Path(path_text).resolve()) == current_norm:
                        path_text = str(self.current_path) if self.current_path is not None else path_text
                    recent_rank = owner.get("recent_rank")
                    shortcut_tree.insert(
                        "",
                        "end",
                        values=(
                            str(digit),
                            _pretty_project_hotkey(_default_project_hotkey(digit)),
                            str(owner.get("project_name", "")),
                            f"#{recent_rank}" if recent_rank else "",
                            "割当済み",
                            path_text,
                        ),
                        tags=("current",) if current_norm is not None and path_text and str(Path(path_text).resolve()) == current_norm else (),
                    )

        def open_selected(_event: tk.Event | None = None) -> None:
            load_selected()

        def open_shortcut_selected(_event: tk.Event | None = None) -> None:
            selection = shortcut_tree.selection()
            if not selection:
                return
            values = shortcut_tree.item(selection[0], "values")
            if len(values) < 6:
                return
            path_text = str(values[5])
            if not path_text or path_text == "(未保存)":
                if self.current_path is None:
                    messagebox.showinfo("選択", "未保存の現在プロジェクトは一覧からは実行できません。")
                    return
                dlg.destroy()
                self.start_playback(test_mode=False)
                return
            path = Path(path_text)
            dlg.destroy()
            if self._load_project_from_path(path):
                self.start_playback(test_mode=False)

        sort_row = ttk.Frame(frame)
        sort_row.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(0, 8))
        ttk.Label(sort_row, text="並び順").pack(side="left")
        ttk.Radiobutton(sort_row, text="ショートカット順", value="hotkey", variable=sort_var, command=refresh_list).pack(side="left", padx=8)
        ttk.Radiobutton(sort_row, text="最近使った順", value="recent", variable=sort_var, command=refresh_list).pack(side="left", padx=8)

        button_row = ttk.Frame(frame)
        button_row.grid(row=3, column=0, columnspan=2, sticky="ew", pady=(10, 0))
        ttk.Button(button_row, text="開く", command=load_selected).pack(side="left")
        ttk.Button(button_row, text="更新", command=refresh_list).pack(side="left", padx=6)
        ttk.Button(button_row, text="ショートカット再生", command=open_shortcut_selected).pack(side="left", padx=6)
        ttk.Button(button_row, text="閉じる", command=dlg.destroy).pack(side="right")

        tree.bind("<Double-1>", open_selected)
        shortcut_tree.bind("<Double-1>", open_shortcut_selected)
        refresh_list()
        refresh_shortcuts()

    def _load_project_from_path(self, path: Path) -> bool:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は読み込めません。")
            return False
        try:
            with path.open("r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as exc:
            messagebox.showerror("読み込み失敗", str(exc))
            return False
        self._apply_loaded_project(data)
        self.current_path = path
        self._touch_recent_project(path)
        self._refresh_status()
        self._append_log(f"読み込みました: {path}")
        return True

    def save_project(self) -> None:
        self.project["project_name"] = self.project_name_var.get().strip() or self.project["project_name"]
        self.project["updated_at"] = _now_iso()
        if self.current_path is None:
            self.project["project_hotkey"] = self._ensure_project_hotkey(ignore_path=None)
        else:
            self.project["project_hotkey"] = self._ensure_project_hotkey(ignore_path=self.current_path)
        self._retitle_auto_labels()
        self._rebuild_orders()
        path = self.current_path
        if path is None:
            suggested = f"{self.project['project_name']}.json"
            save_path = filedialog.asksaveasfilename(
                title="保存先を選択",
                defaultextension=".json",
                initialfile=suggested,
                filetypes=[("JSON", "*.json")],
            )
            if not save_path:
                return
            path = Path(save_path)
        data = copy.deepcopy(self.project)
        with path.open("w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        self.current_path = path
        self._touch_recent_project(path)
        self._sync_project_hotkey_var()
        self._refresh_status()
        self._append_log(f"保存しました: {path}")

    def load_project(self) -> None:
        if self.recording or self.playing:
            messagebox.showwarning("実行中", "記録中または再生中は読み込めません。")
            return
        path = filedialog.askopenfilename(
            title="読み込むJSONを選択",
            filetypes=[("JSON", "*.json")],
        )
        if not path:
            return
        self._load_project_from_path(Path(path))

    def _apply_loaded_project(self, data: dict) -> None:
        self.project = data
        if "project_name" not in self.project:
            self.project["project_name"] = "project"
        self.project["project_hotkey"] = self._normalize_project_hotkey(self.project.get("project_hotkey", ""))
        self.project.setdefault("workflow_enabled", False)
        self.project.setdefault("workflow", [])
        self.project.setdefault("settings", {})
        self.project["settings"].setdefault("record_mouse_move", False)
        self.project["settings"].setdefault("confirm_before_playback", True)
        self.record_mouse_move_var.set(bool(self.project["settings"].get("record_mouse_move", False)))
        if hasattr(self, "playback_confirm_var"):
            self.playback_confirm_var.set(bool(self.project["settings"].get("confirm_before_playback", True)))
        self.project_name_var.set(self.project["project_name"])
        self._sync_project_hotkey_var()
        self._retitle_auto_labels()
        self._rebuild_orders()
        self.selected_step_id = None
        self.selected_step_index = None
        self._refresh_tree()
        self._refresh_status()

    def _on_close(self) -> None:
        if self.recording or self.playing:
            if not messagebox.askyesno("終了確認", "記録中または再生中ですが終了しますか？"):
                return
            self.recording_stop_event.set()
            self.playback_stop_event.set()
        if self.project_hotkey_listener is not None:
            try:
                self.project_hotkey_listener.stop()
            except Exception:
                pass
        self.root.destroy()

    def _toggle_record_mouse_move(self) -> None:
        self.project["settings"]["record_mouse_move"] = bool(self.record_mouse_move_var.get())
        self.project["updated_at"] = _now_iso()
        self._refresh_status()

    def _toggle_playback_confirm(self) -> None:
        self.project["settings"]["confirm_before_playback"] = bool(self.playback_confirm_var.get())
        self.project["updated_at"] = _now_iso()
        self._refresh_status()


def main() -> None:
    root = tk.Tk()
    if pyautogui is not None:
        pyautogui.FAILSAFE = True
        pyautogui.PAUSE = 0.0
    app = RecorderApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Izanami Sector Survey - Elite Dangerous Journal Sync Tool
Standalone Desktop Companion App for Windows & Linux
Includes strict FSS All Bodies verification, System Count Controller, Non-Existent Boxel bulk logger,
and accurate EDAstro 16-point 3D polygon boundary evaluation for Galactic Region #7 (Izanami).
"""

import os
import sys
import re
import json
import time
import glob
import threading
import webbrowser
import urllib.request
import urllib.error
import tkinter as tk
from tkinter import ttk, messagebox, filedialog

# Try importing pystray and PIL for tray minimization, with graceful fallback
HAVE_PYSTRAY = False
try:
    from PIL import Image, ImageDraw
    import pystray
    HAVE_PYSTRAY = True
except ImportError:
    HAVE_PYSTRAY = False

CONFIG_FILE = os.path.expanduser("~/.izanami_journal_uploader.json")
CURRENT_VERSION = "2.6.1"
VERSION_CHECK_URL = "https://www.irishraven.com/api/version"

# Canonical EDAstro 16-Point Boundary (Region #7 - Izanami)
IZANAMI_POLYGON_XZ = [
    (-13500.0, 24500.0),
    (-18000.0, 27500.0),
    (-22500.0, 33000.0),
    (-21000.0, 41000.0),
    (-17000.0, 47500.0),
    (-12000.0, 51000.0),
    (-5000.0,  52500.0),
    (5000.0,   52500.0),
    (12000.0,  51000.0),
    (17000.0,  47500.0),
    (21000.0,  41000.0),
    (22500.0,  33000.0),
    (18000.0,  27500.0),
    (13500.0,  25500.0),
    (0.0,      25000.0),
    (-8000.0,  24500.0),
]
IZANAMI_Y_MIN = -3500.0
IZANAMI_Y_MAX = 3500.0

COORDS_CACHE = {}

def check_coordinate_with_server(coords, server_url, timeout=2.0):
    """ Offloads coordinate spatial boundary evaluation to the main backend connection """
    if not coords or len(coords) < 3 or not server_url:
        return None
    try:
        cache_key = (round(float(coords[0]), 1), round(float(coords[1]), 1), round(float(coords[2]), 1))
        if cache_key in COORDS_CACHE:
            return COORDS_CACHE[cache_key]

        payload = json.dumps({
            "x": float(coords[0]),
            "y": float(coords[1]),
            "z": float(coords[2])
        }).encode('utf-8')
        url = server_url.rstrip('/') + '/api/spatial/check_boundary'
        req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            data = json.loads(resp.read().decode('utf-8'))
            is_inside = bool(data.get('is_in_izanami', False))
            COORDS_CACHE[cache_key] = is_inside
            return is_inside
    except Exception:
        return None

def is_in_izanami(coords, server_url=None):
    """
    Checks if 3D galactic coordinates [x, y, z] are within Izanami (Galactic Region #7).
    First attempts to offload to the authoritative main backend connection.
    Falls back gracefully to canonical EDAstro 16-point 3D polygon.
    """
    if not coords or not isinstance(coords, (list, tuple)) or len(coords) < 3:
        return False
    
    if server_url:
        res = check_coordinate_with_server(coords, server_url)
        if res is not None:
            return res
    if not coords or not isinstance(coords, (list, tuple)) or len(coords) < 3:
        return False
    try:
        x = float(coords[0])
        y = float(coords[1])
        z = float(coords[2])

        if not (IZANAMI_Y_MIN <= y <= IZANAMI_Y_MAX):
            return False

        inside = False
        n = len(IZANAMI_POLYGON_XZ)
        p1x, p1z = IZANAMI_POLYGON_XZ[0]

        for i in range(n + 1):
            p2x, p2z = IZANAMI_POLYGON_XZ[i % n]
            if min(p1z, p2z) < z <= max(p1z, p2z):
                if x <= max(p1x, p2x):
                    if p1z != p2z:
                        x_inters = (z - p1z) * (p2x - p1x) / (p2z - p1z) + p1x
                    if p1x == p2x or x <= x_inters:
                        inside = not inside
            p1x, p1z = p2x, p2z

        return inside
    except (ValueError, TypeError):
        return False

def get_resource_path(relative_path):
    """ Get absolute path to resource, works for dev and PyInstaller """
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

DEFAULT_WIN_PATH = os.path.join(os.path.expanduser("~"), "Saved Games", "Frontier Developments", "Elite Dangerous")
DEFAULT_LINUX_PATH = os.path.join(os.path.expanduser("~"), ".steam", "steam", "steamapps", "compatdata", "359320", "pfx", "drive_c", "users", "steamuser", "Saved Games", "Frontier Developments", "Elite Dangerous")

def get_default_journal_dir():
    if os.path.exists(DEFAULT_WIN_PATH):
        return DEFAULT_WIN_PATH
    if os.path.exists(DEFAULT_LINUX_PATH):
        return DEFAULT_LINUX_PATH
    return DEFAULT_WIN_PATH

def parse_system_to_boxel(sys_name):
    if not sys_name:
        return None, None, None, None
    sys_name = sys_name.strip()
    match = re.match(r"^(.*?)\s+([a-zA-Z]{2}-[a-zA-Z])\s+(.+)$", sys_name, re.IGNORECASE)
    if not match:
        return None, None, None, None
    sector = match.group(1).strip().title()
    subsector = match.group(2).strip().upper()
    rest = match.group(3).strip()
    if "-" in rest:
        m = re.match(r"^([a-hA-H]\d*)-(\d+)$", rest)
        if m:
            mass_code = m.group(1).upper()
            system_index = int(m.group(2))
            return sector, subsector, mass_code, system_index
    else:
        m = re.match(r"^([a-hA-H])(\d*)$", rest)
        if m:
            mass_code = m.group(1).upper()
            system_index = int(m.group(2)) if m.group(2) else 0
            return sector, subsector, mass_code, system_index
    return None, None, None, None


class IzanamiSyncApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Izanami Survey - Journal Sync Companion")
        self.root.geometry("700x720")
        self.root.minsize(640, 580)

        self.server_url = tk.StringVar(value="https://www.irishraven.com")
        self.api_key = tk.StringVar(value="")
        self.journal_dir = tk.StringVar(value=get_default_journal_dir())
        self.active_cmdr = tk.StringVar(value="Auto-detecting...")
        self.current_boxel = tk.StringVar(value="None Detected")
        self.current_system = tk.StringVar(value="None")
        self.fss_status = tk.StringVar(value="Waiting for FSS scan...")
        self.boxel_system_count = tk.StringVar(value="1")
        self.show_settings = False

        self.pending_jump_event = None
        self.current_system_address = None

        self.load_config()

        icon_path = get_resource_path("space.ico")
        if os.path.exists(icon_path):
            try:
                self.root.iconbitmap(icon_path)
            except Exception:
                try:
                    if HAVE_PYSTRAY:
                        from PIL import ImageTk
                        img = Image.open(icon_path)
                        photo = ImageTk.PhotoImage(img)
                        self.root.iconphoto(True, photo)
                except Exception:
                    pass

        self.setup_ui()

        self.current_boxel.trace_add("write", self.on_boxel_changed)
        self.root.protocol("WM_DELETE_WINDOW", self.on_window_close)
        self.tray_icon = None

        if not self.api_key.get().strip():
            self.toggle_settings_panel(force_show=True)

        self.auto_detect_from_folder_thread()
        self.start_live_watcher()
        self.check_for_updates(interactive=False)

    def load_config(self):
        if os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    if data.get("api_key"):
                        self.api_key.set(data.get("api_key"))
                    if data.get("server_url"):
                        self.server_url.set(data.get("server_url"))
                    if data.get("journal_dir"):
                        self.journal_dir.set(data.get("journal_dir"))
            except Exception as e:
                print(f"Error loading config: {e}")

    def save_config(self):
        data = {
            "api_key": self.api_key.get().strip(),
            "server_url": self.server_url.get().strip(),
            "journal_dir": self.journal_dir.get().strip()
        }
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
            messagebox.showinfo("Saved", "Settings saved successfully!")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save settings: {e}")

    def setup_ui(self):
        self.root.configure(bg="#0b0e14")

        style = ttk.Style()
        style.theme_use('clam')

        style.configure('.', background='#0b0e14', foreground='#e1e6ed', font=('Segoe UI', 9))
        style.configure('TFrame', background='#0b0e14')
        style.configure('Card.TFrame', background='#161b22')

        style.configure('TLabelframe', background='#161b22', foreground='#ff9d00', bordercolor='#30363d', lightcolor='#30363d', darkcolor='#30363d', borderwidth=1)
        style.configure('TLabelframe.Label', background='#161b22', foreground='#ff9d00', font=('Segoe UI', 10, 'bold'))

        style.configure('TLabel', background='#161b22', foreground='#e1e6ed')
        style.configure('Header.TLabel', background='#0b0e14', foreground='#ff9d00', font=('Segoe UI', 13, 'bold'))
        style.configure('SubHeader.TLabel', background='#0b0e14', foreground='#00d8ff', font=('Segoe UI', 8, 'bold'))

        style.configure('Cmdr.TLabel', background='#161b22', foreground='#ff9d00', font=('Consolas', 10, 'bold'))
        style.configure('System.TLabel', background='#161b22', foreground='#00d8ff', font=('Consolas', 10, 'bold'))
        style.configure('Boxel.TLabel', background='#161b22', foreground='#00ff66', font=('Consolas', 11, 'bold'))
        style.configure('Fss.TLabel', background='#161b22', foreground='#ffcc00', font=('Segoe UI', 9, 'bold'))
        style.configure('Muted.TLabel', background='#161b22', foreground='#8b949e', font=('Segoe UI', 8, 'italic'))

        style.configure('Primary.TButton', background='#ff9d00', foreground='#000000', font=('Segoe UI', 9, 'bold'), borderwidth=0, focuscolor='none', padding=5)
        style.map('Primary.TButton', background=[('active', '#ffb733'), ('disabled', '#443311')], foreground=[('disabled', '#888888')])

        style.configure('Cyan.TButton', background='#00d8ff', foreground='#000000', font=('Segoe UI', 9, 'bold'), borderwidth=0, focuscolor='none', padding=5)
        style.map('Cyan.TButton', background=[('active', '#66e5ff'), ('disabled', '#113344')])

        style.configure('Dark.TButton', background='#21262d', foreground='#00d8ff', font=('Segoe UI', 9, 'bold'), borderwidth=1, focuscolor='none', padding=5)
        style.map('Dark.TButton', background=[('active', '#30363d')])

        style.configure('Green.TButton', background='#00ff66', foreground='#000000', font=('Segoe UI', 9, 'bold'), borderwidth=0, focuscolor='none', padding=5)
        style.map('Green.TButton', background=[('active', '#66ff99')])

        style.configure('Red.TButton', background='#ff3344', foreground='#ffffff', font=('Segoe UI', 9, 'bold'), borderwidth=0, focuscolor='none', padding=5)
        style.map('Red.TButton', background=[('active', '#ff6677')])

        style.configure('TEntry', fieldbackground='#0d1117', foreground='#00d8ff', bordercolor='#30363d', lightcolor='#30363d', darkcolor='#30363d', insertcolor='#ff9d00', padding=4)
        style.configure('TSpinbox', fieldbackground='#0d1117', foreground='#00d8ff', bordercolor='#30363d', arrowcolor='#00d8ff', padding=3)
        style.configure('Horizontal.TProgressbar', troughcolor='#161b22', background='#00d8ff', bordercolor='#30363d', lightcolor='#00d8ff', darkcolor='#00d8ff')

        canvas = tk.Canvas(self.root, bg="#0b0e14", highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.root, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas, padding="15")

        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        main_frame = scrollable_frame

        # Header
        self.header_frame = ttk.Frame(main_frame)
        self.header_frame.pack(fill=tk.X, pady=(0, 8))

        title_sub_frame = ttk.Frame(self.header_frame)
        title_sub_frame.pack(side=tk.LEFT)

        header_lbl = ttk.Label(title_sub_frame, text=f"🚀 IZANAMI SECTOR SURVEY (v{CURRENT_VERSION})", style="Header.TLabel")
        header_lbl.pack(anchor=tk.W)

        sub_header_lbl = ttk.Label(title_sub_frame, text="JOURNAL SYNC • EDASTRO BOUNDARIES • FSS ENFORCED", style="SubHeader.TLabel")
        sub_header_lbl.pack(anchor=tk.W)

        btn_header_group = ttk.Frame(self.header_frame)
        btn_header_group.pack(side=tk.RIGHT, pady=2)

        self.btn_update = ttk.Button(btn_header_group, text="🔄 Check Updates", style="Dark.TButton", command=lambda: self.check_for_updates(interactive=True))
        self.btn_update.pack(side=tk.LEFT, padx=3)

        self.btn_cog_settings = ttk.Button(btn_header_group, text="⚙️ Settings", style="Dark.TButton", command=self.toggle_settings_panel)
        self.btn_cog_settings.pack(side=tk.LEFT, padx=3)

        # Collapsible Settings
        self.settings_panel = ttk.LabelFrame(main_frame, text=" ⚙️ Connection & Folder Settings ", padding="10")
        
        ttk.Label(self.settings_panel, text="API Key:").grid(row=0, column=0, sticky=tk.W, pady=3)
        api_entry = ttk.Entry(self.settings_panel, textvariable=self.api_key, width=38, show="*")
        api_entry.grid(row=0, column=1, sticky=tk.W, padx=5, pady=3)

        btn_toggle_key = ttk.Button(self.settings_panel, text="👁", width=3, style="Dark.TButton", command=lambda: api_entry.config(show="" if api_entry.cget("show") == "*" else "*"))
        btn_toggle_key.grid(row=0, column=2, padx=2)

        ttk.Label(self.settings_panel, text="Server URL:").grid(row=1, column=0, sticky=tk.W, pady=3)
        ttk.Entry(self.settings_panel, textvariable=self.server_url, width=38).grid(row=1, column=1, sticky=tk.W, padx=5, pady=3)

        btn_save = ttk.Button(self.settings_panel, text="💾 Save", style="Primary.TButton", command=self.save_config)
        btn_save.grid(row=1, column=2, padx=2)

        ttk.Label(self.settings_panel, text="Journal Folder:").grid(row=2, column=0, sticky=tk.W, pady=3)
        ttk.Entry(self.settings_panel, textvariable=self.journal_dir, width=38).grid(row=2, column=1, sticky=tk.W, padx=5, pady=3)
        ttk.Button(self.settings_panel, text="Browse...", style="Dark.TButton", command=self.browse_directory).grid(row=2, column=2, padx=2)

        ver_frame = ttk.Frame(self.settings_panel)
        ver_frame.grid(row=3, column=0, columnspan=3, sticky=tk.W, pady=(8, 2))
        ttk.Label(ver_frame, text=f"Companion Version: v{CURRENT_VERSION}  |", font=('Segoe UI', 8), foreground='#8b949e').pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(ver_frame, text="🔍 Check for Updates Now", style="Dark.TButton", command=lambda: self.check_for_updates(interactive=True)).pack(side=tk.LEFT)

        # Status Frame
        self.status_frame = ttk.LabelFrame(main_frame, text=" Active Exploration Status (FSS Enforced) ", padding="10")
        self.status_frame.pack(fill=tk.X, pady=5)

        ttk.Label(self.status_frame, text="Active CMDR:").grid(row=0, column=0, sticky=tk.W, pady=2)
        ttk.Label(self.status_frame, textvariable=self.active_cmdr, style="Cmdr.TLabel").grid(row=0, column=1, sticky=tk.W, padx=8, pady=2)

        ttk.Label(self.status_frame, text="Current System:").grid(row=1, column=0, sticky=tk.W, pady=2)
        ttk.Label(self.status_frame, textvariable=self.current_system, style="System.TLabel").grid(row=1, column=1, sticky=tk.W, padx=8, pady=2)

        ttk.Label(self.status_frame, text="Current Boxel:").grid(row=2, column=0, sticky=tk.W, pady=2)
        ttk.Label(self.status_frame, textvariable=self.current_boxel, style="Boxel.TLabel").grid(row=2, column=1, sticky=tk.W, padx=8, pady=2)

        ttk.Label(self.status_frame, text="FSS Status:").grid(row=3, column=0, sticky=tk.W, pady=2)
        self.fss_lbl = ttk.Label(self.status_frame, textvariable=self.fss_status, style="Fss.TLabel")
        self.fss_lbl.grid(row=3, column=1, sticky=tk.W, padx=8, pady=2)

        btn_rescan = ttk.Button(self.status_frame, text="🔄 Scan Folder", style="Dark.TButton", command=self.auto_detect_from_folder_thread)
        btn_rescan.grid(row=0, column=2, rowspan=2, padx=8, sticky=tk.E)

        # Action & Count Frame
        boxel_action_frame = ttk.LabelFrame(main_frame, text=" Boxel Survey Actions & System Count Controller ", padding="10")
        boxel_action_frame.pack(fill=tk.X, pady=5)

        cnt_row = ttk.Frame(boxel_action_frame)
        cnt_row.pack(fill=tk.X, pady=2)

        ttk.Label(cnt_row, text="Boxel Total Systems Count:").pack(side=tk.LEFT, padx=(0, 6))
        self.sys_count_spin = ttk.Spinbox(cnt_row, from_=0, to_=99999, textvariable=self.boxel_system_count, width=8)
        self.sys_count_spin.pack(side=tk.LEFT, padx=4)

        btn_update_cnt = ttk.Button(cnt_row, text="🔢 Update System Count", style="Cyan.TButton", command=self.update_active_boxel_system_count)
        btn_update_cnt.pack(side=tk.LEFT, padx=6)

        btn_3d_exp = ttk.Button(cnt_row, text="🧊 3D Boxel Explorer", style="Secondary.TButton", command=self.open_3d_boxel_explorer)
        btn_3d_exp.pack(side=tk.LEFT, padx=6)

        self.btn_mark_complete = ttk.Button(
            boxel_action_frame, 
            text="✔ Mark Current Boxel Complete", 
            style="Green.TButton",
            command=self.mark_current_boxel_complete
        )
        self.btn_mark_complete.pack(fill=tk.X, pady=(6, 2))

        self.mark_feedback_lbl = ttk.Label(
            boxel_action_frame, 
            text="Sync standard: Only systems where 'FSS All Bodies Found' is logged will be counted.",
            style="Muted.TLabel"
        )
        self.mark_feedback_lbl.pack(anchor=tk.W, pady=(2, 0))

        # Bulk Doesn't Exist Section
        self.notexist_frame = ttk.LabelFrame(main_frame, text=" 🚫 Bulk Log Non-Existent Boxels (Copy-Paste Section) ", padding="10")
        self.notexist_frame.pack(fill=tk.X, pady=5)

        ttk.Label(
            self.notexist_frame, 
            text="Paste boxels (e.g. from 3D Explorer or flight notes) to mark them as 'Doesn't Exist' (0/0 systems):",
            style="Muted.TLabel"
        ).pack(anchor=tk.W, pady=(0, 4))

        self.txt_notexist = tk.Text(self.notexist_frame, height=4, bg="#0d1117", fg="#00d8ff", insertbackground="#ff9d00", font=("Consolas", 9), relief=tk.FLAT, borderwidth=1)
        self.txt_notexist.pack(fill=tk.X, pady=3)

        notexist_btn_row = ttk.Frame(self.notexist_frame)
        notexist_btn_row.pack(fill=tk.X, pady=4)

        btn_submit_notexist = ttk.Button(notexist_btn_row, text="🚫 Mark Pasted as Doesn't Exist", style="Red.TButton", command=self.submit_pasted_not_exist)
        btn_submit_notexist.pack(side=tk.LEFT, padx=(0, 4))

        btn_mark_curr_notexist = ttk.Button(notexist_btn_row, text="🚫 Mark Current Boxel (0/0)", style="Dark.TButton", command=self.mark_current_boxel_not_exist)
        btn_mark_curr_notexist.pack(side=tk.LEFT, padx=4)

        btn_paste_clip = ttk.Button(notexist_btn_row, text="📋 Paste Clip", style="Dark.TButton", command=self.paste_clipboard_to_notexist)
        btn_paste_clip.pack(side=tk.RIGHT, padx=2)

        btn_clear_txt = ttk.Button(notexist_btn_row, text="🗑 Clear", style="Dark.TButton", command=lambda: self.txt_notexist.delete("1.0", tk.END))
        btn_clear_txt.pack(side=tk.RIGHT, padx=2)

        # Progress
        progress_frame = ttk.Frame(main_frame, padding="4")
        progress_frame.pack(fill=tk.X, pady=4)

        self.progress_bar = ttk.Progressbar(progress_frame, mode='determinate', style="Horizontal.TProgressbar")
        self.progress_bar.pack(fill=tk.X, pady=2)

        self.status_lbl = ttk.Label(progress_frame, text="Ready to monitor journals (EDAstro verified, FSS All Bodies required).", style="SubHeader.TLabel")
        self.status_lbl.pack(anchor=tk.W)

        # Action Buttons
        btn_action_frame = ttk.Frame(main_frame, padding="4")
        btn_action_frame.pack(fill=tk.X, pady=6)

        ttk.Button(btn_action_frame, text="📡 Sync Historical Journals (FSS Verified)", style="Primary.TButton", command=self.start_historical_sync_thread).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_action_frame, text="📂 Push Single Log...", style="Cyan.TButton", command=self.push_single_file).pack(side=tk.LEFT, padx=3)
        ttk.Button(btn_action_frame, text="📌 Tray", style="Dark.TButton", command=self.minimize_to_tray).pack(side=tk.RIGHT, padx=2)
        ttk.Button(btn_action_frame, text="🗕 Minimize", style="Dark.TButton", command=self.minimize_window).pack(side=tk.RIGHT, padx=2)

    def toggle_settings_panel(self, force_show=False):
        if force_show:
            self.show_settings = True
        else:
            self.show_settings = not self.show_settings

        if self.show_settings:
            self.settings_panel.pack(fill=tk.X, pady=5, before=self.status_frame)
            self.btn_cog_settings.config(text="⚙️ Hide Settings")
        else:
            self.settings_panel.pack_forget()
            self.btn_cog_settings.config(text="⚙️ Settings")

    def open_3d_boxel_explorer(self):
        base_url = self.server_url.get().strip().rstrip('/')
        sec, sub, mass, _ = parse_system_to_boxel(self.current_system.get())
        if sec and sub and mass:
            url = f"{base_url}/boxel_explorer?sector={urllib.parse.quote(sec)}&boxel={urllib.parse.quote(sub)}+{urllib.parse.quote(mass)}"
        else:
            url = f"{base_url}/boxel_explorer"
        try:
            webbrowser.open_new(url)
            self.update_status("Launched standalone 3D Boxel Explorer in browser.", 100)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to open browser: {e}")

    def on_boxel_changed(self, *args):
        b = self.current_boxel.get()
        if b and b != "None Detected":
            self.btn_mark_complete.config(text=f"✔ Mark Current Boxel Complete ({b})")
            sec, sub, mass, idx = parse_system_to_boxel(self.current_system.get())
            if idx is not None and idx >= 0:
                try:
                    curr_val = int(self.boxel_system_count.get())
                except Exception:
                    curr_val = 1
                self.boxel_system_count.set(str(max(curr_val, idx + 1)))
        else:
            self.btn_mark_complete.config(text="✔ Mark Current Boxel Complete")

    def browse_directory(self):
        selected = filedialog.askdirectory(initialdir=self.journal_dir.get(), title="Select Elite Dangerous Journal Directory")
        if selected:
            self.journal_dir.set(selected)
            self.auto_detect_from_folder_thread()

    def auto_detect_from_folder_thread(self):
        threading.Thread(target=self.auto_detect_from_folder, daemon=True).start()

    def auto_detect_from_folder(self):
        jdir = self.journal_dir.get().strip()
        if not os.path.isdir(jdir):
            self.update_status("Journal directory not found. Please click ⚙ Settings to choose your path.", 0)
            self.root.after(0, lambda: self.active_cmdr.set("Folder Not Found"))
            return

        files = sorted(glob.glob(os.path.join(jdir, "Journal.*.log")), key=os.path.getmtime, reverse=True)
        if not files:
            self.update_status("No Journal.*.log files found in directory.", 0)
            self.root.after(0, lambda: self.active_cmdr.set("No Log Files Found"))
            return

        self.update_status(f"Scanning {len(files)} log files for Commander, position & FSS completions...", 15)

        found_cmdr = None
        found_sys = None
        found_boxel = None
        total_jumps = 0
        fss_completed_events = 0
        izanami_fss_events = 0

        for filepath in files:
            evs, cmdr, sys_name, boxel, jumps_count, fss_count = self.parse_journal_events(filepath)
            total_jumps += jumps_count
            fss_completed_events += fss_count

            for ev in evs:
                sec, sub, mass, _ = parse_system_to_boxel(ev.get("StarSystem", ""))
                if sec and sub and mass:
                    izanami_fss_events += 1

            if not found_cmdr and cmdr:
                found_cmdr = cmdr
            if not found_sys and sys_name:
                found_sys = sys_name
            if not found_boxel and boxel:
                found_boxel = boxel

        if found_cmdr:
            self.root.after(0, lambda c=found_cmdr: self.active_cmdr.set(c))
        else:
            self.root.after(0, lambda: self.active_cmdr.set("Unknown / None Logged"))

        if found_sys:
            self.root.after(0, lambda s=found_sys: self.current_system.set(s))
        else:
            self.root.after(0, lambda: self.current_system.set("None Detected"))

        if found_boxel:
            self.root.after(0, lambda b=found_boxel: self.current_boxel.set(b))
        else:
            self.root.after(0, lambda: self.current_boxel.set("None Detected"))

        msg = f"✅ Folder Scanned: {len(files)} logs ({total_jumps} jumps, {fss_completed_events} FSS completed, {izanami_fss_events} Izanami verified). Watcher active."
        self.update_status(msg, 100)

    def start_live_watcher(self):
        def _watch_loop():
            last_file = None
            last_pos = 0
            pending_jump = None

            while True:
                time.sleep(2)
                jdir = self.journal_dir.get().strip()
                if not os.path.isdir(jdir):
                    continue

                files = sorted(glob.glob(os.path.join(jdir, "Journal.*.log")), key=os.path.getmtime, reverse=True)
                if not files:
                    continue

                latest_file = files[0]
                if latest_file != last_file:
                    last_file = latest_file
                    last_pos = 0

                try:
                    size = os.path.getsize(latest_file)
                    if size > last_pos:
                        with open(latest_file, 'r', encoding='utf-8', errors='ignore') as f:
                            f.seek(last_pos)
                            new_lines = f.readlines()
                            last_pos = f.tell()

                        for line in new_lines:
                            line = line.strip()
                            if not line:
                                continue
                            try:
                                ev = json.loads(line)
                                event_type = ev.get("event")
                                active_c = self.active_cmdr.get()

                                if event_type == "Commander":
                                    cmdr_name = ev.get("Name")
                                    if cmdr_name:
                                        self.root.after(0, lambda c=cmdr_name: self.active_cmdr.set(c))

                                elif event_type in ["FSDJump", "Location", "CarrierJump"]:
                                    sys_name = ev.get("StarSystem")
                                    coords = ev.get("StarPos")
                                    sys_addr = ev.get("SystemAddress")

                                    if sys_name and coords:
                                        in_iz = is_in_izanami(coords, self.server_url.get().strip())
                                        z_val = coords[2] if len(coords) >= 3 else 0

                                        if not in_iz:
                                            self.root.after(0, lambda s=sys_name: self.current_system.set(f"{s} [Outside Izanami]"))
                                            self.root.after(0, lambda: self.current_boxel.set(f"Outside Izanami (Z={z_val:.0f} Ly)"))
                                            self.root.after(0, lambda s=sys_name: self.fss_status.set(f"⚠️ {s} is outside EDAstro Izanami boundaries. Not syncing."))
                                            self.update_status(f"Arrived at {sys_name} (Outside Izanami polygon). Non-Izanami jumps are ignored.", 0)
                                            pending_jump = None
                                            continue

                                        self.root.after(0, lambda s=sys_name: self.current_system.set(s))
                                        sec, sub, mass, idx = parse_system_to_boxel(sys_name)
                                        if sec and sub and mass:
                                            boxel_fmt = f"{sec} {sub} {mass}"
                                            self.root.after(0, lambda b=boxel_fmt: self.current_boxel.set(b))
                                            if idx is not None:
                                                def _upd_c(i=idx):
                                                    try:
                                                        cv = int(self.boxel_system_count.get())
                                                    except Exception:
                                                        cv = 1
                                                    self.boxel_system_count.set(str(max(cv, i + 1)))
                                                self.root.after(0, _upd_c)

                                        pending_jump = {
                                            "event": event_type,
                                            "StarSystem": sys_name,
                                            "StarPos": coords,
                                            "SystemAddress": sys_addr,
                                            "Commander": active_c if active_c not in ["Auto-detecting...", "Folder Not Found", "No Log Files Found"] else None
                                        }

                                        self.root.after(0, lambda s=sys_name: self.fss_status.set(f"⏳ Jump to {s}: Awaiting 'FSS All Bodies Found'..."))
                                        self.update_status(f"Arrived at {sys_name} (Izanami). Awaiting FSS All Bodies scan before syncing...", 40)

                                elif event_type == "FSSDiscoveryScan":
                                    body_cnt = ev.get("BodyCount", 0)
                                    sys_name = ev.get("SystemName", self.current_system.get())
                                    self.root.after(0, lambda c=body_cnt, s=sys_name: self.fss_status.set(f"🔭 Honked {s}: {c} bodies detected. FSS scanning..."))

                                elif event_type == "FSSAllBodiesFound":
                                    sys_name = ev.get("SystemName", "")
                                    body_cnt = ev.get("Count", 0)

                                    self.root.after(0, lambda c=body_cnt, s=sys_name: self.fss_status.set(f"✅ FSS All Bodies Found ({c} bodies in {s})!"))
                                    
                                    if pending_jump:
                                        sys_to_sync = pending_jump
                                        if not is_in_izanami(sys_to_sync.get("StarPos")):
                                            self.update_status(f"FSS completed for {sys_to_sync.get('StarSystem')}, but system is outside Izanami. Ignored.", 0)
                                            pending_jump = None
                                            continue

                                        self.update_status(f"✅ FSS All Bodies Complete for {sys_to_sync.get('StarSystem')}! Syncing jump to server...", 75)
                                        ok, res = self.send_events_to_server([sys_to_sync])
                                        if ok:
                                            msg = res.get("msg", f"Synced {sys_to_sync.get('StarSystem')}")
                                            self.update_status(f"Real-time Sync Success: {msg}", 100)
                                        else:
                                            err_msg = res.get("detail", str(res)) if isinstance(res, dict) else str(res)
                                            self.update_status(f"Real-time Sync Error: {err_msg}", 0)
                                        pending_jump = None
                                    else:
                                        curr_s = self.current_system.get()
                                        if curr_s and curr_s != "None":
                                            self.update_status(f"FSS All Bodies completed for {curr_s}. Syncing to server...", 75)
                                            sync_ev = {
                                                "event": "FSDJump",
                                                "StarSystem": curr_s,
                                                "Commander": self.active_cmdr.get()
                                            }
                                            self.send_events_to_server([sync_ev])

                            except json.JSONDecodeError:
                                continue
                except Exception as e:
                    print(f"Error in live watcher: {e}")

        threading.Thread(target=_watch_loop, daemon=True).start()

    def update_status(self, text, progress_val=None):
        def _update():
            self.status_lbl.config(text=text)
            if progress_val is not None:
                self.progress_bar['value'] = progress_val
        self.root.after(0, _update)

    def parse_journal_events(self, file_path):
        confirmed_events = []
        cmdr = None
        current_sys = None
        boxel = None
        total_jumps = 0

        if not os.path.exists(file_path):
            return confirmed_events, cmdr, current_sys, boxel, 0, 0

        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()

            visits = []
            fss_completed_systems = set()
            fss_completed_names = set()

            for line in lines:
                line = line.strip()
                if not line:
                    continue
                try:
                    ev = json.loads(line)
                    event_type = ev.get("event")

                    if event_type == "Commander":
                        cmdr = ev.get("Name")

                    elif event_type in ["FSDJump", "Location", "CarrierJump"]:
                        sys_name = ev.get("StarSystem")
                        coords = ev.get("StarPos")
                        sys_addr = ev.get("SystemAddress")
                        if sys_name:
                            current_sys = sys_name
                            total_jumps += 1
                            sec, sub, mass, _ = parse_system_to_boxel(sys_name)
                            if sec and sub and mass:
                                boxel = f"{sec} {sub} {mass}"
                            
                            if coords:
                                visits.append({
                                    "event": event_type,
                                    "StarSystem": sys_name,
                                    "StarPos": coords,
                                    "SystemAddress": sys_addr,
                                    "Commander": cmdr
                                })

                    elif event_type == "FSSAllBodiesFound":
                        s_name = ev.get("SystemName")
                        s_addr = ev.get("SystemAddress")
                        if s_name:
                            fss_completed_names.add(s_name.strip().lower())
                        if s_addr:
                            fss_completed_systems.add(s_addr)

                except json.JSONDecodeError:
                    continue

            for v in visits:
                s_name = (v.get("StarSystem") or "").strip().lower()
                s_addr = v.get("SystemAddress")
                coords = v.get("StarPos")
                has_fss = (s_addr and s_addr in fss_completed_systems) or (s_name and s_name in fss_completed_names)
                in_iz = is_in_izanami(coords, self.server_url.get().strip())
                if has_fss and in_iz:
                    confirmed_events.append(v)

        except Exception as e:
            print(f"Error reading {file_path}: {e}")

        return confirmed_events, cmdr, current_sys, boxel, total_jumps, len(confirmed_events)

    def send_events_to_server(self, events):
        key = self.api_key.get().strip()
        url = self.server_url.get().strip().rstrip('/') + "/api/journal/batch_sync"

        if not key:
            return False, {"detail": "API Key is missing. Click ⚙ Settings to configure."}

        payload = json.dumps({"api_key": key, "events": events}).encode('utf-8')
        req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})

        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                res_data = json.loads(resp.read().decode('utf-8'))
                return True, res_data
        except urllib.error.HTTPError as e:
            try:
                err_body = json.loads(e.read().decode('utf-8'))
                return False, err_body
            except Exception:
                return False, {"detail": f"HTTP Error {e.code}"}
        except Exception as e:
            return False, {"detail": str(e)}

    def update_active_boxel_system_count(self):
        boxel_str = self.current_boxel.get()
        if not boxel_str or boxel_str == "None Detected":
            messagebox.showwarning("No Boxel Detected", "Please detect or visit a boxel first.")
            return

        sec, sub, mass, _ = parse_system_to_boxel(self.current_system.get())
        if not sec or not sub or not mass:
            m = re.match(r"^(.*?)\s+([a-zA-Z]{2}-[a-zA-Z])\s+(.+)$", boxel_str)
            if not m:
                messagebox.showerror("Invalid Format", f"Unable to parse boxel: {boxel_str}")
                return
            sec = m.group(1).title()
            sub = m.group(2).upper()
            mass = m.group(3).upper()

        key = self.api_key.get().strip()
        if not key:
            messagebox.showerror("API Key Missing", "API Key is required to update system count. Click ⚙ Settings.")
            return

        tot = self.boxel_system_count.get().strip()
        try:
            tot_int = max(0, int(tot))
        except ValueError:
            messagebox.showerror("Invalid Count", "Please enter a valid numeric system count.")
            return

        url = self.server_url.get().strip().rstrip('/') + "/api/journal/update_system_count"
        payload = json.dumps({
            "api_key": key,
            "sector_name": sec,
            "subsector_code": sub,
            "mass_code": mass,
            "total_systems": tot_int
        }).encode('utf-8')

        def _update_count():
            self.update_status(f"Updating system count for {sec} {sub} {mass} to {tot_int}...", 50)
            req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})
            try:
                with urllib.request.urlopen(req, timeout=15) as resp:
                    res = json.loads(resp.read().decode('utf-8'))
                    msg = res.get("msg", "Count updated.")
                    self.update_status(f"✅ {msg}", 100)
                    self.root.after(0, lambda: messagebox.showinfo("System Count Updated", f"✅ {sec} {sub} {mass} total systems updated to {tot_int}!"))
            except Exception as e:
                self.update_status(f"Error updating system count: {e}", 0)
                self.root.after(0, lambda err=str(e): messagebox.showerror("Error", f"Failed to update count: {err}"))

        threading.Thread(target=_update_count, daemon=True).start()

    def submit_pasted_not_exist(self):
        raw_text = self.txt_notexist.get("1.0", tk.END).strip()
        if not raw_text:
            messagebox.showwarning("Empty Input", "Please paste one or more boxel names in the text area first.")
            return

        lines = [line.strip() for line in raw_text.splitlines() if line.strip()]
        if not lines:
            messagebox.showwarning("Empty Input", "No valid boxel lines found.")
            return

        key = self.api_key.get().strip()
        url = self.server_url.get().strip().rstrip('/') + "/api/boxel/batch_not_exist"

        payload = json.dumps({
            "api_key": key,
            "boxels": lines,
            "assigned_cmdr": self.active_cmdr.get()
        }).encode('utf-8')

        def _send():
            self.update_status(f"Marking {len(lines)} boxels as Doesn't Exist (0/0)...", 50)
            req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})
            try:
                with urllib.request.urlopen(req, timeout=20) as resp:
                    res = json.loads(resp.read().decode('utf-8'))
                    count = res.get("count", len(lines))
                    msg = res.get("msg", f"Marked {count} boxels as Non-Existent.")
                    self.update_status(f"✅ Non-Existent Logged: {msg}", 100)
                    self.root.after(0, lambda: messagebox.showinfo(
                        "Non-Existent Boxels Logged",
                        f"✅ Successfully marked {count} boxel(s) as 'Doesn't Exist' (0/0 systems) on the survey portal!\n\n"
                        f"Pasted lines have been registered."
                    ))
            except Exception as e:
                self.update_status(f"Error logging non-existent boxels: {e}", 0)
                self.root.after(0, lambda err=str(e): messagebox.showerror("Error", f"Failed to mark non-existent boxels: {err}"))

        threading.Thread(target=_send, daemon=True).start()

    def mark_current_boxel_not_exist(self):
        boxel_str = self.current_boxel.get()
        if not boxel_str or boxel_str == "None Detected":
            messagebox.showwarning("No Boxel Detected", "Please detect or visit a boxel first.")
            return

        if not messagebox.askyesno("Confirm", f"Mark current boxel {boxel_str} as Non-Existent (Doesn't Exist, 0/0)?"):
            return

        key = self.api_key.get().strip()
        url = self.server_url.get().strip().rstrip('/') + "/api/boxel/batch_not_exist"
        payload = json.dumps({
            "api_key": key,
            "boxels": [boxel_str],
            "assigned_cmdr": self.active_cmdr.get()
        }).encode('utf-8')

        def _send():
            self.update_status(f"Marking {boxel_str} as Doesn't Exist...", 50)
            req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})
            try:
                with urllib.request.urlopen(req, timeout=15) as resp:
                    res = json.loads(resp.read().decode('utf-8'))
                    msg = res.get("msg", "Marked as Doesn't Exist.")
                    self.update_status(f"✅ {msg}", 100)
                    self.root.after(0, lambda: messagebox.showinfo("Success", f"✅ {boxel_str} marked as Doesn't Exist (0/0)!"))
            except Exception as e:
                self.update_status(f"Error: {e}", 0)
                self.root.after(0, lambda err=str(e): messagebox.showerror("Error", f"Failed: {err}"))

        threading.Thread(target=_send, daemon=True).start()

    def paste_clipboard_to_notexist(self):
        try:
            clip = self.root.clipboard_get()
            if clip:
                sep = "\n" if self.txt_notexist.get("1.0", tk.END).strip() else ""
                self.txt_notexist.insert(tk.END, sep + clip.strip())
        except Exception:
            pass

    def start_historical_sync_thread(self):
        t = threading.Thread(target=self.run_historical_sync, daemon=True)
        t.start()

    def run_historical_sync(self):
        jdir = self.journal_dir.get().strip()
        if not os.path.isdir(jdir):
            self.update_status("Error: Journal directory does not exist! Please check ⚙ Settings.", 0)
            return

        files = sorted(glob.glob(os.path.join(jdir, "Journal.*.log")))
        if not files:
            self.update_status("No Journal files found in directory.", 0)
            return

        total_files = len(files)
        all_confirmed_events = []
        total_parsed_jumps = 0
        total_fss_verified = 0

        for idx, filepath in enumerate(files):
            pct = int(((idx + 1) / total_files) * 80)
            fname = os.path.basename(filepath)
            self.update_status(f"Scanning & verifying FSS in {fname} ({idx+1}/{total_files})...", pct)

            evs, cmdr, sys_name, boxel, j_count, fss_count = self.parse_journal_events(filepath)
            total_parsed_jumps += j_count
            total_fss_verified += fss_count

            if cmdr:
                self.root.after(0, lambda c=cmdr: self.active_cmdr.set(c))
            if sys_name:
                self.root.after(0, lambda s=sys_name: self.current_system.set(s))
            if boxel:
                self.root.after(0, lambda b=boxel: self.current_boxel.set(b))

            all_confirmed_events.extend(evs)

        skipped_jumps = total_parsed_jumps - total_fss_verified

        if not all_confirmed_events:
            self.update_status(f"Scan finished: {total_files} logs parsed ({total_parsed_jumps} jumps, {skipped_jumps} skipped). No Izanami FSS events.", 100)
            self.root.after(0, lambda: messagebox.showinfo(
                "Historical Scan Complete",
                f"Historical Scan Completed!\n"
                f"• Logs Scanned: {total_files}\n"
                f"• Total Jumps: {total_parsed_jumps}\n"
                f"• Filtered Out: {skipped_jumps}\n\n"
                f"No systems had 'FSS All Bodies Found' inside Izanami boundaries."
            ))
            return

        self.update_status(f"Uploading {len(all_confirmed_events)} FSS-verified events ({skipped_jumps} skipped) across {total_files} files...", 90)
        success, res_data = self.send_events_to_server(all_confirmed_events)

        if success:
            uploaded_count = res_data.get("processed_events", len(all_confirmed_events))
            updated_boxels = res_data.get("updated_boxels", [])
            summary_msg = f"✅ Up to Date! {total_files} logs | {total_fss_verified} FSS-complete jumps | {uploaded_count} Izanami Sector events synced across {len(updated_boxels)} boxels."
            self.update_status(summary_msg, 100)
            
            self.root.after(0, lambda: messagebox.showinfo(
                "Historical Scan & Upload Complete", 
                f"Historical Journal Scan Completed!\n"
                f"• Log Files Scanned: {total_files}\n"
                f"• Total Jumps Parsed: {total_parsed_jumps}\n"
                f"• FSS All Bodies Verified: {total_fss_verified}\n"
                f"• Filtered / Skipped: {skipped_jumps}\n"
                f"• Izanami Sector Events Synced: {uploaded_count}\n"
                f"• Boxels Updated: {len(updated_boxels)}\n\n"
                f"Your website database is up to date with 100% FSS-verified entries!"
            ))
        else:
            err_msg = res_data.get("detail", str(res_data)) if isinstance(res_data, dict) else str(res_data)
            self.update_status(f"Upload Failed: {err_msg}", 0)
            self.root.after(0, lambda m=err_msg: messagebox.showerror("Upload Error", f"Failed to upload events: {m}"))

    def push_single_file(self):
        filepath = filedialog.askopenfilename(
            initialdir=self.journal_dir.get(), 
            title="Select Journal Log File",
            filetypes=[("Journal Log Files", "Journal.*.log"), ("All Files", "*.*")]
        )
        if not filepath:
            return

        def _push():
            fname = os.path.basename(filepath)
            self.update_status(f"Reading {fname} & verifying EDAstro FSS scans...", 30)
            evs, cmdr, sys_name, boxel, j_count, fss_count = self.parse_journal_events(filepath)

            if cmdr:
                self.active_cmdr.set(cmdr)
            if sys_name:
                self.current_system.set(sys_name)
            if boxel:
                self.current_boxel.set(boxel)

            skipped = j_count - fss_count

            if not evs:
                self.update_status(f"No valid Izanami FSS-completed jump events found in {fname}.", 100)
                messagebox.showinfo("No FSS Verified Jumps", f"No jump events with 'FSS All Bodies Found' in Izanami were found in {fname}.\n({j_count} jumps were skipped).")
                return

            self.update_status(f"Uploading {len(evs)} FSS-verified events from {fname} ({skipped} skipped)...", 70)
            success, res_data = self.send_events_to_server(evs)

            if success:
                count = res_data.get("processed_events", len(evs))
                msg = res_data.get("msg", f"Synced {count} events.")
                self.update_status(f"File Sync Complete: {msg}", 100)
                messagebox.showinfo(
                    "Success", 
                    f"File Pushed Successfully!\n"
                    f"• Total Jumps in File: {j_count}\n"
                    f"• FSS All Bodies Completed: {fss_count}\n"
                    f"• Skipped: {skipped}\n"
                    f"• Izanami Events Synced: {count}\n"
                    f"• Message: {msg}"
                )
            else:
                err_msg = res_data.get("detail", str(res_data)) if isinstance(res_data, dict) else str(res_data)
                self.update_status(f"Push Failed: {err_msg}", 0)
                messagebox.showerror("Error", f"Failed to push file: {err_msg}")

        threading.Thread(target=_push, daemon=True).start()

    def mark_current_boxel_complete(self):
        boxel_str = self.current_boxel.get()
        if not boxel_str or boxel_str == "None Detected":
            messagebox.showwarning("No Boxel Detected", "Please scan folder or push a journal file first to identify your current boxel.")
            return

        sec, sub, mass, _ = parse_system_to_boxel(self.current_system.get())
        if not sec or not sub or not mass:
            m = re.match(r"^(.*?)\s+([a-zA-Z]{2}-[a-zA-Z])\s+(.+)$", boxel_str)
            if not m:
                messagebox.showerror("Invalid Format", f"Unable to parse boxel: {boxel_str}")
                return
            sec = m.group(1).title()
            sub = m.group(2).upper()
            mass = m.group(3).upper()

        key = self.api_key.get().strip()
        url = self.server_url.get().strip().rstrip('/') + "/api/journal/mark_complete"

        if not key:
            messagebox.showerror("API Key Missing", "API Key is required to mark boxel complete! Click ⚙ Settings to configure.")
            return

        tot_sys = self.boxel_system_count.get().strip()
        try:
            tot_int = max(1, int(tot_sys))
        except ValueError:
            tot_int = 1

        def _mark():
            self.update_status(f"Marking {sec} {sub} {mass} as Complete ({tot_int} systems)...", 50)
            payload = json.dumps({
                "api_key": key,
                "sector_name": sec,
                "subsector_code": sub,
                "mass_code": mass,
                "total_systems": tot_int
            }).encode('utf-8')

            req = urllib.request.Request(url, data=payload, headers={'Content-Type': 'application/json'})
            try:
                with urllib.request.urlopen(req, timeout=15) as resp:
                    res_data = json.loads(resp.read().decode('utf-8'))
                    msg = res_data.get("msg", "Marked complete.")
                    self.update_status(f"✅ Complete: {msg}", 100)
                    self.root.after(0, lambda: self.mark_feedback_lbl.config(
                        text=f"✅ Successfully marked {sec} {sub} {mass} ({tot_int}/{tot_int}) as COMPLETED on Izanami Survey!",
                        foreground="#00ff66"
                    ))
                    self.root.after(0, lambda: messagebox.showinfo("Boxel Marked Complete", f"✅ {sec} {sub} {mass} is now marked as Completed ({tot_int}/{tot_int} systems) on the survey website!"))
            except urllib.error.HTTPError as e:
                try:
                    err_body = json.loads(e.read().decode('utf-8'))
                    err_msg = err_body.get("detail", str(e))
                except Exception:
                    err_msg = f"HTTP Error {e.code}"
                self.update_status(f"Error marking complete: {err_msg}", 0)
                self.root.after(0, lambda m=err_msg: self.mark_feedback_lbl.config(text=f"❌ Error: {m}", foreground="#ff3344"))
                self.root.after(0, lambda m=err_msg: messagebox.showerror("Error", f"Failed to mark complete: {m}"))
            except Exception as e:
                self.update_status(f"Error marking complete: {e}", 0)
                self.root.after(0, lambda err=str(e): self.mark_feedback_lbl.config(text=f"❌ Error: {err}", foreground="#ff3344"))
                self.root.after(0, lambda err=str(e): messagebox.showerror("Error", f"Failed to mark complete: {err}"))

        threading.Thread(target=_mark, daemon=True).start()

    def check_for_updates(self, interactive=False):
        def _check():
            try:
                req = urllib.request.Request(
                    VERSION_CHECK_URL, 
                    headers={"User-Agent": f"IzanamiCompanion/{CURRENT_VERSION}"}
                )
                with urllib.request.urlopen(req, timeout=5) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
                    latest_ver = data.get("version")
                    dl_url = data.get("download_url", "https://irishraven.com")

                    if latest_ver and latest_ver != CURRENT_VERSION:
                        self.root.after(0, lambda: self.prompt_update(latest_ver, dl_url))
                    elif interactive:
                        self.root.after(0, lambda: messagebox.showinfo(
                            "Up to Date", 
                            f"You are running the latest version of the Companion (v{CURRENT_VERSION})."
                        ))
            except Exception as e:
                if interactive:
                    self.root.after(0, lambda: messagebox.showwarning(
                        "Update Check", 
                        f"Could not connect to update server: {e}"
                    ))

        threading.Thread(target=_check, daemon=True).start()

    def prompt_update(self, new_ver, dl_url):
        if messagebox.askyesno(
            "Update Available",
            f"A new version of the Companion (v{new_ver}) is available!\n(Current: v{CURRENT_VERSION})\n\nWould you like to open the download page now?"
        ):
            webbrowser.open(dl_url)

    def minimize_window(self):
        self.root.iconify()

    def minimize_to_tray(self):
        if HAVE_PYSTRAY:
            try:
                if not self.tray_icon:
                    image = Image.new('RGB', (64, 64), color=(0, 122, 204))
                    draw = ImageDraw.Draw(image)
                    draw.text((10, 20), "IZN", fill=(255, 255, 255))

                    menu = pystray.Menu(
                        pystray.MenuItem("Restore Izanami Sync", self.restore_from_tray, default=True),
                        pystray.MenuItem("Exit", self.exit_app)
                    )
                    self.tray_icon = pystray.Icon("IzanamiSync", image, "Izanami Journal Sync Companion", menu)
                    threading.Thread(target=self.tray_icon.run, daemon=True).start()

                self.root.withdraw()
                return
            except Exception as e:
                print(f"Failed to start system tray icon: {e}")
                if self.tray_icon:
                    try:
                        self.tray_icon.stop()
                    except Exception:
                        pass
                    self.tray_icon = None

        self.root.deiconify()
        self.root.iconify()

    def restore_from_tray(self, icon=None, item=None):
        if self.tray_icon:
            try:
                self.tray_icon.stop()
            except Exception:
                pass
            self.tray_icon = None
        self.root.after(0, lambda: (self.root.deiconify(), self.root.lift(), self.root.focus_force()))

    def on_window_close(self):
        self.exit_app()

    def exit_app(self, icon=None, item=None):
        if self.tray_icon:
            try:
                self.tray_icon.stop()
            except Exception:
                pass
        self.root.quit()
        self.root.destroy()
        sys.exit(0)


if __name__ == "__main__":
    root = tk.Tk()
    app = IzanamiSyncApp(root)
    root.mainloop()

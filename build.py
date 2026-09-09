import os
import sys
import subprocess
import re
import zipfile
from pathlib import Path
from versionfile_generator import versionfile_generator

versionfile_generator()

preferred_python = Path(".venv64") / "Scripts" / "python.exe"
python_executable = str(preferred_python if preferred_python.exists() else Path(sys.executable))

subprocess.run(
    [
        python_executable,
        "-c",
        "import PySide6, openpyxl, pdfplumber",
    ],
    check=True,
)

hidden_imports = [
    "openpyxl",
    "gspread",
    "pdfplumber",
    "pandas",
    "firebirdsql",
    "passlib",
]

data_files = [
    "data;data",
    "mapping.json;.",
    "icone.ico;.",
    "pdf_icon.png;.",
]

args = [
    python_executable,
    "-m",
    "PyInstaller",
    "--onedir",
    "--noconfirm",
    "--noconsole",
    "--icon=icone.ico",
    "--name",
    "Relatorio de Clientes",
    "--version-file",
    "version.txt",
    "--collect-all",
    "PySide6",
]

for module in hidden_imports:
    args.extend(["--hidden-import", module])

for item in data_files:
    args.extend(["--add-data", item])

args.append("main.py")

subprocess.run(args, check=True)

with open("global_vars.py", "r", encoding="utf-8") as f:
    match = re.search(r'APP_VERSION\s*=\s*"([^"]+)"', f.read())
    if not match:
        raise RuntimeError("APP_VERSION não encontrado em global_vars.py")
    app_version = match.group(1)

dist_dir = Path("dist") / "Relatorio de Clientes"
zip_path = Path("dist") / f"RelatorioClientes-{app_version}.zip"
if dist_dir.exists():
    with zipfile.ZipFile(zip_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for file_path in dist_dir.rglob("*"):
            if file_path.is_file():
                zf.write(file_path, file_path.relative_to(dist_dir))

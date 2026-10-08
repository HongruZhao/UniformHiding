#!/usr/bin/env python3
"""Current source-integrity check; does not run Lean or prove a theorem."""
from pathlib import Path
import subprocess
import sys
root = Path(__file__).resolve().parents[1]
raise SystemExit(subprocess.call([sys.executable, str(root / 'verify_final.py'), '--sources-only'], cwd=root))

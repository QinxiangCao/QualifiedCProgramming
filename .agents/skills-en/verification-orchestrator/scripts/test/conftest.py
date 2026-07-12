from __future__ import annotations

import sys
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
VC_PROVING = SCRIPT_DIR.parents[1] / "vc-proving" / "scripts"
for path in (SCRIPT_DIR, VC_PROVING):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

#!/usr/bin/env python3
"""Check the canonical core extraction against the exact reviewed Git baseline."""

from pathlib import Path
import hashlib
import subprocess


ROOT = Path(__file__).resolve().parents[2]
BASE = "c0231e0fd64d9eee7f7bb798042d9966276e4cd6"
RELATIVE = "proof/PscVerif/PscVerif/StrictSystem.lean"
baseline = subprocess.check_output(["git", "show", BASE + ":" + RELATIVE], cwd=ROOT)
core = (ROOT / "proof/PscVerif/PscVerif/StrictSystemCore.lean").read_bytes()
remaining = baseline
blocks = [
    (b"/-! ### Strict systems -/", 14335,
     "64299f2beca3186ca384ccb6ae03e513a3bdc4b06b52d5de8757890652c6f651"),
    (b"/-! ### (c) Decide-checked strong-coincidence witnesses -/", 4934,
     "017e92d1dffb197b7e3c6732a3f04582aaf6a6f5932e14d7e298b8922c25c03b"),
]
for marker, length, expected in blocks:
    start = baseline.index(marker)
    original = baseline[start:start + length]
    start = core.index(marker)
    extracted = core[start:start + length]
    assert original == extracted
    assert hashlib.sha256(original).hexdigest() == expected
    assert remaining.count(original) == 1
    remaining = remaining.replace(original, b"", 1)
    print("PSC_CORE_BLOCK_IDENTICAL", length, expected, sep="\t")
remaining = remaining.replace(b"import PscVerif.Descendants\n",
                              b"import PscVerif.StrictSystemCore\n", 1)
assert (ROOT / RELATIVE).read_bytes() == remaining
print("PSC_CORE_REMAINDER_IDENTICAL\tonly-import-replacement")
print("PSC_CORE_EXTRACTION_VERIFIED\t397-lines\tunchanged-declarations-and-proof-bodies")

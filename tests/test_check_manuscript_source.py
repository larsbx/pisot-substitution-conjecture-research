"""The manuscript-source guard fails closed on missing, mangled, and truncated files."""
import re
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "check_manuscript_source.py"
SRC = ROOT / "manuscripts"


def run(directory: Path) -> tuple[int, str]:
    r = subprocess.run([sys.executable, str(SCRIPT), str(directory)], capture_output=True, text=True)
    return r.returncode, r.stdout


@pytest.fixture
def copy(tmp_path):
    d = tmp_path / "manuscripts"
    d.mkdir()
    for name in (SRC / "MANIFEST").read_text().split():
        shutil.copy(SRC / name, d / name)
    shutil.copy(SRC / "MANIFEST", d / "MANIFEST")
    return d


def test_repository_manuscripts_pass():
    code, out = run(SRC)
    assert code == 0 and out.startswith("OK"), out


def test_intact_copy_passes(copy):
    assert run(copy)[0] == 0


def test_mangled_tex_fails(copy):
    tex = next(copy.glob("*.tex"))
    tex.write_bytes(bytes(b ^ 0xA5 for b in tex.read_bytes()))
    code, out = run(copy)
    assert code == 1 and ("not valid UTF-8" in out or "\\documentclass" in out)


def test_truncated_tex_fails(copy):
    tex = next(copy.glob("*.tex"))
    tex.write_text("\\documentclass{article}\n\\begin{document}\nx\n\\end{document}\n")
    code, out = run(copy)
    assert code == 1 and "lines" in out


def test_pdf_truncated_after_header_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(pdf.read_bytes()[:5])
    code, out = run(copy)
    assert code == 1 and "%%EOF" in out


def test_pdf_with_bad_startxref_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = pdf.read_bytes()
    pdf.write_bytes(raw[: raw.rfind(b"startxref")] + b"startxref\n999999999\n%%EOF\n")
    code, out = run(copy)
    assert code == 1 and "startxref" in out


def test_pdf_startxref_at_ordinary_object_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = pdf.read_bytes()
    ordinary = next(m for m in re.finditer(rb"\d+\s+\d+\s+obj\b", raw) if b"/XRef" not in raw[m.start(): m.start() + 4096])
    pdf.write_bytes(raw[: raw.rfind(b"startxref")] + b"startxref\n%d\n%%%%EOF\n" % ordinary.start())
    code, out = run(copy)
    assert code == 1 and "not a cross-reference stream" in out


def test_pdf_last_trailer_is_the_one_checked(copy):
    # an incremental update whose newest trailer is corrupt, with the old valid trailer still in the window
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(pdf.read_bytes() + b"\nstartxref\n999999999\n%%EOF\n")
    code, out = run(copy)
    assert code == 1 and "beyond end of file" in out


def test_pdf_xref_object_without_stream_body_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(
        b"%PDF-1.5\n1 0 obj\n<< /Type /XRef /Size 2 /W [1 2 1] /Root 1 0 R /Length 4 >>\nendobj\nstartxref\n9\n%%EOF\n"
    )
    code, out = run(copy)
    assert code == 1 and "no stream body" in out


MINIMAL_CLASSIC = (
    b"%PDF-1.4\n1 0 obj\n<< /Type /Catalog >>\nendobj\n"
    b"xref\n0 2\n0000000000 65535 f \n0000000009 00000 n \n"
    b"trailer\n<< /Size 2 /Root 1 0 R >>\nstartxref\n45\n%%EOF\n"
)


def test_minimal_classic_table_passes(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(MINIMAL_CLASSIC)
    assert MINIMAL_CLASSIC[45:49] == b"xref" and MINIMAL_CLASSIC[9:16] == b"1 0 obj"
    code, out = run(copy)
    assert code == 0, out


def test_entryless_classic_table_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(b"%PDF-1.4\nxref\ntrailer\nstartxref\n9\n%%EOF\n")
    code, out = run(copy)
    assert code == 1 and "no entries" in out


def test_empty_xref_stream_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(
        b"%PDF-1.5\n1 0 obj\n<< /Type /XRef /Size 2 /W [1 2 1] /Root 1 0 R /Length 0 >>\nstream\nendstream\nendobj\nstartxref\n9\n%%EOF\n"
    )
    code, out = run(copy)
    assert code == 1 and "not a positive multiple" in out


def test_corrupted_flate_payload_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = bytearray(pdf.read_bytes())
    i = raw.rfind(b"stream\n", 0, raw.rfind(b"endstream")) + len(b"stream\n") + 40
    raw[i] ^= 0xFF
    pdf.write_bytes(bytes(raw))
    code, out = run(copy)
    assert code == 1 and ("does not inflate" in out or "not a positive multiple" in out)


def test_missing_required_file_fails(copy):
    next(copy.glob("*.pdf")).unlink()
    code, out = run(copy)
    assert code == 1 and "required by the manifest but missing" in out


def test_empty_directory_fails(tmp_path):
    code, out = run(tmp_path)
    assert code == 1 and "missing manifest" in out

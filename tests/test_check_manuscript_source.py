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



def classic_pdf(objs=None, extra_trailer=b"", edit=None):
    """A complete classic-table PDF (catalog, page tree, one page); `edit` mutates the bytes."""
    objs = objs or [
        b"<< /Type /Catalog /Pages 2 0 R >>",
        b"<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        b"<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>",
    ]
    out, offs = b"%PDF-1.4\n", []
    for i, body in enumerate(objs, 1):
        offs.append(len(out))
        out += b"%d 0 obj\n%s\nendobj\n" % (i, body)
    xref = len(out)
    out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
    out += b"".join(b"%010d 00000 n \n" % o for o in offs)
    out += b"trailer\n<< /Size %d /Root 1 0 R %s>>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, extra_trailer, xref)
    return edit(out) if edit else out


def xref_pdf(rows=None, dict_extra=b"", predictor=False, compress=True):
    """A complete PDF whose cross-reference is a stream (catalog, one-page tree; page is object 4)."""
    import zlib

    out = b"%PDF-1.5\n"
    o1 = len(out)
    out += b"1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n"
    o2 = len(out)
    out += b"2 0 obj\n<< /Type /Pages /Kids [4 0 R] /Count 1 >>\nendobj\n"
    o4 = len(out)
    out += b"4 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>\nendobj\n"
    o3 = len(out)
    table = [b"\x00\x00\x00\x00"] + [b"\x01" + o.to_bytes(2, "big") + b"\x00" for o in (o1, o2, o3, o4)]
    if rows is not None:
        table = rows(table, o1, o2, o3)
    if predictor:
        prev, enc = bytes(4), b""
        for r in table:
            enc += b"\x02" + bytes((a - b) & 0xFF for a, b in zip(r, prev))
            prev = r
        body = zlib.compress(enc)
    else:
        body = zlib.compress(b"".join(table)) if compress else b"".join(table)
    flt = b"/Filter /FlateDecode " if (compress or predictor) else b""
    out += b"3 0 obj\n<< /Type /XRef /Size 5 /W [1 2 1] /Root 1 0 R " + flt + dict_extra + b"/Length %d >>\nstream\n" % len(body)
    out += body + b"\nendstream\nendobj\nstartxref\n%d\n%%%%EOF\n" % o3
    return out


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
    pdf.write_bytes(classic_pdf())
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


def xref_stream_pdf(dictionary: bytes, body: bytes) -> bytes:
    return b"%PDF-1.5\n1 0 obj\n" + dictionary + b"\nstream\n" + body + b"\nendstream\nendobj\nstartxref\n9\n%%EOF\n"


def test_indirect_length_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 1 /W [1 2 1] /Root 1 0 R /Length 4 0 R >>", b"\x01\x00\x09\x00"))
    code, out = run(copy)
    assert code == 1 and "indirect reference" in out


def test_row_count_must_match_size(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 100 /W [1 2 1] /Root 1 0 R /Length 4 >>", b"\x01\x00\x09\x00"))
    code, out = run(copy)
    assert code == 1 and "declares 100" in out


def test_row_count_must_match_index(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 5 /Index [0 3] /W [1 2 1] /Root 1 0 R /Length 4 >>", b"\x01\x00\x09\x00"))
    code, out = run(copy)
    assert code == 1 and "declares 3" in out


def test_uncompressed_xref_stream_passes(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_pdf(compress=False))
    code, out = run(copy)
    assert code == 0, out


def test_filter_array_form_is_inflated(copy):
    import zlib

    pdf = next(copy.glob("*.pdf"))
    body = zlib.compress(b"\x01\x00\x09\x00")
    pdf.write_bytes(xref_pdf().replace(b"/Filter /FlateDecode", b"/Filter [/FlateDecode]"))
    code, out = run(copy)
    assert code == 0, out
    bad = xref_stream_pdf(b"<< /Type /XRef /Size 1 /W [1 2 1] /Root 1 0 R /Filter [/LZWDecode] /Length %d >>" % len(body), body)
    pdf.write_bytes(bad)
    code, out = run(copy)
    assert code == 1 and "unsupported" in out


def test_truncated_after_endstream_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = xref_stream_pdf(b"<< /Type /XRef /Size 1 /W [1 2 1] /Root 1 0 R /Length 4 >>", b"\x01\x00\x09\x00")
    pdf.write_bytes(raw.replace(b"\nendobj\n", b"\n"))
    code, out = run(copy)
    assert code == 1 and "endobj" in out


def test_index_ranges_must_fit_size(copy):
    pdf = next(copy.glob("*.pdf"))
    for index in (b"[999 1]", b"[0 1 2]", b"[0 0]"):
        pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 1 /Index " + index + b" /W [1 2 1] /Root 1 0 R /Length 4 >>", b"\x01\x00\x09\x00"))
        code, out = run(copy)
        assert code == 1 and "/Index" in out, (index, out)


def test_w_needs_three_fields(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 1 /W [4] /Root 1 0 R /Length 4 >>", b"\x01\x00\x09\x00"))
    code, out = run(copy)
    assert code == 1 and "exactly three fields" in out


def test_classic_entry_must_point_at_its_object(copy):
    pdf = next(copy.glob("*.pdf"))
    for bad in (b"0000000008 00000 n", b"9999999999 00000 n", b"0000000009 00001 n"):
        pdf.write_bytes(MINIMAL_CLASSIC.replace(b"0000000009 00000 n", bad))
        code, out = run(copy)
        assert code == 1 and "does not point at" in out, (bad, out)


def test_classic_subsection_must_fit_size(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(MINIMAL_CLASSIC.replace(b"/Size 2", b"/Size 1"))
    code, out = run(copy)
    assert code == 1 and "exceeds the trailer /Size" in out


def test_xref_stream_entries_are_dereferenced(copy):
    pdf = next(copy.glob("*.pdf"))
    head = b"<< /Type /XRef /Size 2 /Index [1 1] /W [1 2 1] /Root 1 0 R /Length 4 >>"
    for row, marker in ((b"\x01\xff\xff\x00", "does not point at"), (b"\x01\x00\x08\x00", "does not point at"),
                        (b"\x07\x00\x09\x00", "unknown type"), (b"\x02\x00\x09\x00", "beyond /Size")):
        pdf.write_bytes(xref_stream_pdf(head, row))
        code, out = run(copy)
        assert code == 1 and marker in out, (row, out)


def test_predicted_xref_stream_is_unfiltered(copy):
    import zlib

    pdf = next(copy.glob("*.pdf"))
    # PNG Up predictor: one row, filter byte 2, row bytes are deltas against a zero previous row
    pdf.write_bytes(xref_pdf(predictor=True, dict_extra=b"/DecodeParms << /Columns 4 /Predictor 12 >> "))
    code, out = run(copy)
    assert code == 0, out


def test_bogus_prev_chain_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(extra_trailer=b"/Prev 999999 "))
    code, out = run(copy)
    assert code == 1 and "offset 999999 beyond end of file" in out, out


def test_cyclic_prev_chain_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = classic_pdf(extra_trailer=b"/Prev 000000 ")
    xref = int(re.search(rb"startxref\n(\d+)", raw).group(1))
    pdf.write_bytes(raw.replace(b"/Prev 000000 ", b"/Prev %06d " % xref))
    code, out = run(copy)
    assert code == 1 and "revisits offset" in out, out


def test_incremental_update_extent_comes_from_prev_section(copy):
    # an update section rewriting only object 1; /Size 4 is justified by the original section
    pdf = next(copy.glob("*.pdf"))
    raw = classic_pdf()
    old_xref = int(re.search(rb"startxref\n(\d+)", raw).group(1))
    o1 = len(raw)
    raw += b"1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n"
    new_xref = len(raw)
    raw += b"xref\n1 1\n%010d 00000 n \ntrailer\n<< /Size 4 /Root 1 0 R /Prev %d >>\nstartxref\n%d\n%%%%EOF\n" % (o1, old_xref, new_xref)
    pdf.write_bytes(raw)
    code, out = run(copy)
    assert code == 0, out


def test_free_top_entry_passes_classic(copy):
    # objects 1-3 in use, object 4 free, /Size 5: the extent counts the free entry
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"xref\n0 4\n", b"xref\n0 5\n")
                                .replace(b"trailer", b"0000000000 00000 f \ntrailer").replace(b"/Size 4 ", b"/Size 5 ")))
    code, out = run(copy)
    assert code == 0, out


def test_free_top_entry_passes_xref_stream(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_pdf(rows=lambda t, o1, o2, o3: [*t, b"\x00\x00\x00\x00"]).replace(b"/Size 5 ", b"/Size 6 "))
    code, out = run(copy)
    assert code == 0, out


def test_type2_entry_to_non_object_stream_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    # object 1 declared as member 0 of "object stream" 2, which is the page tree, not an object stream
    pdf.write_bytes(xref_pdf(rows=lambda t, o1, o2, o3: [t[0], b"\x02\x00\x02\x00", *t[2:]]))
    code, out = run(copy)
    assert code == 1 and "full parse failed" in out


def test_predictor_parameters_are_validated(copy):
    pdf = next(copy.glob("*.pdf"))
    for params in (b"/DecodeParms << /Columns 4 /Predictor 99 >> ", b"/DecodeParms << /Columns 999 /Predictor 12 >> "):
        pdf.write_bytes(xref_pdf(predictor=True, dict_extra=params))
        code, out = run(copy)
        assert code == 1 and "full parse failed" in out, (params, out)


def test_missing_required_file_fails(copy):
    next(copy.glob("*.pdf")).unlink()
    code, out = run(copy)
    assert code == 1 and "required by the manifest but missing" in out


def test_empty_directory_fails(tmp_path):
    code, out = run(tmp_path)
    assert code == 1 and "missing manifest" in out


def test_inflated_classic_size_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    # /Size 99 keeps every subsection within bound, but the highest object number is 3
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"/Size 4 ", b"/Size 99 ")))
    code, out = run(copy)
    assert code == 1 and "highest object number 3" in out, out


def test_inflated_xref_stream_size_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    # /Index keeps the row count consistent while /Size overstates the object-number extent
    pdf.write_bytes(xref_pdf(dict_extra=b"/Index [0 5] ").replace(b"/Size 5 ", b"/Size 99 "))
    code, out = run(copy)
    assert code == 1 and "highest object number 4" in out, out


def test_corrupted_ordinary_stream_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    raw = bytearray(pdf.read_bytes())
    # the first content stream (a /Length-then-/Filter dictionary with no /Type); its offsets and
    # lengths are untouched, so only decoding the body can detect the flipped byte
    m = re.search(rb"\d+ 0 obj\n<<\n/Length \d+\s*\n/Filter /FlateDecode\n>>\nstream\n", bytes(raw))
    raw[m.end() + 40] ^= 0xFF
    pdf.write_bytes(bytes(raw))
    code, out = run(copy)
    assert code == 1 and "does not inflate" in out, out

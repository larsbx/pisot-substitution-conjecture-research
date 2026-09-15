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


def xref_pdf(rows=None, dict_extra=b"", predictor=False, compress=True, gen_bytes=1):
    """A complete PDF whose cross-reference is a stream (catalog, one-page tree; page is
    object 4), with ``/W [1 2 gen_bytes]``."""
    import zlib

    out = b"%PDF-1.5\n"
    o1 = len(out)
    out += b"1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n"
    o2 = len(out)
    out += b"2 0 obj\n<< /Type /Pages /Kids [4 0 R] /Count 1 >>\nendobj\n"
    o4 = len(out)
    out += b"4 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>\nendobj\n"
    o3 = len(out)
    # object 0: free, next free 0, generation column saturated (as pdfTeX writes it in one byte)
    table = [b"\x00\x00\x00" + b"\xff" * gen_bytes] + [b"\x01" + o.to_bytes(2, "big") + bytes(gen_bytes) for o in (o1, o2, o3, o4)]
    if rows is not None:
        table = rows(table, o1, o2, o3)
    if predictor:
        prev, enc = bytes(3 + gen_bytes), b""
        for r in table:
            enc += b"\x02" + bytes((a - b) & 0xFF for a, b in zip(r, prev))
            prev = r
        body = zlib.compress(enc)
    else:
        body = zlib.compress(b"".join(table)) if compress else b"".join(table)
    flt = b"/Filter /FlateDecode " if (compress or predictor) else b""
    out += b"3 0 obj\n<< /Type /XRef /Size 5 /W [1 2 %d] /Root 1 0 R " % gen_bytes + flt + dict_extra + b"/Length %d >>\nstream\n" % len(body)
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


def classic_with_free_4(head=b"0000000004 65535 f ", tail=b"0000000000 00000 f "):
    """objects 1-3 in use, object 4 free and linked from object 0, /Size 5."""
    return classic_pdf(edit=lambda b: b.replace(b"xref\n0 4\n0000000000 65535 f ", b"xref\n0 5\n" + head)
                       .replace(b"trailer", tail + b"\ntrailer").replace(b"/Size 4 ", b"/Size 5 "))


def test_free_top_entry_passes_classic(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_with_free_4())
    code, out = run(copy)
    assert code == 0, out


def test_free_top_entry_passes_xref_stream(copy):
    pdf = next(copy.glob("*.pdf"))
    rows = lambda t, o1, o2, o3: [b"\x00\x00\x05\xff", *t[1:], b"\x00\x00\x00\x00"]
    pdf.write_bytes(xref_pdf(rows=rows).replace(b"/Size 5 ", b"/Size 6 "))
    code, out = run(copy)
    assert code == 0, out


def test_free_entry_pointer_must_be_below_size(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"0000000000 65535 f", b"9999999999 65535 f")))
    code, out = run(copy)
    assert code == 1 and "beyond /Size" in out, out
    pdf.write_bytes(xref_pdf(rows=lambda t, o1, o2, o3: [b"\x00\x00\x63\xff", *t[1:]]))
    code, out = run(copy)
    assert code == 1 and "beyond /Size" in out, out


def test_object_zero_must_be_free_with_generation_65535(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"0000000000 65535 f", b"0000000000 00000 f")))
    code, out = run(copy)
    assert code == 1 and "not 65535" in out, out


def test_stream_generation_is_taken_literally(copy):
    pdf = next(copy.glob("*.pdf"))
    # a two-byte column holding exactly 65535 passes; a three-byte column holding 65536 fails
    pdf.write_bytes(xref_pdf(gen_bytes=2))
    code, out = run(copy)
    assert code == 0, out
    pdf.write_bytes(xref_pdf(gen_bytes=3, rows=lambda t, o1, o2, o3: [b"\x00\x00\x00\x01\x00\x00", *t[1:]]))
    code, out = run(copy)
    assert code == 1 and "generation 65536 > 65535" in out, out


def test_unlinked_stream_free_entry_passes(copy):
    # object 5 free with next-free field 0 and not linked from object 0: allowed in a stream
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(xref_pdf(rows=lambda t, o1, o2, o3: [*t, b"\x00\x00\x00\x00"]).replace(b"/Size 5 ", b"/Size 6 "))
    code, out = run(copy)
    assert code == 0, out
    # but an unlinked free entry pointing at object 3 dangles
    pdf.write_bytes(xref_pdf(rows=lambda t, o1, o2, o3: [*t, b"\x00\x00\x03\x00"]).replace(b"/Size 5 ", b"/Size 6 "))
    code, out = run(copy)
    assert code == 1 and "not on the free list" in out, out


def test_free_entries_must_form_the_free_list(copy):
    pdf = next(copy.glob("*.pdf"))
    # object 4 free but object 0 still points at 0: object 4 is off the list
    pdf.write_bytes(classic_with_free_4(head=b"0000000000 65535 f "))
    code, out = run(copy)
    assert code == 1 and "not on the free list" in out, out
    # object 0 points at the in-use object 2
    pdf.write_bytes(classic_with_free_4(head=b"0000000002 65535 f "))
    code, out = run(copy)
    assert code == 1 and "not an unvisited free entry" in out, out


def test_classic_free_list_is_judged_at_its_own_section(copy):
    # a newer cross-reference stream replaces object 0 with an unlinked row and inherits the
    # classic section's free object 4 through /Prev; the classic list was valid at its section
    pdf = next(copy.glob("*.pdf"))
    raw = classic_with_free_4()
    old_xref = int(re.search(rb"startxref\n(\d+)", raw).group(1))
    o5 = len(raw)
    rows = b"\x00\x00\x00\xff" + b"\x01" + o5.to_bytes(2, "big") + b"\x00"
    raw += (b"5 0 obj\n<< /Type /XRef /Size 6 /Index [0 1 5 1] /W [1 2 1] /Root 1 0 R /Prev %d /Length %d >>\nstream\n"
            % (old_xref, len(rows)) + rows + b"\nendstream\nendobj\nstartxref\n%d\n%%%%EOF\n" % o5)
    pdf.write_bytes(raw)
    code, out = run(copy)
    assert code == 0, out


def test_huge_declared_row_count_fails_fast(copy):
    pdf = next(copy.glob("*.pdf"))
    for dictionary in (b"<< /Type /XRef /Size 1000000000 /W [1 2 1] /Root 1 0 R /Length 4 >>",
                       b"<< /Type /XRef /Size 1000000001 /Index [0 1000000000] /W [1 2 1] /Root 1 0 R /Length 4 >>"):
        pdf.write_bytes(xref_stream_pdf(dictionary, b"\x01\x00\x09\x00"))
        code, out = run(copy)
        assert code == 1 and "declares 1000000000" in out, out


def test_in_use_generation_is_bounded(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"0000000009 00000 n", b"0000000009 65536 n")))
    code, out = run(copy)
    assert code == 1 and "generation 65536 > 65535" in out, out
    row1 = lambda t, o1, o2, o3: [b"\x00\x00\x00\x00\xff\xff", b"\x01" + o1.to_bytes(2, "big") + b"\x01\x00\x00", *t[2:]]
    pdf.write_bytes(xref_pdf(gen_bytes=3, rows=row1))
    code, out = run(copy)
    assert code == 1 and "generation 65536 > 65535" in out, out


def test_matching_compression_bomb_hits_the_row_ceiling(copy):
    import zlib
    pdf = next(copy.glob("*.pdf"))
    # two million all-zero rows agree with the declaration and compress to a few kilobytes
    body = zlib.compress(bytes(4 * 2_000_000))
    pdf.write_bytes(xref_stream_pdf(b"<< /Type /XRef /Size 2000000 /W [1 2 1] /Root 1 0 R /Filter /FlateDecode /Length %d >>" % len(body), body))
    code, out = run(copy)
    assert code == 1 and "above the ceiling" in out, out


def hybrid_pdf(free5=b"\x00\x00\x00\x00"):
    """A classic table for objects 0-3 whose trailer names a companion /XRefStm stream
    (object 4) describing itself and a free object 5; /Size 6."""
    raw = classic_pdf()
    o4 = len(raw)
    rows = b"\x00\x00\x00\xff" + b"\x01" + o4.to_bytes(2, "big") + b"\x00" + free5
    raw += (b"4 0 obj\n<< /Type /XRef /Size 6 /Index [0 1 4 2] /W [1 2 1] /Root 1 0 R /Length %d >>\nstream\n" % len(rows)
            + rows + b"\nendstream\nendobj\n")
    xref = len(raw)
    raw += (b"xref\n0 4\n0000000000 65535 f \n" + b"".join(b"%010d 00000 n \n" % int(m) for m in re.findall(rb"(\d{10}) 00000 n", classic_pdf()))
            + b"trailer\n<< /Size 6 /Root 1 0 R /XRefStm %d >>\nstartxref\n%d\n%%%%EOF\n" % (o4, xref))
    return raw


def test_hybrid_companion_stream_is_walked(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(hybrid_pdf())
    code, out = run(copy)
    assert code == 0, out
    # the companion's free row for object 5 points beyond /Size
    pdf.write_bytes(hybrid_pdf(free5=b"\x00\x00\x63\x00"))
    code, out = run(copy)
    assert code == 1 and "/XRefStm" in out and "beyond /Size" in out, out


def test_size_is_checked_at_every_section(copy):
    # the original section covers objects 0-3 but declares /Size 5; a later update adds object 4
    pdf = next(copy.glob("*.pdf"))
    raw = classic_pdf(edit=lambda b: b.replace(b"/Size 4 ", b"/Size 5 "))
    old_xref = int(re.search(rb"startxref\n(\d+)", raw).group(1))
    o4 = len(raw)
    raw += b"4 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] >>\nendobj\n"
    new_xref = len(raw)
    raw += b"xref\n4 1\n%010d 00000 n \ntrailer\n<< /Size 5 /Root 1 0 R /Prev %d >>\nstartxref\n%d\n%%%%EOF\n" % (o4, old_xref, new_xref)
    pdf.write_bytes(raw)
    code, out = run(copy)
    assert code == 1 and "/Size 5 is not one more than the highest object number 3" in out, out


def test_zero_count_subsection_fails(copy):
    pdf = next(copy.glob("*.pdf"))
    pdf.write_bytes(classic_pdf(edit=lambda b: b.replace(b"trailer", b"9999 0\ntrailer").replace(b"/Size 4 ", b"/Size 9999 ")))
    code, out = run(copy)
    assert code == 1 and "empty xref subsection" in out, out


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

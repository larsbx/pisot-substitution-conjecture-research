"""Theorem T_C pieces: the onset diagonals certify the frozen sets, a lower
diagonal certifies a different set, a gap line through a sign change refuses,
and malformed pieces refuse. The full cover is replayed by the driver
(`class_c_tail_certificate.mojo theorem +-1`) in its own workflow."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_gap_profile import c_block, frozen_onset, rows_of
from psc.class_c_tail_certificate import CONE, DIAGONAL, GAP, Cover, Piece, certify_piece, rows


def refuses(eps: Int, c: Int, d0: Int, m0: Int, kind: Int) -> Bool:
    try:
        _ = Piece(eps, c, d0, m0, kind)
    except:
        return True
    return False


def undecided(p: Piece) raises -> Bool:
    try:
        _ = certify_piece(p)
    except e:
        return String(e).startswith("a sign")
    return False


def main() raises:
    for eps in [1, -1]:
        var frozen = rows_of(c_block(8, eps, frozen_onset(8, eps)))
        # The onset diagonal n = 4d + c, every d >= 8, is the frozen set.
        var g = certify_piece(Piece(eps, frozen_onset(0, eps), 8, 0, DIAGONAL))
        assert_equal(g.size(), 196 if eps == 1 else 214)
        assert_true(rows(g) == frozen)
    # Negative control: one diagonal lower certifies just as uniformly, with another set.
    var below = certify_piece(Piece(1, -1, 8, 0, DIAGONAL))
    assert_equal(below.size(), 198)
    assert_true(rows(below) != rows_of(c_block(8, 1, 32)))
    assert_true(rows(below) == rows_of(c_block(9, 1, 35)))
    # Gap 6 from the onset changes an intermediate sign between m = 0 and m = 1: refused, not decided.
    assert_true(undecided(Piece(1, 0, 6, 0, GAP)))
    # The cover's agreement check refuses a second label set.
    var out = Cover()
    out.agree("R 0 0 0 0 0 0\n", "first")
    var raised = False
    try:
        out.agree("R 0 0 1 0 0 0\n", "second")
    except:
        raised = True
    assert_true(raised)
    # Malformed pieces: sign, gap floor, kind, normal form.
    assert_true(refuses(0, 0, 6, 0, CONE))
    assert_true(refuses(1, 0, 1, 0, CONE))
    assert_true(refuses(1, 0, 6, 0, 3))
    assert_true(refuses(-1, -18, 6, 0, DIAGONAL))
    require_contract("class C (n+d,n,n-d+eps) tail pieces on the symbolic cone engine: the onset diagonals n=4d (plus) and n=4d+4 (minus) certify PIP, hitting and constant offsets for every d>=8 with exactly the frozen label sets (196/214); the diagonal n=4d-1 certifies a different 198-label set; gap 6 from the onset refuses on an undecided sign; the cover refuses a second label set; malformed pieces refuse")

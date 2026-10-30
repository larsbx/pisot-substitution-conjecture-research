"""Theorem T_C2 pieces in the strip frame (k, j) = (n - 3d, 4d - n): a diagonal
certifies and matches the exact graph, the middle sector's edge line keeps the
280-label set, malformed strip pieces refuse, and a several-set cover collects
instead of raising. The full covers are replayed by the driver
(`class_c_tail_certificate.mojo strip +-1`) in their own workflow job."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_c_gap_profile import c_block, rows_of
from psc.class_c_tail_certificate import CONE, DIAGONAL, GAP, STRIP, Cover, Piece, certify_piece, rows


def refuses(eps: Int, c: Int, k0: Int, j0: Int, kind: Int) -> Bool:
    try:
        _ = Piece(eps, c, k0, j0, kind, STRIP)
    except:
        return True
    return False


def main() raises:
    # The diagonal j = 4d - n = 5 (plus), every k = n - 3d >= 2: 196 labels, the
    # exact graph's at (k, j) = (4, 5), i.e. d = 9, n = 31.
    var diag = certify_piece(Piece(1, 0, 2, 5, DIAGONAL, STRIP))
    assert_equal(diag.size(), 196)
    assert_true(rows(diag) == rows_of(c_block(9, 1, 31)))
    # The line n = 3d (k = 0), every j >= 14 (plus): the middle sector's 280 labels,
    # the exact graph's at (0, 20), i.e. d = 20, n = 60.
    var edge = certify_piece(Piece(1, 0, 0, 14, GAP, STRIP))
    assert_equal(edge.size(), 280)
    assert_true(rows(edge) == rows_of(c_block(20, 1, 60)))
    # A several-set cover records a second set instead of raising.
    var many = Cover(False, False)
    many.agree("R 0 0 0 0 0 0\n", "first")
    many.agree("R 0 0 1 0 0 0\n", "second")
    many.agree("R 0 0 0 0 0 0\n", "third")
    assert_equal(len(many.sets), 2)
    # Malformed strip pieces: an offset c, a corner with d = k + j < 1, |j0| > 64, a sign.
    assert_true(refuses(1, 1, 0, 1, CONE))
    assert_true(refuses(1, 0, 0, 0, CONE))
    assert_true(refuses(1, 0, 0, 65, CONE))
    assert_true(refuses(0, 0, 0, 1, CONE))
    require_contract("class C (n+d,n,n-d+eps) T_C2 strip frame (k, j) = (n-3d, 4d-n) on the symbolic cone engine: the diagonal j=5 certifies for every k>=2 with 196 labels equal to the exact graph at d=9, n=31; the line n=3d certifies for every j>=14 with the middle sector's 280 labels equal to the exact graph at d=20, n=60; a several-set cover collects distinct sets; malformed strip pieces refuse")

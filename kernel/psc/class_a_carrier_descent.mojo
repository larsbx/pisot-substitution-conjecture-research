"""Uniform offset-zero descent on the typed class-A carrier for every n>=n0 (#139).

A *piece* is an affine sub-interval `j in [lo(n), hi(n)]` of one carrier row
together with an integer potential `X(n,j) = a n + b j + c`. The pieces of a
row partition its index range. A piece whose only member is an offset-zero
label (`w = 0`) is a *target*; every other piece is covered by *descent rows*
`(piece, [lo,hi], top part, bottom part, y', child piece)`, each naming one
symbolic ordered child occurrence of every member.

For every integer `n>=n0` the verifier proves, row by row:
  * the pieces partition each carrier row and `X>=0` on every piece;
  * the descent rows of each non-target piece partition it;
  * for every descent row and every member `j`: the named child occurrence is
    realizable (its run positions exist), is a strict overlap (exact Perron
    signs at both ends of the affine range, the displacement being affine in
    `j`), is a label of the named child piece, and satisfies
    `X_child <= X_parent - 1`.
Since `X` is a non-negative integer that strictly decreases along the chosen
children, every carrier label reaches an offset-zero label after at most
`X` inflations. Combined with `psc.class_a_carrier_closure` (the seed graph
lies in the carrier) this is boundary hitting on the whole class-A line
`x->xy^(n+1)x, c->cy^nx, y->xy^(n+1)c` for every `n>=n0`.

The tables live in `psc.class_a_descent_data`; they were synthesized from
exact finite graphs and are evidence only through this verifier. The sign
machinery is shared with the closure module and fails closed.
"""
from psc.class_a_carrier_closure import (
    AffH, Segment, a_add, a_le, a_sub, aff, displacement, scaled_length,
)
from psc.class_a_typed_carrier import template_rows
from psc.class_a_descent_data import piece_rows, descent_rows
from psc.class_a_run_index import member, labelled
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, interior_overlap
from psc.overlap_zipper import ordered_child_occurrences
from psc.vertex_coincidence import length_matrix, offset_vector
from finite_exact.rat_q import Q


def _nonneg(u: List[Int], n0: Int) -> Bool:
    """`u >= 0` for every integer `n >= n0`."""
    return a_le(aff(0, 0), u, n0) == 1


def _partition(parts: List[List[Int]], lo: List[Int], hi: List[Int], n0: Int, what: String) raises:
    """`parts` (each `[lo_a, lo_b, hi_a, hi_b]`, in order) tile `[lo, hi]` exactly,
    every part being non-empty or at most empty (`lo <= hi + 1`) on the ray."""
    if len(parts) == 0:
        raise Error(what + ": no parts")
    var cursor = lo.copy()
    for p in parts:
        var p_lo = aff(p[0], p[1])
        var p_hi = aff(p[2], p[3])
        if p_lo[0] != cursor[0] or p_lo[1] != cursor[1]:
            raise Error(what + ": parts do not tile the range")
        if a_le(p_lo, a_add(p_hi, aff(0, 1)), n0) != 1:
            raise Error(what + ": part has negative length for some n")
        cursor = a_add(p_hi, aff(0, 1))
    var end = a_add(hi, aff(0, 1))
    if cursor[0] != end[0] or cursor[1] != end[1]:
        raise Error(what + ": parts stop short of the range end")


def _potential(piece: List[Int], j: List[Int]) -> List[Int]:
    """`X(n, j) = X_n n + X_j j + X_c` at the affine index `j`, as an affine form in n."""
    return aff(piece[5] + piece[6] * j[0], piece[6] * j[1] + piece[7])


def is_target_piece(row: List[Int], piece: List[Int]) -> Bool:
    """The piece is the single offset-zero label `w = 0` of its row."""
    return (row[2] == 0 and row[3] == 0 and piece[1] == piece[3] and piece[2] == piece[4]
            and row[4] + piece[1] == 0 and row[5] + piece[2] == 0)


def certify_descent_rows(n0: Int, rows: List[List[Int]], pieces: List[List[Int]],
                         descents: List[List[Int]]) raises -> List[Int]:
    """Returns `[pieces, target pieces, descent rows, bound slope, bound constant]`:
    every carrier label reaches offset zero within `bound slope * n + bound constant`
    inflations for every integer `n >= n0`. Raises on any failed obligation."""
    if n0 < 4 or n0 > 64:
        raise Error("uniform descent floor must satisfy 4<=n0<=64")
    var q = Q(1, Int64(n0 + 1))
    # Pieces partition every row.
    var by_row = List[List[List[Int]]]()
    for _ in range(len(rows)):
        by_row.append(List[List[Int]]())
    for p in pieces:
        if len(p) != 8 or p[0] < 0 or p[0] >= len(rows):
            raise Error("malformed potential piece")
        by_row[p[0]].append([p[1], p[2], p[3], p[4]])
    for ri in range(len(rows)):
        var row = rows[ri].copy()
        _partition(by_row[ri], aff(0, 0), aff(row[6] - row[4], row[7] - row[5]), n0, "pieces of row " + String(ri))
    # Potentials are non-negative, and the uniform bound is collected.
    var bound_slope = 0
    var bound_at_n0 = 0
    var targets = 0
    for p in pieces:
        var lo = aff(p[1], p[2])
        var hi = aff(p[3], p[4])
        for j in [lo.copy(), hi.copy()]:
            var x = _potential(p, j)
            if not _nonneg(x, n0):
                raise Error("potential is negative on a piece")
            bound_slope = max(bound_slope, x[0])
            bound_at_n0 = max(bound_at_n0, x[0] * n0 + x[1])
        if is_target_piece(rows[p[0]], p):
            targets += 1
    # Descent rows partition every non-target piece.
    var by_piece = List[List[List[Int]]]()
    for _ in range(len(pieces)):
        by_piece.append(List[List[Int]]())
    for d in descents:
        if len(d) != 9 or d[0] < 0 or d[0] >= len(pieces) or d[8] < 0 or d[8] >= len(pieces):
            raise Error("malformed descent row")
        by_piece[d[0]].append([d[1], d[2], d[3], d[4]])
    for pi in range(len(pieces)):
        var p = pieces[pi].copy()
        if is_target_piece(rows[p[0]], p):
            if len(by_piece[pi]) != 0:
                raise Error("target piece carries descent rows")
            continue
        _partition(by_piece[pi], aff(p[1], p[2]), aff(p[3], p[4]), n0, "descents of piece " + String(pi))
    # Every descent row is a realizable strict child occurrence into its child
    # piece with strictly smaller potential.
    for d in descents:
        var parent = pieces[d[0]].copy()
        var child = pieces[d[8]].copy()
        var row = rows[parent[0]].copy()
        var crow = rows[child[0]].copy()
        var s_lo = aff(d[1], d[2])
        var s_hi = aff(d[3], d[4])
        var seg_top = Segment(row[0], d[5])
        var seg_bottom = Segment(row[1], d[6])
        var yp = d[7]
        var dx = seg_bottom.px - seg_top.px
        var dc = seg_bottom.pc - seg_top.pc
        var s2 = 2 * row[2] + dx + dc + yp
        if seg_top.child != crow[0] or seg_bottom.child != crow[1] or s2 != crow[2] or yp != crow[3]:
            raise Error("descent child type disagrees with the named child piece")
        var k_lo = aff(row[4], row[5])
        var k0 = a_add(k_lo, aff(0, row[2] + dx))          # child k' = k0 + j
        var shift = a_sub(k0, aff(crow[4], crow[5]))          # child j' = j + shift
        # Child label lies in the child piece for every j in [s_lo, s_hi].
        if not _nonneg(a_sub(a_add(s_lo, shift), aff(child[1], child[2])), n0):
            raise Error("descent child leaves its piece below")
        if not _nonneg(a_sub(aff(child[3], child[4]), a_add(s_hi, shift)), n0):
            raise Error("descent child leaves its piece above")
        # Realizable: y' - (k + n s + y) - j in [m_b - m_t range] for every member.
        var base = aff(row[4] + row[2], row[5] + row[3])
        var d_lo = a_sub(seg_bottom.m_lo, seg_top.m_hi)
        var d_hi = a_sub(seg_bottom.m_hi, seg_top.m_lo)
        if not _nonneg(a_sub(a_sub(a_sub(aff(0, yp), base), s_hi), d_lo), n0):
            raise Error("descent occurrence is not realizable (lower run bound)")
        if not _nonneg(a_sub(d_hi, a_sub(a_sub(aff(0, yp), base), s_lo)), n0):
            raise Error("descent occurrence is not realizable (upper run bound)")
        # Parent and child are strict overlaps at both ends of the affine range.
        for j in [s_lo.copy(), s_hi.copy()]:
            var t_parent = displacement(aff(0, row[2]), a_add(k_lo, j), aff(0, row[3]))
            if scaled_length(row[0]).sub(t_parent).sign(q) <= 0 or t_parent.add(scaled_length(row[1])).sign(q) <= 0:
                raise Error("descent source is not a strict overlap")
            var t_child = displacement(aff(0, s2), a_add(k0, j), aff(0, yp))
            if scaled_length(crow[0]).sub(t_child).sign(q) <= 0 or t_child.add(scaled_length(crow[1])).sign(q) <= 0:
                raise Error("descent child is not a strict overlap")
            # X_parent(j) - X_child(j + shift) - 1 >= 0.
            var drop = a_sub(a_sub(_potential(parent, j), _potential(child, a_add(j, shift))), aff(0, 1))
            if not _nonneg(drop, n0):
                raise Error("descent does not lower the potential")
    var bound_const = bound_at_n0 - bound_slope * n0
    print("CLASS_A_CARRIER_DESCENT n>=" + String(n0), "pieces", len(pieces), "targets", targets,
          "descent_rows", len(descents), "hit_depth_bound", String(bound_slope) + "n" + ("+" if bound_const >= 0 else "") + String(bound_const))
    return [len(pieces), targets, len(descents), bound_slope, bound_const]


def certify_descent(n0: Int = 8) raises -> List[Int]:
    return certify_descent_rows(n0, template_rows(), piece_rows(), descent_rows())


def replay_descent_finite(n: Int, rows: List[List[Int]], pieces: List[List[Int]],
                          descents: List[List[Int]]) raises -> List[Int]:
    """Differential control at one n in 4..24: every descent member's named
    child occurrence is an actual ordered child occurrence of the exact
    Perron-field engine, with the stated prefix segments and child label, and
    the potential drops there. Returns `[labels, targets, checked edges]`."""
    if n < 4 or n > 24:
        raise Error("finite descent replay permits 4<=n<=24")
    var tables = build_seed_overlap_tables_screened(member(n))
    var lm = length_matrix(tables)
    var labels = 0
    var targets = 0
    var edges = 0
    for pi in range(len(pieces)):
        var p = pieces[pi].copy()
        var row = rows[p[0]].copy()
        var lo = p[1] * n + p[2]
        var hi = p[3] * n + p[4]
        for j in range(lo, hi + 1):
            labels += 1
            var k = row[4] * n + row[5] + j
            var c = row[2] - k - row[3]
            var parent = labelled(tables, row[0], row[1], k, c, row[3])
            if not interior_overlap(tables, parent):
                raise Error("finite piece member is not a strict overlap")
            if is_target_piece(row, p):
                if not parent.shift.is_zero():
                    raise Error("target piece member has nonzero offset")
                targets += 1
                continue
            var found = 0
            for d in descents:
                if d[0] != pi or j < d[1] * n + d[2] or j > d[3] * n + d[4]:
                    continue
                found += 1
                var child = pieces[d[8]].copy()
                var crow = rows[child[0]].copy()
                var x_parent = p[5] * n + p[6] * j + p[7]
                var matched = False
                for occurrence in ordered_child_occurrences(tables, parent):
                    var ti = occurrence.top_index
                    var bi = occurrence.bottom_index
                    var run_t = len(tables.sigma[row[0]]) - 2
                    var run_b = len(tables.sigma[row[1]]) - 2
                    var pt = 0 if ti == 0 else (1 if ti <= run_t else 2)
                    var pb = 0 if bi == 0 else (1 if bi <= run_b else 2)
                    if pt != d[5] or pb != d[6]:
                        continue
                    var w = offset_vector(lm, occurrence.state.shift)
                    if occurrence.state.top != crow[0] or occurrence.state.bottom != crow[1] or w[2] != d[7]:
                        continue
                    var cj = w[0] - (crow[4] * n + crow[5])
                    if w[0] + w[1] + w[2] != crow[2] or cj < child[1] * n + child[2] or cj > child[3] * n + child[4]:
                        continue
                    var x_child = child[5] * n + child[6] * cj + child[7]
                    if x_child > x_parent - 1:
                        raise Error("finite descent member does not drop the potential")
                    matched = True
                if not matched:
                    raise Error("finite descent member has no matching exact child occurrence")
                edges += 1
            if found != 1:
                raise Error("finite non-target label is not covered by exactly one descent row")
    if labels != 40 * n + 115:
        raise Error("finite piece enumeration disagrees with the carrier cardinality")
    print("CLASS_A_DESCENT_FINITE", n, "labels", labels, "targets", targets, "checked_edges", edges)
    return [labels, targets, edges]

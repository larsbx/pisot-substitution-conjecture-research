"""Alternative gap-four ranks from PR #326, preserved beside main's #327 tables.

Same exact verifiers; independent integer tables and occurrences. The minus
r=0,1 bounds are l+4; the default registry retains #327's earlier plus r=3
floor. See docs/issue139-ac-integration-2026-10-23.md.
"""
from psc.class_a_line import ALine
from psc.class_a_carrier_closure import certify_closure_line, ray_floor
from psc.class_a_carrier_descent import certify_descent_line
from psc.class_a_ray_d4p_rank import (
    rows_r0 as d4p_rows_r0, rows_r1 as d4p_rows_r1, rows_r2 as d4p_rows_r2, rows_r3 as d4p_rows_r3,
    pieces_r0 as d4p_pieces_r0, pieces_r1 as d4p_pieces_r1, pieces_r2 as d4p_pieces_r2, pieces_r3 as d4p_pieces_r3,
    descents_r0 as d4p_descents_r0, descents_r1 as d4p_descents_r1, descents_r2 as d4p_descents_r2, descents_r3 as d4p_descents_r3,
)

from psc.class_a_ray_d4m_rank import (
    rows_r0 as d4m_rows_r0, rows_r1 as d4m_rows_r1, rows_r2 as d4m_rows_r2, rows_r3 as d4m_rows_r3,
    pieces_r0 as d4m_pieces_r0, pieces_r1 as d4m_pieces_r1, pieces_r2 as d4m_pieces_r2, pieces_r3 as d4m_pieces_r3,
    descents_r0 as d4m_descents_r0, descents_r1 as d4m_descents_r1, descents_r2 as d4m_descents_r2, descents_r3 as d4m_descents_r3,
)

def tabulated_rays() -> List[List[Int]]:
    """`[d, eps, r, floor n0, cardinality slope, cardinality constant]` per tabulated ray;
    `n0` is the least `n = r (mod d)` at which both certificates are accepted."""
    return List[List[Int]]([
        List[Int]([4, 1, 0, 24, 40, 88]),
        List[Int]([4, 1, 1, 21, 40, 90]),
        List[Int]([4, 1, 2, 22, 40, 88]),
        List[Int]([4, 1, 3, 19, 40, 92]),
        List[Int]([4, -1, 0, 24, 40, 75]),
        List[Int]([4, -1, 1, 25, 40, 145]),
        List[Int]([4, -1, 2, 22, 40, 129]),
        List[Int]([4, -1, 3, 23, 40, 125]),
    ])


def ray_tables(line: ALine) raises -> List[List[List[Int]]]:
    """`[rows, pieces, descents]` of a tabulated ray."""
    line.check()
    if line.d == 4 and line.eps == 1 and line.r == 0:
        return [d4p_rows_r0(), d4p_pieces_r0(), d4p_descents_r0()]
    if line.d == 4 and line.eps == 1 and line.r == 1:
        return [d4p_rows_r1(), d4p_pieces_r1(), d4p_descents_r1()]
    if line.d == 4 and line.eps == 1 and line.r == 2:
        return [d4p_rows_r2(), d4p_pieces_r2(), d4p_descents_r2()]
    if line.d == 4 and line.eps == 1 and line.r == 3:
        return [d4p_rows_r3(), d4p_pieces_r3(), d4p_descents_r3()]
    if line.d == 4 and line.eps == -1 and line.r == 0:
        return [d4m_rows_r0(), d4m_pieces_r0(), d4m_descents_r0()]
    if line.d == 4 and line.eps == -1 and line.r == 1:
        return [d4m_rows_r1(), d4m_pieces_r1(), d4m_descents_r1()]
    if line.d == 4 and line.eps == -1 and line.r == 2:
        return [d4m_rows_r2(), d4m_pieces_r2(), d4m_descents_r2()]
    if line.d == 4 and line.eps == -1 and line.r == 3:
        return [d4m_rows_r3(), d4m_pieces_r3(), d4m_descents_r3()]
    raise Error("no generated tables for line " + line.name())


def certify_ray(line: ALine, n0: Int) raises -> List[List[Int]]:
    var t = ray_tables(line)
    var closure = certify_closure_line(line, n0, t[0])
    var descent = certify_descent_line(line, n0, t[0], t[1], t[2])
    print("CLASS_A_RAY_BOUNDARY_HITTING n>=" + String(line.n_of(ray_floor(line, n0))), "line=" + line.name(),
          "closure=true descent=true universal_139=false")
    return [closure^, descent^]

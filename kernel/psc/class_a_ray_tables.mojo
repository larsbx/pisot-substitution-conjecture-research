"""Registry of the generated residue-ray tables and the per-ray certificate.

`certify_ray(line, n0)` proves, for every integer `n >= n0` with
`n = r (mod d)`, forward closure of the ray's typed carrier and the strict
descent of its affine potential, i.e. boundary hitting on that ray. A ray
without tables refuses. `RAY_FLOORS` records, per tabulated ray, the least
floor at which both certificates are accepted and the carrier cardinality
`a l + b`, which is checked independently against exact complete graphs.
Source note: docs/class-a-residue-rays-2026-10-22.md.
"""
from psc.class_a_line import ALine
from psc.class_a_carrier_closure import certify_closure_line, ray_floor
from psc.class_a_carrier_descent import certify_descent_line
from psc.class_a_ray_d2m import (
    rows_r0 as d2m_rows_r0, rows_r1 as d2m_rows_r1,
    pieces_r0 as d2m_pieces_r0, pieces_r1 as d2m_pieces_r1,
    descents_r0 as d2m_descents_r0, descents_r1 as d2m_descents_r1,
)
from psc.class_a_ray_d2p import (
    rows_r0 as d2p_rows_r0, rows_r1 as d2p_rows_r1,
    pieces_r0 as d2p_pieces_r0, pieces_r1 as d2p_pieces_r1,
    descents_r0 as d2p_descents_r0, descents_r1 as d2p_descents_r1,
)
from psc.class_a_ray_d4m import (
    rows_r0 as d4m_rows_r0, rows_r1 as d4m_rows_r1, rows_r2 as d4m_rows_r2, rows_r3 as d4m_rows_r3,
    pieces_r0 as d4m_pieces_r0, pieces_r1 as d4m_pieces_r1, pieces_r2 as d4m_pieces_r2, pieces_r3 as d4m_pieces_r3,
    descents_r0 as d4m_descents_r0, descents_r1 as d4m_descents_r1,
    descents_r2 as d4m_descents_r2, descents_r3 as d4m_descents_r3,
)
from psc.class_a_ray_d4p import (
    rows_r0 as d4p_rows_r0, rows_r1 as d4p_rows_r1, rows_r2 as d4p_rows_r2, rows_r3 as d4p_rows_r3,
    pieces_r0 as d4p_pieces_r0, pieces_r1 as d4p_pieces_r1, pieces_r2 as d4p_pieces_r2, pieces_r3 as d4p_pieces_r3,
    descents_r0 as d4p_descents_r0, descents_r1 as d4p_descents_r1,
    descents_r2 as d4p_descents_r2, descents_r3 as d4p_descents_r3,
)
from psc.class_a_ray_d3m import (
    rows_r0 as d3m_rows_r0, rows_r1 as d3m_rows_r1, rows_r2 as d3m_rows_r2, pieces_r0 as d3m_pieces_r0, pieces_r1 as d3m_pieces_r1, pieces_r2 as d3m_pieces_r2, descents_r0 as d3m_descents_r0, descents_r1 as d3m_descents_r1, descents_r2 as d3m_descents_r2,
)
from psc.class_a_ray_d3p import (
    rows_r0 as d3p_rows_r0, rows_r1 as d3p_rows_r1, rows_r2 as d3p_rows_r2, pieces_r0 as d3p_pieces_r0, pieces_r1 as d3p_pieces_r1, pieces_r2 as d3p_pieces_r2, descents_r0 as d3p_descents_r0, descents_r1 as d3p_descents_r1, descents_r2 as d3p_descents_r2,
)


def tabulated_rays() -> List[List[Int]]:
    """`[d, eps, r, floor n0, cardinality slope, cardinality constant]` per tabulated ray;
    `n0` is the least `n = r (mod d)` at which both certificates are accepted."""
    return List[List[Int]]([
        List[Int]([2, -1, 0, 14, 40, 93]),
        List[Int]([2, -1, 1, 15, 40, 149]),
        List[Int]([2, 1, 0, 14, 40, 105]),
        List[Int]([2, 1, 1, 13, 40, 111]),
        List[Int]([3, -1, 0, 15, 40, 81]),
        List[Int]([3, -1, 1, 19, 40, 143]),
        List[Int]([3, -1, 2, 20, 40, 131]),
        List[Int]([3, 1, 0, 18, 40, 94]),
        List[Int]([3, 1, 1, 16, 40, 94]),
        List[Int]([3, 1, 2, 17, 40, 98]),
        List[Int]([4, -1, 0, 24, 40, 75]),
        List[Int]([4, -1, 1, 25, 40, 145]),
        List[Int]([4, -1, 2, 22, 40, 129]),
        List[Int]([4, -1, 3, 23, 40, 125]),
        List[Int]([4, 1, 0, 24, 40, 88]),
        List[Int]([4, 1, 1, 21, 40, 90]),
        List[Int]([4, 1, 2, 22, 40, 88]),
        List[Int]([4, 1, 3, 15, 40, 92]),
    ])


def ray_tables(line: ALine) raises -> List[List[List[Int]]]:
    """`[rows, pieces, descents]` of a tabulated ray."""
    line.check()
    if line.d == 2 and line.eps == -1 and line.r == 0:
        return [d2m_rows_r0(), d2m_pieces_r0(), d2m_descents_r0()]
    if line.d == 2 and line.eps == -1 and line.r == 1:
        return [d2m_rows_r1(), d2m_pieces_r1(), d2m_descents_r1()]
    if line.d == 2 and line.eps == 1 and line.r == 0:
        return [d2p_rows_r0(), d2p_pieces_r0(), d2p_descents_r0()]
    if line.d == 2 and line.eps == 1 and line.r == 1:
        return [d2p_rows_r1(), d2p_pieces_r1(), d2p_descents_r1()]
    if line.d == 3 and line.eps == -1 and line.r == 0:
        return [d3m_rows_r0(), d3m_pieces_r0(), d3m_descents_r0()]
    if line.d == 3 and line.eps == -1 and line.r == 1:
        return [d3m_rows_r1(), d3m_pieces_r1(), d3m_descents_r1()]
    if line.d == 3 and line.eps == -1 and line.r == 2:
        return [d3m_rows_r2(), d3m_pieces_r2(), d3m_descents_r2()]
    if line.d == 3 and line.eps == 1 and line.r == 0:
        return [d3p_rows_r0(), d3p_pieces_r0(), d3p_descents_r0()]
    if line.d == 3 and line.eps == 1 and line.r == 1:
        return [d3p_rows_r1(), d3p_pieces_r1(), d3p_descents_r1()]
    if line.d == 3 and line.eps == 1 and line.r == 2:
        return [d3p_rows_r2(), d3p_pieces_r2(), d3p_descents_r2()]
    if line.d == 4 and line.eps == -1:
        var rows = [d4m_rows_r0(), d4m_rows_r1(), d4m_rows_r2(), d4m_rows_r3()]
        var pieces = [d4m_pieces_r0(), d4m_pieces_r1(), d4m_pieces_r2(), d4m_pieces_r3()]
        var descents = [d4m_descents_r0(), d4m_descents_r1(), d4m_descents_r2(), d4m_descents_r3()]
        return [rows[line.r].copy(), pieces[line.r].copy(), descents[line.r].copy()]
    if line.d == 4 and line.eps == 1:
        var rows = [d4p_rows_r0(), d4p_rows_r1(), d4p_rows_r2(), d4p_rows_r3()]
        var pieces = [d4p_pieces_r0(), d4p_pieces_r1(), d4p_pieces_r2(), d4p_pieces_r3()]
        var descents = [d4p_descents_r0(), d4p_descents_r1(), d4p_descents_r2(), d4p_descents_r3()]
        return [rows[line.r].copy(), pieces[line.r].copy(), descents[line.r].copy()]
    raise Error("no generated tables for line " + line.name())


def certify_ray(line: ALine, n0: Int) raises -> List[List[Int]]:
    var t = ray_tables(line)
    var closure = certify_closure_line(line, n0, t[0])
    var descent = certify_descent_line(line, n0, t[0], t[1], t[2])
    print("CLASS_A_RAY_BOUNDARY_HITTING n>=" + String(line.n_of(ray_floor(line, n0))), "line=" + line.name(),
          "closure=true descent=true universal_139=false")
    return [closure^, descent^]

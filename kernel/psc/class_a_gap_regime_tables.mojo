"""Registry of the fitted class-A residue regimes and their generated tables.

`fitted_regimes()` lists `[eps, kind, j, j1, d0, l_fit]` for every regime
whose rows `psc.class_a_gap_regimes.fit` fitted exactly on the label
datasets (kind 0: low `r = j`; 1: high `r = d - j`; 2: middle
`j <= r <= d - j1`). `regime_rows` returns the regime's `l`-affine carrier
rows in ray-row format; `regime_pieces` and `regime_descents` return the
potential pieces and descent occurrences generated for the regime from one
sample ray (`oracles/python/class_a_descent_table.py --ray d,eps,r --src ...`),
and a regime without them refuses. The tables are proof *targets*; evidence
only through `psc.class_a_gap_uniform`. Source note:
docs/class-a-gap-uniform-certificate-design-2026-10-23.md.
"""
from psc.gap_form import Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE
from psc.class_a_gap_regime_rows_minus import regimes_minus, rows_minus
from psc.class_a_gap_regime_rows_plus import regimes_plus, rows_plus
from psc.class_a_gap_regime_descents_minus import (
    pieces_low0 as m_pieces_low0, descents_low0 as m_descents_low0,
)


def fitted_regimes() -> List[List[Int]]:
    var out = regimes_minus()
    out.extend(regimes_plus())
    return out^


def regime_of(spec: List[Int], l0: Int) raises -> Regime:
    """The regime of a registry entry, certified from `l >= l0` and its fitted gap floor."""
    if len(spec) != 6:
        raise Error("malformed regime registry entry")
    return Regime(spec[0], spec[1], spec[2], spec[3], l0, spec[4])


def regime_rows(reg: Regime) raises -> List[List[Int]]:
    if reg.eps == -1:
        return rows_minus(reg.kind, reg.j)
    if reg.eps == 1:
        return rows_plus(reg.kind, reg.j)
    raise Error("class-A line requires eps = +-1")


def regime_pieces(reg: Regime) raises -> List[List[Int]]:
    """Potential pieces `[row, j_lo l-slope, j_lo constant, j_hi l-slope, j_hi constant, X_l, X_j, X_c]`."""
    if reg.eps == -1 and reg.kind == KIND_LOW and reg.j == 0:
        return m_pieces_low0()
    raise Error("no generated descent tables for regime " + reg.name() + " of eps " + String(reg.eps))


def regime_descents(reg: Regime) raises -> List[List[Int]]:
    """Descent occurrences `[piece, j_lo l-slope, j_lo constant, j_hi l-slope, j_hi constant, top part, bottom part, child y, child piece]`."""
    if reg.eps == -1 and reg.kind == KIND_LOW and reg.j == 0:
        return m_descents_low0()
    raise Error("no generated descent tables for regime " + reg.name() + " of eps " + String(reg.eps))


def regime_floors() -> List[List[Int]]:
    """`[eps, kind, j, d0]` per fitted regime: the least gap floor from which both the
    regime closure and the regime descent are accepted at `l >= 5`
    (`kernel/class_a_gap_uniform.mojo floor-all 5 20`, `descent-floor`); the theorem
    assembly re-certifies every entry."""
    return List[List[Int]]([
        List[Int]([-1, 0, 0, 5]),
        List[Int]([-1, 0, 1, 8]),
        List[Int]([-1, 0, 2, 6]),
        List[Int]([-1, 1, 1, 6]),
        List[Int]([-1, 1, 2, 5]),
        List[Int]([-1, 1, 3, 5]),
        List[Int]([-1, 2, 3, 7]),
        List[Int]([1, 0, 0, 5]),
        List[Int]([1, 0, 1, 7]),
        List[Int]([1, 0, 2, 8]),
        List[Int]([1, 0, 3, 9]),
        List[Int]([1, 0, 4, 10]),
        List[Int]([1, 1, 1, 5]),
        List[Int]([1, 1, 2, 5]),
        List[Int]([1, 1, 3, 6]),
        List[Int]([1, 1, 4, 8]),
        List[Int]([1, 1, 5, 9]),
        List[Int]([1, 2, 5, 11]),
    ])

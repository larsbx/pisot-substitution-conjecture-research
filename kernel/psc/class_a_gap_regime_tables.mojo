"""Registry of the fitted class-A residue regimes and their generated tables.

`fitted_regimes()` lists `[eps, kind, j, j1, d0, l_fit]` for every regime
whose rows `psc.class_a_gap_regimes.fit` fitted exactly on the label
datasets (kind 0: low `r = j`; 1: high `r = d - j`; 2: middle
`j <= r <= d - j1`). `regime_rows` returns the regime's `l`-affine carrier
rows in ray-row format. The tables are proof *targets*; evidence only
through `psc.class_a_gap_uniform`. Source note:
docs/class-a-gap-uniform-certificate-design-2026-10-23.md.
"""
from psc.gap_form import Regime, KIND_LOW, KIND_HIGH, KIND_MIDDLE
from psc.class_a_gap_regime_rows_minus import regimes_minus, rows_minus
from psc.class_a_gap_regime_rows_plus import regimes_plus, rows_plus


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

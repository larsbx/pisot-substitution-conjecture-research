"""Source-orbit upper bounds for a conditional strict-carrier seam correction.

Let E be the connected source eventual-range graph and F its permutation.
For an interior-state orbit of length q represented by an actual carrier,
the seam slice is a nonempty F^q-invariant subgraph S of E. At sign eps,
induction around the orbit uses delta = eps^q. Equivariant H1 inclusion
and H0(S) -> H0(E) give

  b_eps(S over the orbit) <= m_delta(H1(E), F^q) - [delta = 1]
                           = m_delta(edges, F^q) - m_delta(vertices, F^q).

E itself attains this graph-only bound. An unrepresented orbit contributes
zero, NOT its possibly negative full-product correction. Thus an inventory
of all possible interior orbits gives the safe sum of positive parts.

These functions only compute finite graph budgets. They do not authenticate
a strict joining, determine coincidence rank, supply a defect rank, or
transfer eigenvalue multiplicities. See the accompanying neutral-rank note.
"""

from finite_exact.checked_int import checked_add, checked_sub
from psc.one_track_seam_spectrum import UnitMultiplicities
from psc.rank_two_parity import ERGraphMap


def _sign_multiplicity(lengths: List[Int], sign: Int) raises -> Int:
    var count = 0
    for length in lengths:
        if length <= 0:
            raise Error("neutral seam budget: cycle length must be positive")
        if sign == 1 or length % 2 == 0:
            count = checked_add(count, 1)
    return count


def source_orbit_budget(graph: ERGraphMap, period: Int, sign: Int) raises -> Int:
    """Sharp graph-only upper bound for one REPRESENTED interior orbit.

    `graph` must come from `er_graph_map` or `graph_map_on`, which validate
    connectedness and the endpoint permutation. `period` is one orbit's
    length, not the number of its states and not an observed power bound.
    """
    if period <= 0:
        raise Error("neutral seam budget: interior period must be positive")
    if sign != 1 and sign != -1:
        raise Error("neutral seam budget: target must be +1 or -1")
    var delta = sign if period % 2 else 1
    var edges = graph.edge_cycle_type(period)
    var vertices = graph.vertex_cycle_type(period)
    return checked_sub(_sign_multiplicity(edges, delta), _sign_multiplicity(vertices, delta))


def represented_source_budget(graph: ERGraphMap, periods: List[Int]) raises -> UnitMultiplicities:
    """Sum signed budgets when exactly these interior orbits are represented.

    Repeated lengths denote distinct orbits. The caller must authenticate
    representation by the actual component; a full source list is not that.
    """
    var plus = 0
    var minus = 0
    for period in periods:
        plus = checked_add(plus, source_orbit_budget(graph, period, 1))
        minus = checked_add(minus, source_orbit_budget(graph, period, -1))
    return UnitMultiplicities(plus, minus)


def optional_source_budget(graph: ERGraphMap, periods: List[Int]) raises -> UnitMultiplicities:
    """Safe upper bounds when each listed source orbit may be absent.

    The supplied list must contain ALL possible interior-state orbits.
    Bounded literal returns alone do not establish completeness. No verdict
    follows from a capped or incomplete period inventory.
    """
    var plus = 0
    var minus = 0
    for period in periods:
        plus = checked_add(plus, max(0, source_orbit_budget(graph, period, 1)))
        minus = checked_add(minus, max(0, source_orbit_budget(graph, period, -1)))
    return UnitMultiplicities(plus, minus)

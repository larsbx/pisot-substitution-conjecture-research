"""Regressions for the exact Rauzy contact structure (psc/rauzy_contacts.mojo).

Pins:
- the box verdict, read from the same box the contacts come from;
- the Tribonacci lattice-neighbour set against the literature;
- the overstrong variant "seed overlaps are contacts", refuted on specimen 1
  (`1 2 5`), whose formal `(0, 1)` swap seeds reach a non-contact;
- the reversal closure of the contacts (Smith), and the fail-closed guards
  against a one-sided contact cycle and a capped graph.

Covering degree 1 is cited from Ito--Rao / Barge--Kwapisz and asserted nowhere
here.
"""

from std.testing import assert_equal, assert_false, assert_true

from mojo_smoke.claims import require_contract
from psc.corpus import pip_corpus
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    build_seed_overlap_graph_from_tables,
    build_seed_overlap_tables,
)
from psc.perron_field3 import CubicElt
from psc.rauzy_contacts import contacts_of, cycle_descendants, tile_contacts
from psc.rauzy_torus import FREQUENCY_SCALE, frequency_frame, incidence_of
from psc.vertex_coincidence import build_box_graph, decide_vertex_coincidence, length_matrix, offset_vector


def _tribonacci() -> List[List[Int]]:
    return [[0, 1], [0, 2], [0]]


def _smith() -> List[List[Int]]:
    return [[1], [0, 2], [0, 2, 0, 1]]


def _has(vs: List[List[Int]], a: Int, b: Int) -> Bool:
    for v in vs:
        if v[0] == a and v[1] == b:
            return True
    return False


def test_verdict_is_the_box_verdict() raises:
    for sigma in [_tribonacci(), _smith()]:
        var t = tile_contacts(sigma, frequency_frame(incidence_of(sigma)))
        var expected = decide_vertex_coincidence(sigma)
        assert_true(t.verdict.productive)
        assert_equal(t.verdict.productive, expected.productive)
        assert_equal(t.verdict.states, expected.states)
        assert_equal(t.verdict.coincidence_depth, expected.coincidence_depth)


def test_tribonacci_has_the_six_lattice_neighbours() raises:
    # The Tribonacci Rauzy fractal tiles its lattice with six neighbours
    # (the classical case of Siegel--Thuswaldner 2009): ±(1,0), ±(0,1), ±(1,-1).
    var frame = frequency_frame(incidence_of(_tribonacci()))
    var t = tile_contacts(_tribonacci(), frame)
    assert_equal(len(t.contacts), 28)
    var nb = t.lattice_neighbours()
    assert_equal(len(nb), 6)
    for v in [[1, 0], [-1, 0], [0, 1], [0, -1], [1, -1], [-1, 1]]:
        assert_true(_has(nb, v[0], v[1]))
    for c in t.contacts:
        var s = c.w0 + c.w1 + c.w2
        assert_equal(c.hi0, FREQUENCY_SCALE * c.w0 - s * frame.f0)
        assert_equal(c.hi1, FREQUENCY_SCALE * c.w1 - s * frame.f1)


def test_seed_overlaps_are_not_contacts() raises:
    # Overstrong variant: swap seeds ab | ba are formal pairs. Specimen 1
    # (1 2 5) has no word 01, and a state reachable from its (0, 1) seeds is
    # not a descendant of any box cycle, hence not a contact.
    var spec = pip_corpus()[1].copy()
    assert_equal(spec.label(), "1 2 5")
    var tables = build_seed_overlap_tables(spec.sigma)
    var box = build_box_graph(tables)
    var mark = cycle_descendants(box)
    var seed = build_seed_overlap_graph_from_tables(tables)
    var strays = 0
    for st in seed.states:
        if st.is_coincidence():
            continue
        var contact = False
        for k in range(box.size()):
            if mark[k] and box.states[k] == st:
                contact = True
        if not contact:
            strays += 1
    assert_true(strays > 0)


def test_smith_contacts_are_closed_under_reversal() raises:
    var sigma = _smith()
    var t = tile_contacts(sigma, frequency_frame(incidence_of(sigma)))
    assert_equal(len(t.contacts), 52)
    var nb = t.lattice_neighbours()
    assert_equal(len(nb), 8)
    for v in nb:
        assert_true(_has(nb, -v[0], -v[1]))


def test_specimen_3742_has_twenty_lattice_neighbours() raises:
    # The specimen whose sampled lift profile never showed a one-lift cell.
    var sigma: List[List[Int]] = [[1, 2, 2], [2, 0, 1], [1, 2]]
    var t = tile_contacts(sigma, frequency_frame(incidence_of(sigma)))
    assert_true(t.verdict.productive)
    assert_equal(len(t.contacts), 148)
    assert_equal(len(t.lattice_neighbours()), 20)


def test_a_one_sided_contact_cycle_is_refused() raises:
    # A synthetic graph whose only cycle is (0, 1, t) with no (1, 0, -t):
    # the contacts would not be closed under reversal, so contacts_of raises.
    var sigma = _tribonacci()
    var frame = frequency_frame(incidence_of(sigma))
    var tables = build_seed_overlap_tables(sigma)
    var lone = OverlapState(0, 1, CubicElt())
    var fake = SeedOverlapAutomaton([lone], [[0]], False)
    var refused = False
    try:
        _ = contacts_of(tables, fake, frame)
    except:
        refused = True
    assert_true(refused)


def test_a_capped_graph_has_no_contacts() raises:
    var capped = SeedOverlapAutomaton(List[OverlapState](), List[List[Int]](), True)
    var refused = False
    try:
        _ = cycle_descendants(capped)
    except:
        refused = True
    assert_true(refused)


def main() raises:
    test_verdict_is_the_box_verdict()
    print("[PASS] contact verdict equals decide_vertex_coincidence")
    test_tribonacci_has_the_six_lattice_neighbours()
    print("[PASS] Tribonacci: 28 contacts, six lattice neighbours, exact P(w) enclosures")
    test_seed_overlaps_are_not_contacts()
    print("[PASS] specimen 1 2 5: a seed-reachable overlap is not a contact")
    test_smith_contacts_are_closed_under_reversal()
    print("[PASS] Smith: 52 contacts, 8 lattice neighbours, closed under reversal")
    test_specimen_3742_has_twenty_lattice_neighbours()
    print("[PASS] specimen 3742: productive box, 148 contacts, 20 lattice neighbours")
    test_a_one_sided_contact_cycle_is_refused()
    print("[PASS] a contact cycle without its reversal raises")
    test_a_capped_graph_has_no_contacts()
    print("[PASS] a capped graph refuses")
    require_contract("rauzy contacts: oriented overlaps (i, j, <l, w>) of the box automaton read as R(i) + P(w) meeting R(j) in H; contacts are the non-coincidence descendants of the box's recurrent components (Siegel-Thuswaldner boundary-graph criterion, cited), are closed under reversal, else raise; seed-graph overlaps are not contacts in general; |w|_1 = 0 contacts are lattice neighbours; the verdict is the same box's Theorem Omega verdict; covering degree 1 is not asserted")

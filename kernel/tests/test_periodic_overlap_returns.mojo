"""Compare overlap occurrence walks with literal based words at twice the power."""

from std.testing import assert_equal, assert_true
from finite_linear_algebra.mat3 import Mat3
from mojo_smoke.claims import require_contract
from psc.bpa import apply_substitution
from psc.c4_geometric_f import PrototileState
from psc.fixed_point_count import fixed_point_formula
from psc.periodic_overlap_returns import PeriodicOverlapGraph
from psc.periodic_pair import incidence_power, interior_occurrences
from psc.perron_field3 import CubicElt
from substitution_dynamics.substitution import Substitution


def literal_pair_counts(sigma: List[List[Int]], n: Int) raises -> List[Int]:
    # Every ordinary and exchanged pair is individually fixed at power 2n.
    # Enumerate those marks in the expanded words and find the centre at n
    # using the actual ancestor block of each mark. No overlap graph is used.
    var power = incidence_power(sigma, n)
    var entries = incidence_power(sigma, 2 * n).e.copy()
    for a in range(3):
        entries[4 * a] -= 1
    var a = Mat3(entries)
    var det = a.det()
    assert_true(det != 0)
    var den = abs(det)
    var sign = 1 if det > 0 else -1
    var adjugate = a.adjugate()
    var images = List[List[Int]]()
    for letter in range(3):
        var word: List[Int] = [letter]
        for _ in range(n):
            word = apply_substitution(sigma, word)
        images.append(word^)

    var states = List[PrototileState]()
    var targets = List[PrototileState]()
    var residues = List[CubicElt]()
    var index = Dict[PrototileState, Int]()
    for letter in range(3):
        for mark in interior_occurrences(sigma, letter, 2 * n, 20000):
            var v = adjugate.apply(mark.prefix)
            for x in range(3):
                v[x] *= sign
            var mid = power.apply(v)
            var ordinal = mark.index
            var middle = -1
            for d in images[letter]:
                if ordinal < len(images[d]):
                    middle = d
                    break
                ordinal -= len(images[d])
                mid[d] -= den
            assert_true(middle >= 0)
            var state = PrototileState(letter, v[0], v[1], v[2])
            assert_true(state not in index)
            index[state] = len(states)
            states.append(state)
            targets.append(PrototileState(middle, mid[0], mid[1], mid[2]))
            residues.append(CubicElt(v[0] % den, v[1] % den, v[2] % den))

    # Columns are ordinary ordered pairs, exchanged ordered pairs, their
    # zero-class parts, and exchanged pairs over two different classes.
    var out = List[Int](length=5, fill=0)
    var fixed_by_residue = Dict[CubicElt, Int]()
    for i in range(len(states)):
        assert_true(targets[i] in index)
        var j = index[targets[i]]
        assert_true(targets[j] == states[i])
        var residue = residues[i]
        if j == i:
            var count = fixed_by_residue[residue] if residue in fixed_by_residue else 0
            fixed_by_residue[residue] = count + 1
            out[0] += 2 * count
            if residue.is_zero():
                out[2] += 2 * count
        elif residue == residues[j]:
            out[1] += 1
            out[3] += Int(residue.is_zero())
        else:
            out[4] += 1
    return out^


def replay(
    sigma: List[List[Int]], ordinary: List[Int], exchanged: List[Int],
    zero_ordinary: List[Int], zero_exchanged: List[Int],
) raises -> Int:
    var graph = PeriodicOverlapGraph(sigma)
    assert_equal(graph.nonproductive_sinks, 0)
    assert_equal(graph.aligned_sinks, 0)
    var cross_fibre = 0
    for n in range(1, len(ordinary) + 1):
        var counts = graph.count(n)
        var literal = literal_pair_counts(sigma, n)
        assert_equal(counts.ordinary.distinct, literal[0])
        assert_equal(counts.exchanged.distinct, literal[1])
        assert_equal(literal[0], ordinary[n - 1])
        assert_equal(literal[1], exchanged[n - 1])
        assert_equal(literal[2], zero_ordinary[n - 1])
        assert_equal(literal[3], zero_exchanged[n - 1])
        assert_equal(counts.ordinary.noncoincident, 0)
        assert_equal(counts.exchanged.noncoincident, 0)
        assert_equal(counts.ordinary.aligned_sink, 0)
        assert_equal(counts.exchanged.aligned_sink, 0)
        cross_fibre += literal[4]
    print(sigma, "ordinary", ordinary, "exchanged", exchanged,
          "zero ordinary/exchanged", zero_ordinary, zero_exchanged)
    return cross_fibre


def test_literal_edge_ordinals() raises:
    var graph = PeriodicOverlapGraph([[1], [0, 2], [2, 0, 2]])
    var repeated = 0
    var endpoint_exit = 0
    for source in range(graph.graph.size()):
        ref row = graph.graph.adj[source]
        var last: List[Int] = [-1, -1]
        var seen = Dict[Int, Bool]()
        var owner = graph.owner[source]
        for k in range(len(row)):
            var indices = graph.occurrence_indices(source, k)
            assert_true(indices[0] > last[0] or (indices[0] == last[0] and indices[1] > last[1]))
            var swapped = graph.occurrence_indices(graph.swap_vertex[source], k)
            assert_equal(swapped, [indices[1], indices[0]])
            last = indices^
            if row[k] in seen:
                repeated += 1
            seen[row[k]] = True
            if owner >= 0 and graph.owner[row[k]] == owner:
                if graph.owner[row[0]] != owner or graph.owner[row[len(row) - 1]] != owner:
                    endpoint_exit += 1
    assert_true(repeated > 0)
    assert_true(endpoint_exit > 0)


def refuses(sigma: List[List[Int]], expected: String, max_states: Int = 400000) -> Bool:
    try:
        _ = PeriodicOverlapGraph(sigma, max_states)
    except e:
        return expected in String(e)
    return False


def test_neutral_model() raises:
    # S1, S2, S3, JS1, JS2, JS3 from the two round-three child orders.
    var a = Substitution.checked([[1], [2], [1, 5, 0], [4], [5], [4, 2, 3]])
    var b = Substitution.checked([[1], [2], [0, 1, 5], [4], [5], [3, 4, 2]])
    assert_equal(a.apply_n([2], 2), [2, 4, 2, 3, 1])
    assert_equal(b.apply_n([2], 2), [1, 2, 3, 4, 2])
    assert_equal(a.apply_n([5], 2), [5, 1, 5, 0, 4])
    assert_equal(b.apply_n([5], 2), [4, 5, 0, 1, 5])
    var sigma: List[List[Int]] = [[1], [2], [0, 2, 1]]
    assert_equal(fixed_point_formula(sigma, 2).total(), 1)
    assert_equal(PeriodicOverlapGraph(sigma).count(2).ordinary.distinct, 0)


def test_refusals() raises:
    var sigma: List[List[Int]] = [[1], [2], [0, 2, 1]]
    assert_true(refuses(sigma, "state cap reached", 1))
    assert_true(refuses([[1], [0, 1, 2], [0, 0, 1]], "must be unimodular"))
    assert_true(refuses([[1], [0, 1, 2], [1, 0, 1]], "characteristic polynomial is reducible"))
    var graph = PeriodicOverlapGraph(sigma)
    var refused = False
    try:
        _ = graph.count(2, max_work=1)
    except e:
        refused = "work cap reached" in String(e)
    assert_true(refused)


def main() raises:
    var zero = List[Int](length=5, fill=0)
    var cross = replay([[1], [2], [0, 2, 1]], [0, 0, 12, 0, 10], [0, 0, 0, 8, 10], zero, zero)
    cross += replay([[0, 1], [1, 2], [0, 2, 1]], [0, 0, 6, 12, 50], [0, 4, 30, 24, 40], zero, zero)
    cross += replay([[0, 1], [0, 2], [0]], [0, 0, 6, 0, 0], [0, 0, 0, 8, 0], zero, zero)
    cross += replay([[1], [0, 2], [2, 0, 2]], [0, 2, 0, 18, 0], [2, 0, 8, 0, 32],
                    [0, 2, 0, 2, 0], [2, 0, 2, 0, 2])
    assert_true(cross > 0)
    test_literal_edge_ordinals()
    test_neutral_model()
    test_refusals()
    require_contract("Unit PIP periodic overlap walks count all ordered same-fibre pairs with both tiles interior, including exchanges at the specified power and zero-class interiors. Endpoint-only returns are subtracted using the full rows. Literal twice-power marks agree for four specimens and powers one through five. Actual edges retain local indices and repetitions, including endpoints leaving the recurrent SCC. The two abstract neutral orders require an impossible second-power return on their source. Reducible, nonunit, and capped passes are refused.")

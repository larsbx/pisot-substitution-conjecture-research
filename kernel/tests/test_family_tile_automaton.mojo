"""Exact replay and overstrong-variant controls for the finite tile graph."""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.bigint_z import BigZ, bigz_add, bigz_eq, bigz_from_i64, bigz_mul, bigz_neg
from finite_graph.scc import sccs
from mojo_smoke.claims import require_contract
from psc.family_tile_automaton import (
    certificate_holds, edge_sources, edge_targets, entry_word, generator_words, recipe_output, recipe_powers,
    reversed_walk, terminal_word, tile_chain_automaton, walk_output, walk_output_from,
)


def main() raises:
    assert_true(certificate_holds())
    var automaton = tile_chain_automaton()
    assert_equal(automaton.states(), 4)
    assert_equal(automaton.letters, 10)
    # Full concrete native table, independently reduced in the Lean model.
    # State order: label1, label0, label2, rejecting sink.
    var expected_table: List[Int] = [
        3, 3, 0, 2, 3, 3, 1, 0, 3, 3,
        1, 0, 3, 3, 3, 1, 3, 3, 3, 2,
        3, 3, 3, 3, 1, 3, 3, 3, 0, 3,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
    ]
    assert_equal(automaton.delta, expected_table)
    var expected_outputs: List[Int] = [
        1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
        -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1,
    ]
    var sources = edge_sources()
    var targets = edge_targets()
    for edge in range(10):
        var source = sources[edge % 5] if edge < 5 else targets[edge % 5]
        var destination = targets[edge % 5] if edge < 5 else sources[edge % 5]
        var path = terminal_word(source)
        path.append(edge)
        var output = walk_output(path, destination)
        for j in range(3):
            assert_true(bigz_eq(output[j], bigz_from_i64(Int64(expected_outputs[3 * edge + j]))))
    assert_false(automaton.accepts([0]))  # 00 cannot start at label 1.
    assert_false(automaton.accepts([3]))  # 12 ends at label 2, not 1.

    var discontinuity_refused = False
    try:
        _ = walk_output([0])
    except e:
        discontinuity_refused = "discontinuous" in String(e)
    assert_true(discontinuity_refused)

    var edge_refused = False
    try:
        _ = reversed_walk([10])
    except e:
        edge_refused = "outside" in String(e)
    assert_true(edge_refused)

    var shape_refused = False
    try:
        _ = recipe_powers([bigz_from_i64(1)])
    except e:
        shape_refused = "three" in String(e)
    assert_true(shape_refused)

    var words = generator_words()
    for i in range(3):
        assert_equal(reversed_walk(reversed_walk(words[i])), words[i])
        var output = walk_output(words[i])
        var reverse = walk_output(reversed_walk(words[i]))
        for j in range(3):
            assert_true(bigz_eq(reverse[j], bigz_neg(output[j])))
    # A sign-blind interpretation of inverses gives the wrong loop output.
    assert_false(bigz_eq(walk_output([6, 0, 1])[0], bigz_from_i64(3)))

    # Removing 00 and its inverse preserves graph connectivity, but every
    # remaining edge satisfies dx-dz=h(target)-h(source). Telescoping on
    # any anchor loop forces x=z, excluding e0. Check all eight edges.
    assert_equal(len(sccs([[1], [1, 2], [0]])), 1)
    var potentials: List[Int] = [-1, 0, 0]
    for edge in range(10):
        if edge % 5 == 0:
            continue
        var i = edge % 5
        var source = sources[i] if edge < 5 else targets[i]
        var destination = targets[i] if edge < 5 else sources[i]
        var sign = 1 if edge < 5 else -1
        var functional = 1 if sources[i] == 0 else -1 if sources[i] == 2 else 0
        assert_equal(sign * functional, potentials[destination] - potentials[source])

    # Exact integers well beyond 64 bits. Powers are kept compressed.
    var large = bigz_from_i64(1)
    for _ in range(150):
        large = bigz_mul(large, bigz_from_i64(2))
    var v: List[BigZ] = [large.copy(), bigz_neg(large), bigz_add(large, bigz_from_i64(17))]
    var rebuilt = recipe_output(recipe_powers(v))
    for j in range(3):
        assert_true(bigz_eq(v[j], rebuilt[j]))

    # A small expanded word checks composition and signed powers in the
    # executable representation. Universal coverage is proved in Lean.
    var target: List[Int] = [2, -3, 4]
    var powers: List[Int] = [-2, -7, 4]
    var expanded = List[Int]()
    for i in range(3):
        var block = words[i].copy() if powers[i] >= 0 else reversed_walk(words[i])
        for _ in range(abs(powers[i])):
            for edge in block:
                expanded.append(edge)
    for label in range(3):
        var full = expanded.copy()
        var tail = terminal_word(label)
        for edge in tail:
            full.append(edge)
        var output = walk_output(full, label)
        for j in range(3):
            assert_true(bigz_eq(output[j], bigz_from_i64(Int64(target[j]))))

    # Bind arbitrary source and target labels to the same finite certificate.
    # The entry is the inverse zero-output tail; no new DFA engine is used.
    for source in range(3):
        var entry = entry_word(source)
        var entry_output = walk_output_from(entry, source, 1)
        for j in range(3):
            assert_true(bigz_eq(entry_output[j], bigz_from_i64(0)))
        for destination in range(3):
            var full = entry.copy()
            for edge in expanded:
                full.append(edge)
            for edge in terminal_word(destination):
                full.append(edge)
            var output = walk_output_from(full, source, destination)
            for j in range(3):
                assert_true(bigz_eq(output[j], bigz_from_i64(Int64(target[j]))))
    # An empty path preserves its actual starting label, not the DFA anchor.
    _ = walk_output_from(List[Int](), 0, 0)
    var wrong_start_refused = False
    try:
        _ = walk_output_from(List[Int](), 0, 1)
    except e:
        wrong_start_refused = "wrong endpoint" in String(e)
    assert_true(wrong_start_refused)
    var invalid_source_refused = False
    try:
        _ = entry_word(3)
    except e:
        invalid_source_refused = "outside" in String(e)
    assert_true(invalid_source_refused)
    # Inverse traversal of 01 is legal and has negative output; the forward
    # edge cannot be replayed from label1. This guards geometric orientation.
    assert_true(bigz_eq(walk_output_from([6], 1, 0)[0], bigz_from_i64(-1)))
    var wrong_orientation_refused = False
    try:
        _ = walk_output_from([1], 1, 0)
    except e:
        wrong_orientation_refused = "discontinuous" in String(e)
    assert_true(wrong_orientation_refused)

    print("PSC_FINITE_TILE_AUTOMATON control_states=3 sink_states=1 edges=10 generators=3 determinant=1 tails=3 bigz_bits=151")
    print("PSC_FINITE_TILE_ENDPOINTS source_labels=3 target_labels=3 endpoint_pairs=9 entries=3 orientation_controls=1")
    require_contract("finite signed family tile-chain automaton, exact integer generator certificate, inverse signs, arbitrary source and target labels, and compressed arbitrary-integer recipes; actual-hull transfer is checked in Lean")

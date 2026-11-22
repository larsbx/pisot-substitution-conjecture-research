"""Finite signed tile-chain certificate for sigma_k, k >= 2.

The control has three tile labels plus a rejecting sink. An edge a->b
has formal output e_a, and its inverse has output -e_a. The integer
output is unbounded: this is not a finite enumeration of lifted states.

An accepted edge word is a co-occurrence chain, not necessarily a legal
substitution word. Actual-hull interpretation is a separate Lean bridge.
See docs/c4-finite-tile-automaton-2026-11-21.md for the pre-code decision.
"""

from finite_automata.dfa import Dfa, with_sink
from finite_exact.bigint_z import BigZ, bigz_add, bigz_eq, bigz_from_i64, bigz_sub, bigz_zero
from finite_graph.scc import sccs
from finite_linear_algebra.mat3 import Mat3


def edge_sources() -> List[Int]:
    return [0, 0, 1, 1, 2]


def edge_targets() -> List[Int]:
    return [0, 1, 1, 2, 0]


def _control(label: Int) raises -> Int:
    if label < 0 or label >= 3:
        raise Error("tile-chain label outside 0,1,2")
    return 1 if label == 0 else 0 if label == 1 else 2


def tile_chain_automaton(target: Int = 1) raises -> Dfa:
    """Use the shared total DFA engine; state zero represents label 1."""
    var target_state = _control(target)
    var labels: List[Int] = [1, 0, 2]
    var sources = edge_sources()
    var targets = edge_targets()
    var partial = List[Int]()
    var accepting = List[Bool]()
    for state in range(3):
        accepting.append(state == target_state)
        for signed_edge in range(10):
            var edge = signed_edge % 5
            var source = sources[edge] if signed_edge < 5 else targets[edge]
            var destination = targets[edge] if signed_edge < 5 else sources[edge]
            partial.append(_control(destination) if labels[state] == source else -1)
    return with_sink(10, partial, accepting)


def reversed_walk(word: List[Int]) raises -> List[Int]:
    """Reverse order and orientation; this is not just reversing the list."""
    var out = List[Int]()
    for i in range(len(word)):
        var edge = word[len(word) - 1 - i]
        if edge < 0 or edge >= 10:
            raise Error("tile-chain edge outside 0..9")
        out.append(edge + 5 if edge < 5 else edge - 5)
    return out^


def walk_output(word: List[Int], target: Int = 1) raises -> List[BigZ]:
    """Reject non-composable words, then accumulate exact signed output."""
    var automaton = tile_chain_automaton(target)
    if not automaton.accepts(word):
        raise Error("tile-chain word is discontinuous or has the wrong endpoint")
    var sources = edge_sources()
    var out = List[BigZ]()
    for _ in range(3):
        out.append(bigz_zero())
    for edge in word:
        var coordinate = sources[edge % 5]
        out[coordinate] = bigz_add(out[coordinate], bigz_from_i64(Int64(1 if edge < 5 else -1)))
    return out^


def generator_words() -> List[List[Int]]:
    """Three loops at label 1, with outputs e0, e1, and e0+e1+e2."""
    return [[6, 0, 1], [2], [3, 4, 1]]


def terminal_word(target: Int) raises -> List[Int]:
    """An anchor-to-target chain of exactly zero integer displacement."""
    _ = _control(target)
    if target == 0:
        return [6, 0, 1, 6]
    if target == 1:
        return List[Int]()
    return [7, 3]


def entry_word(source: Int) raises -> List[Int]:
    """A source-to-anchor chain with zero output, reversing the legal tail."""
    return reversed_walk(terminal_word(source))


def walk_output_from(word: List[Int], source: Int, target: Int) raises -> List[BigZ]:
    """Replay from an arbitrary tile label through the same shared DFA.

    Its fixed initial state is label 1. Prepending the already checked
    zero-output terminal word puts it at source without changing output.
    """
    var anchored = terminal_word(source)
    for edge in word:
        anchored.append(edge)
    return walk_output(anchored, target)


def recipe_powers(v: List[BigZ]) raises -> List[BigZ]:
    """Compressed finite walk for ANY integer triple, no box or state cap.

    Read generator i to power powers[i], using inverse words for a
    negative power. This describes a finite word without materializing
    a possibly enormous number of edge steps.
    """
    if len(v) != 3:
        raise Error("tile-chain displacement needs three integer coordinates")
    return [bigz_sub(v[0], v[2]), bigz_sub(v[1], v[2]), v[2].copy()]


def recipe_output(powers: List[BigZ]) raises -> List[BigZ]:
    if len(powers) != 3:
        raise Error("tile-chain recipe needs three signed powers")
    return [bigz_add(powers[0], powers[2]), bigz_add(powers[1], powers[2]), powers[2].copy()]


def certificate_holds() raises -> Bool:
    """Check the constant witnesses using the existing finite kernels."""
    var words = generator_words()
    var expected: List[List[Int]] = [[1, 0, 0], [0, 1, 0], [1, 1, 1]]
    for i in range(3):
        var output = walk_output(words[i])
        var reverse = walk_output(reversed_walk(words[i]))
        for j in range(3):
            if not bigz_eq(output[j], bigz_from_i64(Int64(expected[i][j]))):
                return False
            if not bigz_eq(reverse[j], bigz_from_i64(Int64(-expected[i][j]))):
                return False
    # Columns are the checked loop outputs. All entries are 0 or 1.
    var matrix = Mat3([1, 0, 1, 0, 1, 1, 0, 0, 1])
    if matrix.det() != 1:
        return False
    for target in range(3):
        var output = walk_output(terminal_word(target), target)
        for j in range(3):
            if not bigz_eq(output[j], bigz_zero()):
                return False
    # Connectivity is a separate finite graph check, never the lattice proof.
    var components = sccs([[0, 1], [1, 2], [0]])
    return len(components) == 1 and len(components[0]) == 3

"""Adversarial occurrence certificates; no universal mathematical claim."""
from std.testing import assert_true, assert_false, assert_equal
from mojo_smoke.claims import require_contract
from psc.occurrence_path import (
    SwapOccurrence, OccurrenceEdge, ImageHead, WordEdge, matched_target,
    replay_overlap_path, certify_overlap_path, replay_word_path, certify_word_path,
    search_overlap_path, CERTIFIED_LIFTABLE_TARGET_PATH, BUDGET_EXHAUSTED,
    DEPTH_COMPLETE_NO_CLOSURE,
)
from psc.overlap_seed_patch import (
    OverlapState, build_seed_overlap_tables, overlap_children,
    selected_overlap_child, interior_overlap,
)
from psc.perron_field3 import CubicElt
from psc.words import Pair, k1
from psc.bpa import inflate_pair


def family() -> List[List[Int]]:
    return [[0, 0, 0, 1, 2, 2], [0, 1], [0]]


def test_target_fidelity() raises:
    var swap = Pair([0, 1], [1, 0])  # 12|21 in one-based notation
    for q in range(-1, 4):
        assert_false(matched_target(swap, q))
    assert_true(matched_target(Pair([0, 1, 2], [1, 0, 2]), 2))
    assert_false(matched_target(Pair([0, 2, 1], [1, 2, 0]), 1))
    assert_false(matched_target(Pair([], []), 0))
    var caught = False
    try:
        _ = matched_target(Pair([0], [1]), 0)
    except:
        caught = True
    assert_true(caught)
    caught = False
    try:
        _ = matched_target(Pair([3], [3]), 0)
    except:
        caught = True
    assert_true(caught)


def test_recurrent_loop_and_productive_exit() raises:
    var sigma = family()
    var tables = build_seed_overlap_tables(sigma)
    var seed = SwapOccurrence(0, 1, 0, 1)
    var s = seed.state(tables)
    var h = OverlapState(2, 0, CubicElt())
    var c = OverlapState(0, 0, CubicElt())
    assert_true(s == OverlapState(0, 0, tables.lengths.at(1)))
    assert_false(s.is_coincidence())
    var path = List[OccurrenceEdge]()
    for _ in range(5):
        path.append(OccurrenceEdge(s, 1, 0, s))
    assert_true(replay_overlap_path(sigma, seed, path) == s)
    var caught = False
    try:
        certify_overlap_path(sigma, seed, path)
    except:
        caught = True
    assert_true(caught)
    path.append(OccurrenceEdge(s, 4, 2, h))
    assert_true(replay_overlap_path(sigma, seed, path) == h)
    caught = False
    try:
        certify_overlap_path(sigma, seed, path)
    except:
        caught = True
    assert_true(caught)  # zero displacement, different letters
    path.append(OccurrenceEdge(h, 0, 0, c))
    certify_overlap_path(sigma, seed, path)
    assert_equal(len(path), 7)
    # Independently locate the direct two-step exit in the full inflated
    # swap words: proper occurrence choices (4,2), then (0,0) give cut 20.
    var inflated_swap = inflate_pair(sigma, inflate_pair(sigma, Pair([0, 1], [1, 0])))
    assert_equal(len(inflated_swap.u), 30)
    assert_true(matched_target(inflated_swap, 20))

    # Exact labelled enumeration agrees occurrence-for-occurrence, including
    # multiplicities, with the canonical graph child generator.
    var parents: List[OverlapState] = [s, h, c]
    for p in range(len(parents)):
        var children = overlap_children(tables, parents[p])
        var index = 0
        for i in range(len(sigma[parents[p].top])):
            for j in range(len(sigma[parents[p].bottom])):
                var child = selected_overlap_child(tables, parents[p], i, j)
                if interior_overlap(tables, child):
                    assert_true(index < len(children))
                    assert_true(child == children[index])
                    index += 1
        assert_equal(index, len(children))


def test_overlap_tampering_and_budgets() raises:
    var sigma = family()
    var seed = SwapOccurrence(0, 1, 0, 1)
    var s = seed.state(build_seed_overlap_tables(sigma))
    var h = OverlapState(2, 0, CubicElt())
    var c = OverlapState(0, 0, CubicElt())
    for bad in range(7):
        var edges = List[OccurrenceEdge]()
        var root = seed
        var budget = 10
        if bad == 0:
            edges.append(OccurrenceEdge(s, -1, 0, s))
        elif bad == 1:
            edges.append(OccurrenceEdge(s, 6, 0, s))
        elif bad == 2:
            edges.append(OccurrenceEdge(s, 1, 0, c))  # altered endpoint
        elif bad == 3:
            edges.append(OccurrenceEdge(s, 4, 2, h))
            edges.append(OccurrenceEdge(c, 0, 0, c))  # same shift, wrong type
        elif bad == 4:
            root = SwapOccurrence(0, 1, 2, 1)
        elif bad == 5:
            edges.append(OccurrenceEdge(s, 1, 0, s))
            budget = 0
        else:
            edges.append(OccurrenceEdge(s, 0, 5, c))  # disjoint selected tiles
        var caught = False
        try:
            _ = replay_overlap_path(sigma, root, edges, budget)
        except:
            caught = True
        assert_true(caught)
    var result = search_overlap_path(sigma, seed, 2, 1000, 10000)
    assert_equal(result.status, CERTIFIED_LIFTABLE_TARGET_PATH)
    assert_equal(len(result.edges), 2)
    certify_overlap_path(sigma, seed, result.edges, 2)
    assert_equal(search_overlap_path(sigma, seed, 0, 1000, 10000).status, DEPTH_COMPLETE_NO_CLOSURE)
    assert_equal(search_overlap_path(sigma, seed, 1, 1000, 10000).status, DEPTH_COMPLETE_NO_CLOSURE)
    assert_equal(search_overlap_path(sigma, seed, 2, 1, 10000).status, BUDGET_EXHAUSTED)
    assert_equal(search_overlap_path(sigma, seed, 2, 1000, 0).status, BUDGET_EXHAUSTED)


def test_projected_context_splice() raises:
    # Identity substitution, two legitimate local edges A->A and C->0|0.
    # All endpoints have total imbalance zero. The projected graph permits
    # their composition from A, but no iterate of A ever has a matched letter.
    var sigma: List[List[Int]] = [[0], [1], [2]]
    var a = Pair([0, 1], [1, 0])
    var c = Pair([0, 1], [0, 1])
    var target = Pair([0], [0])
    var first = WordEdge(a, ImageHead(0, 0), ImageHead(0, 0), 2, a)
    var second = WordEdge(c, ImageHead(0, 0), ImageHead(0, 0), 1, target)
    var left: List[WordEdge] = [first.copy()]
    var right: List[WordEdge] = [second.copy()]
    assert_true(replay_word_path(sigma, a, left) == a)
    certify_word_path(sigma, c, right)
    assert_true(k1(a) == k1(c))
    assert_true(k1(a) == k1(target))
    var mixed: List[WordEdge] = [first.copy(), second.copy()]
    var caught = False
    try:
        certify_word_path(sigma, a, mixed)
    except:
        caught = True
    assert_true(caught)
    caught = False
    try:
        certify_word_path(sigma, a, left)
    except:
        caught = True
    assert_true(caught)


    # Nonzero prefix projection: A=012|210 has no matched target. B=021|201
    # has the same residual d=e0-e2 at cut 1, but its next step returns to
    # zero at cut 2, where 1/1 matches. Splice A:0->1 with B:1->2 and the
    # projected prefix graph suggests a target unreachable in identity(A).
    var a3 = Pair([0, 1, 2], [2, 1, 0])
    var b3 = Pair([0, 2, 1], [2, 0, 1])
    var a_at_one = Pair([a3.u[0]], [a3.v[0]])
    var b_at_one = Pair([b3.u[0]], [b3.v[0]])
    assert_true(k1(a_at_one) == k1(b_at_one))
    assert_true(k1(a_at_one) != k1(Pair([], [])))
    for q in range(4):
        assert_false(matched_target(a3, q))
    assert_true(matched_target(b3, 2))
    var keep_a = WordEdge(a3, ImageHead(0, 0), ImageHead(0, 0), 3, a3)
    var take_b = WordEdge(b3, ImageHead(2, 0), ImageHead(2, 0), 3, Pair([1], [1]))
    var a_only: List[WordEdge] = [keep_a.copy()]
    var b_only: List[WordEdge] = [take_b.copy()]
    assert_true(replay_word_path(sigma, a3, a_only) == a3)
    certify_word_path(sigma, b3, b_only)
    var spliced: List[WordEdge] = [keep_a^, take_b^]
    caught = False
    try:
        certify_word_path(sigma, a3, spliced)
    except:
        caught = True
    assert_true(caught)


def test_paired_heads_and_word_refusals() raises:
    var sigma: List[List[Int]] = [[0, 1], [0], [2]]
    var seed = Pair([0, 1], [1, 0])
    var target = Pair([0], [0])
    var good = WordEdge(seed, ImageHead(0, 0), ImageHead(0, 0), 1, target)
    var path: List[WordEdge] = [good.copy()]
    certify_word_path(sigma, seed, path)
    var residual = Pair([1, 0], [0, 1])
    var branch = WordEdge(seed, ImageHead(0, 1), ImageHead(1, 0), 3, residual)
    var finish = WordEdge(residual, ImageHead(0, 0), ImageHead(0, 0), 1, target)
    var two_steps: List[WordEdge] = [branch^, finish^]
    certify_word_path(sigma, seed, two_steps)
    for bad in range(7):
        var edge = good.copy()
        var budget = 100
        if bad == 0:
            edge.top_head = ImageHead(1, 0)  # top cut 2, bottom cut 0
        elif bad == 1:
            edge.top_head = ImageHead(0, 2)  # not a proper image occurrence
        elif bad == 2:
            edge.end = 4
        elif bad == 3:
            edge.end = 3  # skips the first balanced return
        elif bad == 4:
            edge.target = Pair([1], [1])
        elif bad == 5:
            budget = 2  # both full inflated words have length 3
        else:
            edge.top_head = ImageHead(-1, 0)
        var broken: List[WordEdge] = [edge^]
        var caught = False
        try:
            certify_word_path(sigma, seed, broken, 10, budget)
        except:
            caught = True
        assert_true(caught)
    # A legitimate start can have unequal parent read heads.
    var identity_pair = Pair([0, 1], [1, 0])
    var different: List[List[Int]] = [[0, 0], [0], [2]]
    var at_one = WordEdge(identity_pair, ImageHead(0, 1), ImageHead(1, 0), 2, target)
    var unequal: List[WordEdge] = [at_one^]
    certify_word_path(different, identity_pair, unequal)


def main() raises:
    test_target_fidelity()
    test_recurrent_loop_and_productive_exit()
    test_overlap_tampering_and_budgets()
    test_projected_context_splice()
    test_paired_heads_and_word_refusals()
    print("5 occurrence-path test groups passed")
    require_contract("occurrence paths replay ordered seed and child addresses, reject context splices and false matched targets, and refuse incomplete budgets without universal closure claims")

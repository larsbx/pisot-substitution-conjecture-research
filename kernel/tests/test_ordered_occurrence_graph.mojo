from mojo_smoke.claims import require_contract
from psc.ordered_occurrence_graph import ordered_graph, ordered_parent_residuals, replay_ordered_graph
from psc.words import Pair
from std.testing import assert_equal, assert_true, assert_false, assert_raises


def emit(tag: String, rows: List[List[Int]]):
    for row in rows:
        var line = tag
        for value in row:
            line += "," + String(value)
        print(line)


def main() raises:
    var seed = Pair([0, 1], [1, 0])
    var trib: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var control: List[List[Int]] = [[1], [0, 1, 2], [1]]
    var graph = ordered_graph(trib, seed, 32, 128, 32)
    assert_true(replay_ordered_graph(trib, seed, graph, 32, 128, 32))
    assert_equal(len(graph.states), 11)
    assert_equal(len(graph.edges), 25)
    var non_pisot = ordered_graph(control, seed, 32, 128, 32)
    assert_true(replay_ordered_graph(control, seed, non_pisot, 32, 128, 32))
    assert_equal(len(non_pisot.states), 4)
    assert_equal(len(non_pisot.edges), 8)
    for pair in graph.states:
        emit("R2_TRIB_STATE", [pair.u.copy(), pair.v.copy()])
    emit("R2_TRIB_EDGE", graph.edges)
    for pair in non_pisot.states:
        emit("R2_CONTROL_STATE", [pair.u.copy(), pair.v.copy()])
    emit("R2_CONTROL_EDGE", non_pisot.edges)
    var trib_vectors = ordered_parent_residuals(trib, seed, graph, 32, 128, 32)
    var control_vectors = ordered_parent_residuals(control, seed, non_pisot, 32, 128, 32)
    var trib_cycle: List[Int] = [2, 4, 0, 0, 2]
    var control_cycle0: List[Int] = [1, 3, 2, 0, 0]
    var control_cycle2: List[Int] = [2, 3, 0, 0, 2]
    assert_true(trib_vectors[5] == trib_cycle)
    assert_true(control_vectors[3] == control_cycle0)
    assert_true(control_vectors[5] == control_cycle2)
    emit("R2_TRIB_VECTOR", trib_vectors)
    emit("R2_CONTROL_VECTOR", control_vectors)

    # The two 4→0 edges have different occurrence ordinals and intervals.
    assert_equal(graph.edges[9][1], graph.edges[11][1])
    assert_equal(graph.edges[9][0], graph.edges[11][0])
    graph.edges[11][2] = graph.edges[9][2]
    assert_false(replay_ordered_graph(trib, seed, graph, 32, 128, 32))
    graph.edges[11][2] = 3
    var collapsed = ordered_graph(trib, seed, 32, 128, 32)
    _ = collapsed.edges.pop(11)
    assert_false(replay_ordered_graph(trib, seed, collapsed, 32, 128, 32))
    graph.edges[5][9] = 1
    assert_false(replay_ordered_graph(trib, seed, graph, 32, 128, 32))
    graph.edges[5][9] = -1
    graph.edges[5][8] = 1
    assert_false(replay_ordered_graph(trib, seed, graph, 32, 128, 32))
    graph.edges[5][8] = 0
    _ = graph.edges.pop()
    assert_false(replay_ordered_graph(trib, seed, graph, 32, 128, 32))

    var capped = ordered_graph(trib, seed, 32, 24, 32)
    assert_false(capped.complete)
    capped.complete = True
    assert_false(replay_ordered_graph(trib, seed, capped, 32, 24, 32))
    with assert_raises():
        _ = ordered_parent_residuals(trib, seed, capped, 32, 24, 32)
    with assert_raises():
        _ = ordered_parent_residuals(trib, seed, graph, 32, 128, 32)
    assert_false(ordered_graph(trib, seed, 10, 128, 32).complete)
    assert_false(ordered_graph(trib, seed, 32, 128, 6).complete)
    require_contract("Complete raw ordered BPA rows preserve addresses, signs, and parallel occurrences")

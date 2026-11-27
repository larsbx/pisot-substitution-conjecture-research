"""Symbolic ordered rows and literal boundary closures for sigma_(k,3)."""

from std.testing import assert_equal, assert_false, assert_true
from mojo_smoke.claims import require_contract
from psc.c4_affine_carrier import (
    append_power, append_run, check_irreducible, FIRST_SYMBOLIC_K, fold_images,
    inflate, Length, Run, template,
)
from psc.ordered_occurrence_graph import ordered_graph
from psc.words import Pair

# Row number is the zero-based line index. d:j*m is m copies of d singleton
# 1 coincidences followed by child j. A prime reverses that child's tracks.
# Omitted d and m are 0 and 1. A dash marks a terminal singleton coincidence.
comptime TABLE = """
01 10 | 0' k-1:2
1 1 | -
12 21 | 3 4'
0 0 | -
0010I2 I20001 | 5' k-2:6 k-3:7*k-2 k-3:8
011 110 | 0' k-1:9 k-1:2
11210 20111 | 3 10' k-1:2'
11120 20111 | 3 11'
11120I20001 200011110I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:8'
120 201 | 3 13'
00110I20I20 I20I2000101 | 5' k-2:14 k-2:6 k-3:7*k-3 k-3:15 k-3:7*k-3 k-3:16
00110I20I20I2 I20I20I200011 | 5' k-2:14 k-2:6 k-3:7*k-3 k-3:15 k-3:7*k-3 k-3:15 k-3:7*k-3 k-3:17
0011110I20I20I20 I20I20I200011011 | 5' k-2:14*3 k-2:6 k-3:7*k-5 k-3:18 k-3:7*k-5 k-3:18 k-3:7*k-5 k-3:19
00110I2 I200011 | 5' k-2:14 k-2:6 k-3:7*k-3 k-3:17
1120 2011 | 3 20'
11120I20I2000110 2000110I20I20111 | 3 21' k-3:7'*k-1 22' k-3:7'*k-1 23' k-1:9' k-1:2'
11120I20I200011 200011110I210I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:24' k-2:6' k-3:7'*k-3 k-3:17'
11120I20I20001 200011110I20I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:8'
11120I20I20I20I2000110 2000110I20I20I20I20111 | 3 21' k-3:7'*k-1 22' k-3:7'*k-1 22' k-3:7'*k-1 22' k-3:7'*k-1 23' k-1:9' k-1:2'
11120I20I20I20I200011 200011110I20I210I20I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:24' k-2:6' k-3:7'*k-3 k-3:15' k-3:7'*k-3 k-3:17'
00110I20I2 I20I200011 | 5' k-2:14 k-2:6 k-3:7*k-3 k-3:15 k-3:7*k-3 k-3:17
0011110I20I210I20 I20I20I2000110111 | 5' k-2:14*3 k-2:6 k-3:7*k-5 k-3:18 k-3:7*k-5 k-3:26 k-2:6 k-3:7*k-6 k-3:27
00110I20 H2000110111 | 5' k-2:14 k-2:6 k-3:7*k-6 k-3:27
00110I20 H2000111101 | 5' k-2:14 k-2:6 k-3:7*k-6 k-3:28
11120I200010 2000110I2011 | 3 21' k-3:7'*k-1 23' k-1:2'
11120I2000110 2000110I20111 | 3 21' k-3:7'*k-1 23' k-1:9' k-1:2'
11120I20I20I20I200010 2000110I20I20I20I2011 | 3 21' k-3:7'*k-1 22' k-3:7'*k-1 22' k-3:7'*k-1 22' k-3:7'*k-1 23' k-1:2'
11120I20I20I20I20I200011 200011110I20I210I20I20I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:24' k-2:6' k-3:7'*k-3 k-3:15' k-3:7'*k-3 k-3:15' k-3:7'*k-3 k-3:17'
11120I20I20I20I20I200011 200011110I20I20I20I210I2 | 3 12' k-2:6' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:25' k-3:7'*k-2 k-3:24' k-2:6' k-3:7'*k-3 k-3:17'
"""


@fieldwise_init
struct Child(Copyable, Movable):
    var diagonal_prefix: Length
    var target: Int
    var swapped: Bool
    var count: Length


def affine(text: String) raises -> Length:
    if text == "k":
        return Length(1, FIRST_SYMBOLIC_K)
    if text.startswith("k-"):
        return Length(1, FIRST_SYMBOLIC_K).minus(Length(0, Int(String(text[byte=2:]))))
    return Length(0, Int(text))


def child_token(token: String) raises -> Child:
    var prefix = token.split(":")
    var diagonal_prefix = Length(0, 0)
    var tail = String(prefix[len(prefix) - 1])
    if len(prefix) == 2:
        diagonal_prefix = affine(String(prefix[0]))
    var repeat = tail.split("*")
    var count = affine(String(repeat[1])) if len(repeat) == 2 else Length(0, 1)
    var name = String(repeat[0])
    var swapped = name.endswith("'")
    if swapped:
        var unprimed = String(name[byte=0 : name.byte_length() - 1])
        name = unprimed^
    return Child(diagonal_prefix, Int(name), swapped, count)


def check_row(tracks: List[List[List[Run]]], source: Int, tokens: String) raises:
    ref pair = tracks[source]
    if tokens == "-":
        assert_true(pair[0] == pair[1])
        assert_true(pair[0] == template("0") or pair[0] == template("1"))
        return
    check_irreducible(pair[0], pair[1])
    var products = [List[Run](), List[Run]()]
    var produces_diagonal = False
    for tok in tokens.split(" "):
        var child = child_token(String(tok))
        assert_true(0 <= child.target < len(tracks))
        if child.diagonal_prefix.positive() or child.target == 1 or child.target == 3:
            produces_diagonal = True
        for side in range(2):
            var block = List[Run]()
            append_run(block, Run(1, child.diagonal_prefix))
            for run in tracks[child.target][side ^ Int(child.swapped)]:
                append_run(block, run)
            append_power(products[side], block, child.count)
    assert_true(produces_diagonal)
    for side in range(2):
        assert_true(fold_images(products[side]) == inflate(pair[side]), "ordered row fails literal concatenation")


def check_symbolic() raises:
    var tracks = List[List[List[Run]]]()
    var rows = List[String]()
    for line in TABLE.split("\n"):
        if line.byte_length() == 0:
            continue
        var fields = String(line).split(" | ")
        var words = String(fields[0]).split(" ")
        tracks.append([template(String(words[0])), template(String(words[1]))])
        rows.append(String(fields[1]))
    assert_equal(len(tracks), 29)
    assert_true(tracks[0] == [template("01"), template("10")])
    assert_equal(rows[1], "-")
    assert_equal(rows[3], "-")
    for i in range(len(rows)):
        try:
            check_row(tracks, i, rows[i])
        except e:
            raise Error("symbolic carrier row " + String(i) + ": " + String(e))

    # Both tracks must match, even if a changed row still produces a diagonal.
    assert_row_refused(tracks, "0 k-1:2")
    assert_row_refused(tracks, "0' k-2:2")
    assert_row_refused(tracks, "k-1:2 0'")


def assert_row_refused(tracks: List[List[List[Run]]], incorrect: String) raises:
    try:
        check_row(tracks, 0, incorrect)
    except:
        return
    raise Error("accepted an incorrect ordered row: " + incorrect)


def check_literal(k: Int, states: Int, edges: Int, longest: Int, max_depth: Int) raises:
    var middle: List[Int] = [0]
    for _ in range(k):
        middle.append(1)
    middle.append(2)
    var images: List[List[Int]] = [[1], middle^, [0, 0, 0, 1]]
    var graph = ordered_graph(images, Pair([0, 1], [1, 0]), 1200, 100000, 100000)
    assert_true(graph.complete)
    assert_equal(len(graph.states), states)
    assert_equal(len(graph.edges), edges)
    var longest_seen = 0
    var depths = List[Int]()
    for pair in graph.states:
        longest_seen = max(longest_seen, pair.length())
        if pair.is_coincidence():
            assert_equal(pair.length(), 1)
        depths.append(0 if pair.is_coincidence() else -1)
    assert_equal(longest_seen, longest)

    # Each pass reads the previous depths. Row order cannot shorten a witness.
    for depth in range(1, max_depth + 1):
        var previous = depths.copy()
        for edge in graph.edges:
            if previous[edge[0]] == -1 and previous[edge[1]] >= 0:
                depths[edge[0]] = depth
    var seen_depth = 0
    for depth in depths:
        assert_true(depth >= 0)
        seen_depth = max(seen_depth, depth)
    assert_equal(seen_depth, max_depth)
    print("det3", k, len(graph.states), len(graph.edges), longest_seen, seen_depth)
    if k == 3:
        var capped = ordered_graph(images, Pair([0, 1], [1, 0]), 10, 100000, 100000)
        assert_false(capped.complete)


def main() raises:
    check_symbolic()
    check_literal(3, 587, 66538, 9531, 2)
    check_literal(4, 243, 10983, 264, 1)
    check_literal(5, 65, 1636, 44, 1)
    check_literal(6, 57, 2171, 49, 1)
    check_literal(7, 57, 3136, 54, 1)
    check_literal(8, 57, 4293, 59, 1)
    check_literal(9, 57, 5642, 64, 1)
    check_literal(16, 57, 20461, 99, 1)
    require_contract("The determinant-three 01/10 carrier closes and produces coincidences at every k >= 3")

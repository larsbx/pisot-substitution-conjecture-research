from mojo_smoke.claims import require_contract
from psc.ordered_ancestry_cycles import scan_ordered_cycles, replay_cycle
from psc.words import Pair
from std.testing import assert_equal, assert_true, assert_false


def emit(tag: String, row: List[Int]):
    var line = tag
    for value in row:
        line += "," + String(value)
    print(line)


def main() raises:
    var sigma: List[List[Int]] = [[0, 1], [0, 2], [0]]
    var seed = Pair([0, 1], [1, 0])
    var counts: List[Int] = [1, 3, 9, 18, 35, 71]
    var cycles: List[Int] = [0, 0, 0, 0, 0, 9]
    for depth in range(1, 7):
        var scan = scan_ordered_cycles(sigma, seed, depth, 81, 71)
        assert_true(scan.complete)
        assert_equal(scan.returns, counts[depth - 1])
        assert_equal(len(scan.cycles), cycles[depth - 1])
        emit("R1_SCAN", [depth, scan.returns, len(scan.cycles)])
        for row in scan.cycles:
            emit("R1_CYCLE", row)

    var witness: List[Int] = [51, 0, 3, 1, -1, 0, -3, -3, -2, -2, -1, -1, -1, -1, 0,
                              0, -1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0,
                              2, 2, 0, 1, 0, 0, -1, 0, 0,
                              4, 4, 1, 0, 0, 1, 1, 0, 0]
    assert_true(replay_cycle(sigma, seed, 6, 81, 71, witness))
    witness[21] = 1
    assert_false(replay_cycle(sigma, seed, 6, 81, 71, witness))
    witness[21] = 0
    witness[33] = 1
    assert_false(replay_cycle(sigma, seed, 6, 81, 71, witness))
    # This candidate satisfies A*e0=b, but its local digits do not make
    # the supplied occurrence addresses valid.
    witness[3] = 1
    witness[4] = 0
    witness[15] = -3
    witness[16] = -2
    witness[17] = -1
    witness[24] = -1
    witness[33] = -1
    witness[42] = 0
    assert_false(replay_cycle(sigma, seed, 6, 81, 71, witness))
    assert_false(scan_ordered_cycles(sigma, seed, 6, 80, 71).complete)
    assert_false(scan_ordered_cycles(sigma, seed, 6, 81, 70).complete)
    require_contract("Ordered ancestry cycles bind literal cuts to signed corrections and exact integer equations")

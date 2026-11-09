"""Finite ordered prefix ancestry of literal balanced returns."""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from psc.bpa import coincidence_boundaries
from psc.words import Pair, is_balanced
from substitution_dynamics.substitution import Substitution, validate_word


def _difference(u: List[Int], v: List[Int], i: Int, j: Int) -> List[Int]:
    var x: List[Int] = [0, 0, 0]
    for k in range(i):
        x[u[k]] += 1
    for k in range(j):
        x[v[k]] -= 1
    return x^


def _head(starts: List[Int], cut: Int) -> Int:
    var lo = 0
    var hi = len(starts) - 1
    while lo + 1 < hi:
        var mid = lo + (hi - lo) // 2
        if starts[mid] <= cut:
            lo = mid
        else:
            hi = mid
    return lo


def _action(m: List[Int], x: List[Int]) raises -> List[Int]:
    var y: List[Int] = [0, 0, 0]
    for i in range(3):
        for j in range(3):
            y[i] = checked_add(y[i], checked_mul(m[3 * i + j], x[j]))
    return y^


def _add(x: List[Int], y: List[Int]) raises -> List[Int]:
    return [checked_add(x[0], y[0]), checked_add(x[1], y[1]), checked_add(x[2], y[2])]


struct CycleScan(Movable):
    var complete: Bool
    var returns: Int
    var cycles: List[List[Int]]

    def __init__(out self, complete: Bool, returns: Int, var cycles: List[List[Int]]):
        self.complete = complete
        self.returns = returns
        self.cycles = cycles^


def _bounded_starts(sigma: Substitution, word: List[Int], max_word: Int) raises -> List[Int]:
    var size = 0
    for a in word:
        var n = len(sigma.images[a])
        if n > max_word - size:
            return List[Int]()
        size += n
    return sigma.image_prefix_lengths(word)


def scan_ordered_cycles(images: List[List[Int]], seed: Pair, depth: Int,
                        max_word: Int, max_returns: Int) raises -> CycleScan:
    """All interior zero returns at a given depth or explicit exhaustion.

    A cycle row starts with [cut, first level, final level, initial defect
    (3), A (9 row-major), b (3)]. Then for each chronological step it
    records [top parent index, bottom parent index, top offset, bottom
    offset, top parent letter, bottom parent letter, digit (3)].
    """
    var sigma = Substitution.checked(images)
    if sigma.size != 3 or depth < 1 or depth > 12 or max_word < 1 or max_returns < 0:
        raise Error("invalid ordered ancestry domain")
    validate_word(seed.u, 3)
    validate_word(seed.v, 3)
    if len(seed.u) == 0 or not is_balanced(seed):
        raise Error("ordered ancestry requires a nonempty balanced seed")

    var cycles = List[List[Int]]()
    var top: List[List[Int]] = [seed.u.copy()]
    var bottom: List[List[Int]] = [seed.v.copy()]
    var top_starts = List[List[Int]]()
    var bottom_starts = List[List[Int]]()
    for level in range(depth):
        var ts = _bounded_starts(sigma, top[level], max_word)
        var bs = _bounded_starts(sigma, bottom[level], max_word)
        if len(ts) == 0 or len(bs) == 0:
            return CycleScan(False, 0, cycles^)
        top_starts.append(ts^)
        bottom_starts.append(bs^)
        top.append(sigma.apply(top[level]))
        bottom.append(sigma.apply(bottom[level]))

    var cuts = coincidence_boundaries(top[depth], bottom[depth])
    var m = sigma.incidence()
    var count = 0
    for c in range(1, len(cuts) - 1):
        if count == max_returns:
            return CycleScan(False, count, cycles^)
        count += 1
        var p = cuts[c]
        var q = p
        var defects: List[List[Int]] = [[0, 0, 0]]
        var letters: List[List[Int]] = [[top[depth][p], bottom[depth][q]]]
        var steps = List[List[Int]]()
        # The stored tracks run from the selected return toward its ancestors.
        for t in range(depth):
            var level = depth - t - 1
            var i = _head(top_starts[level], p)
            var j = _head(bottom_starts[level], q)
            var r = p - top_starts[level][i]
            var s = q - bottom_starts[level][j]
            var a = top[level][i]
            var b = bottom[level][j]
            var digit = _difference(sigma.images[a], sigma.images[b], r, s)
            var x = _difference(top[level], bottom[level], i, j)
            if _add(_action(m, x), digit) != defects[t]:
                raise Error("literal prefix ancestry failed exact incidence transport")
            defects.append(x^)
            letters.append([a, b])
            steps.append([i, j, r, s, a, b, digit[0], digit[1], digit[2]])
            p = i
            q = j

        for first in range(depth):
            var src = depth - first
            var zero: List[Int] = [0, 0, 0]
            if defects[src] == zero:
                continue
            for last in range(first + 1, depth + 1):
                var dst = depth - last
                if letters[src] != letters[dst] or defects[src] != defects[dst]:
                    continue
                var rhs: List[Int] = [0, 0, 0]
                var col0: List[Int] = [1, 0, 0]
                var col1: List[Int] = [0, 1, 0]
                var col2: List[Int] = [0, 0, 1]
                var row: List[Int] = [cuts[c], first, last]
                for a in defects[src]:
                    row.append(a)
                for level in range(first, last):
                    ref step = steps[depth - level - 1]
                    rhs = _add(_action(m, rhs), [step[6], step[7], step[8]])
                    col0 = _action(m, col0)
                    col1 = _action(m, col1)
                    col2 = _action(m, col2)
                var operator = List[Int]()
                for i in range(3):
                    operator.append(checked_sub(Int(i == 0), col0[i]))
                    operator.append(checked_sub(Int(i == 1), col1[i]))
                    operator.append(checked_sub(Int(i == 2), col2[i]))
                if _action(operator, defects[src]) != rhs:
                    raise Error("literal cycle failed its exact matrix equation")
                for a in operator:
                    row.append(a)
                for a in rhs:
                    row.append(a)
                for level in range(first, last):
                    for a in steps[depth - level - 1]:
                        row.append(a)
                cycles.append(row^)
    return CycleScan(True, count, cycles^)


def replay_cycle(images: List[List[Int]], seed: Pair, depth: Int, max_word: Int,
                 max_returns: Int, proposed: List[Int]) raises -> Bool:
    var scan = scan_ordered_cycles(images, seed, depth, max_word, max_returns)
    if not scan.complete:
        return False
    for row in scan.cycles:
        if row == proposed:
            return True
    return False

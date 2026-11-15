"""Exact independent replay by merging the two ordered endpoint streams."""
from collections import deque
from functools import cache
from itertools import accumulate

ZERO = (0, 0, 0)
UNIT = tuple(tuple(int(i == j) for i in range(3)) for j in range(3))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def prefixes(word):
    return list(accumulate((UNIT[int(a)] for a in word), add, initial=ZERO))


def diagonal(state):
    a, b, delta = state
    return a == b and delta == ZERO


def geometry(sigma):
    columns = [prefixes(word)[-1] for word in sigma]

    def lift(delta):
        return tuple(sum(delta[j] * columns[j][i] for j in range(3))
                     for i in range(3))

    @cache
    def sign(delta):
        if delta == ZERO:
            return 0
        for _ in range(32):
            if min(delta) >= 0:
                return 1
            if max(delta) <= 0:
                return -1
            delta = lift(delta)
        raise ValueError("uncertified endpoint sign")

    def children(state):
        a, b, delta = state
        if diagonal(state):
            return
        top, bottom = sigma[a], sigma[b]
        left = [add(lift(delta), v) for v in prefixes(top)]
        right = prefixes(bottom)
        i = j = 0
        while i < len(top) and j < len(bottom):
            if sign(sub(left[i+1], right[j])) > 0 and sign(sub(right[j+1], left[i])) > 0:
                yield (i, j), (int(top[i]), int(bottom[j]), sub(left[i], right[j]))
            ends = sign(sub(left[i+1], right[j+1]))
            if ends <= 0:
                i += 1
            if ends >= 0:
                j += 1

    return sign, children


def close(sigma, root, cap=128):
    sign, children = geometry(sigma)
    a, b, delta = root
    if sign(add(delta, UNIT[a])) <= 0 or sign(sub(UNIT[b], delta)) <= 0:
        raise ValueError("root has no interior overlap")
    paths = {root: ()}
    rows = {}
    queue = deque([root])
    while queue:
        state = queue.popleft()
        row = rows[state] = list(children(state))
        for digits, child in row:
            if child in paths:
                continue
            if len(paths) >= cap:
                raise ValueError("incomplete closure")
            paths[child] = paths[state] + (digits,)
            queue.append(child)
    return rows, paths


def first(paths, pred):
    return next((path for state, path in paths.items() if pred(state)), None)


def aligned(edge, side):
    def check(state):
        a, b, delta = state
        offset = ZERO if side == "left" else sub(UNIT[b], UNIT[a])
        return {a, b} == edge and delta == offset
    return check


def inflate(sigma, word):
    return "".join(sigma[int(a)] for a in word)


def factors(sigma, pair):
    top, bottom = (inflate(sigma, word) for word in pair)
    cuts = [i for i, (a, b) in enumerate(zip(prefixes(top), prefixes(bottom), strict=True))
            if a == b]
    assert cuts[-1] == len(top)
    return [(top[i:j], bottom[i:j]) for i, j in zip(cuts, cuts[1:])]


def endpoint_witness(sigma, a, b, end, budget=8):
    """Find an equal letter with equal prefix or suffix Parikh vector."""
    top, bottom = str(a), str(b)
    for depth in range(budget + 1):
        words = (top, bottom) if end == 0 else (top[::-1], bottom[::-1])
        keys = [{(v, letter): i for i, (v, letter) in enumerate(zip(prefixes(w), w))}
                for w in words]
        shared = keys[0].keys() & keys[1].keys()
        if shared:
            key = min(shared, key=lambda k: keys[0][k])
            return depth, tuple(track[key] for track in keys), key
        top, bottom = inflate(sigma, top), inflate(sigma, bottom)
    raise ValueError("no endpoint witness within budget")


def endpoint_orbit(sigma, pair, end):
    orbit = []
    while pair[0] != pair[1] and pair not in orbit:
        orbit.append(pair)
        pair = tuple(int(sigma[a][end]) for a in pair)
    return tuple(orbit), pair


def addressed(sigma, pair, sources, route):
    """Check same-factor containment at every generation and recover first cut."""
    positions = list(sources)
    trace = []
    for digits in route:
        tracks = [tuple(sigma[int(a)] for a in word) for word in pair]
        positions = [sum(map(len, track[:i])) + d
                     for track, i, d in zip(tracks, positions, digits, strict=True)]
        words = ["".join(track) for track in tracks]
        cuts = [i for i, (a, b) in enumerate(zip(*(prefixes(w) for w in words), strict=True))
                if a == b]
        for ordinal, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
            if all(lo <= k < hi for k in positions):
                trace.append(ordinal)
                if hi == lo + 1:
                    cut = lo if lo > 0 else hi
                    assert 0 < cut < len(words[0])
                    return tuple(trace), pair, cut, "Sync+" if lo > 0 else "Sync-"
                pair = tuple(w[lo:hi] for w in words)
                positions = [i - lo for i in positions]
                break
        else:
            raise ValueError("addressed overlap split across factors")
    raise ValueError("route has no diagonal")


def main():
    for sigma, root, size, edge, expected in [
        (("1", "02", "002"), (2, 0, (0, -1, 0)), (54, 94), {1, 2}, (None, 7, 8)),
        (("1", "02", "220"), (2, 1, (-1, 0, 0)), (39, 80), {0, 2}, (3, 3, 3)),
        (("01", "12", "021"), (2, 1, (-1, 0, 0)), (68, 146), {0, 2}, (4, 2, 3)),
    ]:
        rows, paths = close(sigma, root)
        assert (len(rows), sum(map(len, rows.values()))) == size
        left, right, direct = (first(paths, pred) for pred in
                               (aligned(edge, "left"), aligned(edge, "right"), diagonal))
        depths = tuple(len(path) if path is not None else None for path in (left, right, direct))
        assert depths == expected
        print(sigma, size, depths)
        a, b = sorted(edge)
        prefix = endpoint_witness(sigma, a, b, 0)
        suffix = endpoint_witness(sigma, a, b, -1)
        assert (prefix[0], suffix[0]) == ((4, 5) if sigma[-1] == "220" else (1, 1))
        print("prefix and suffix witnesses", prefix, suffix)
        if sigma[-1] == "220":
            assert right == ((1,1),(0,1),(2,0))
            assert endpoint_orbit(sigma, (0, 2), -1) == (
                ((0, 2), (1, 0), (2, 1)), (0, 2))
            state = (0, 2, (-1, 0, 1))
            assert paths[state] == right
            continuation = ((0,2),(1,0),(1,1),(1,0),(0,1))
            assert first(close(sigma, state)[1], diagonal) == continuation
            receipt = addressed(sigma, ("12202202201", "02220220112"), (8, 9),
                                 right + continuation)
            print("off-terminal continuation", receipt)
        if sigma[-1] == "021":
            assert right == ((2,1),(1,0))
            assert addressed(sigma, ("1201", "0112"), (1, 2), right + ((2,1),)) == (
                (0,1,2), ("02112","21120"), 11, "Sync+")
        if sigma[-1] == "002":
            pair = factors(sigma, factors(sigma, ("01", "10"))[0])[0]
            assert pair == ("0210", "1002")
            legal = "2"
            for _ in range(4):
                legal = inflate(sigma, legal)
            assert tuple(legal.index(w) for w in pair) == (2, 0)
            assert factors(sigma, pair) == [("1002021", "0211002")]
            assert factors(sigma, factors(sigma, pair)[0])[1:] == [("0","0"), ("2","2")]
            assert right == ((2,0),(2,1),(2,0),(2,0),(2,1),(0,2),(0,2))
            assert direct == ((2,0),(2,1),(2,0),(1,0),(0,0),(1,0),(2,1),(1,0))
            flip = (root[1], root[0], sub(ZERO, root[2]))
            flipped, _ = close(sigma, flip)
            assert len(flipped) == size[0] and sum(map(len, flipped.values())) == size[1]
            assert not any(aligned(edge, "left")(s) for s in flipped)
            for route in (direct, right + ((0,1),)):
                receipt = addressed(sigma, ("0210", "1002"), (1, 2), route)
                print("addresses", tuple((i, *(d[t] for d in route))
                                         for t, i in enumerate((1, 2))), receipt)
                if route != direct:
                    assert receipt == ((0,0,1,0,0,0,1,3), ("100202021","020211002"), 15, "Sync+")
                if route == direct:
                    assert receipt == ((0,0,1,0,0,0,1,1), ("100202021","020211002"), 5, "Sync+")


def test_orientation_safe_controls():
    main()


if __name__ == "__main__":
    main()

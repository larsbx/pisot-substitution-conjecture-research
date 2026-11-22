"""Exact origin-tile recurrence of the literal family `0 -> 1, 1 -> 0 1^k 2, 2 -> 001`.

A placed tile is `(a; v)` with `v` in `Z^3`: type `a`, start `-l.v`, where
`l = (beta, beta^2, beta + 2)` and `beta` is the real root of
`x^3 - k x^2 - 2 x - 2`.  It is *interior* when the origin lies strictly
inside it: `0 < l.v < l_a`.  Inflation sends it to the child of `sigma(a)`
whose support contains the origin, `(b; M v - P(p))` for the prefix `p` of
`sigma(a)` before that child.  The origin tile of an inflation-periodic
tiling with a lattice origin is a periodic point of this map (Lean:
`Psc.PeriodicPartnerRealization.originChild_periodic_of_periodic`).

Every comparison is the exact sign of `2 w2 + (w0 + w2) x + w1 x^2` at
`beta`, a Sturm--Tarski query on an isolating rational bracket.  No floating
value enters. `cycle_census` follows every interior tile of a coordinate box
to its cycle. It raises if the walk or the full distance to the cycle exceeds
the step cap, or if the walk leaves the packed coordinate range. A census
certifies only the starting tiles in its box.

An interior tile can inflate to a tile that starts at the origin (`(2;-1,0,1)`
has `l.v = 2`, and `2 beta` is the start of the third child of `sigma(2)`).
From then on `v = 0`, and the orbit is in the vertex cycle `(0;0,0,0) ->
(1;0,0,0)`.  A vertex tile never returns to an interior one, so the interior
periodic tiles are exactly the cycles other than that one.
"""

from finite_exact.rat_q import Q
from psc.exact import q_poly
from psc.real_root_sign import count_real_roots, sign_at_isolated_root

comptime PACK = 1 << 14  # packed coordinates lie in [-PACK/2, PACK/2)


def pack_tile(a: Int, v0: Int, v1: Int, v2: Int) raises -> Int:
    var half = PACK // 2
    if a < 0 or a > 2 or v0 < -half or v0 >= half or v1 < -half or v1 >= half or v2 < -half or v2 >= half:
        raise Error("origin tile outside the packed coordinate range")
    return ((a * PACK + v0 + half) * PACK + v1 + half) * PACK + v2 + half


def unpack_tile(key: Int) -> List[Int]:
    var half = PACK // 2
    var v2 = key % PACK - half
    var v1 = (key // PACK) % PACK - half
    var v0 = (key // (PACK * PACK)) % PACK - half
    var a = key // (PACK * PACK * PACK)
    return [a, v0, v1, v2]


struct OriginSystem(Movable):
    """The recurrence at one parameter `k >= 1`, with its sign cache."""

    var k: Int
    var cubic: List[Q]
    var lo: Q
    var hi: Q
    var signs: Dict[Int, Int]

    def __init__(out self, k: Int) raises:
        if k < 1 or k > 64:
            raise Error("origin recurrence needs 1 <= k <= 64")
        self.k = k
        self.cubic = q_poly([-2, -2, -k, 1])
        self.lo = Q.from_int(Int64(k))
        self.hi = Q.from_int(Int64(k + 2))
        self.signs = Dict[Int, Int]()
        if count_real_roots(self.cubic, self.lo, self.hi) != 1:
            raise Error("the bracket (k, k + 2) does not isolate beta")

    def length_sign(mut self, w0: Int, w1: Int, w2: Int) raises -> Int:
        """Exact sign of `l.w = w0 beta + w1 beta^2 + w2 (beta + 2)`."""
        var key = pack_tile(0, w0, w1, w2)
        if key not in self.signs:
            self.signs[key] = sign_at_isolated_root(
                self.cubic, q_poly([2 * w2, w0 + w2, w1]), self.lo, self.hi)
        return self.signs[key]

    def is_interior(mut self, a: Int, v0: Int, v1: Int, v2: Int) raises -> Bool:
        """`0 < l.v < l_a`."""
        if self.length_sign(v0, v1, v2) <= 0:
            return False
        var e: List[Int] = [0, 0, 0]
        e[a] = 1
        return self.length_sign(v0 - e[0], v1 - e[1], v2 - e[2]) < 0

    def image(self, a: Int) -> List[Int]:
        if a == 0:
            return [1]
        if a == 2:
            return [0, 0, 1]
        var out: List[Int] = [0]
        for _ in range(self.k):
            out.append(1)
        out.append(2)
        return out^

    def child(mut self, key: Int) raises -> Int:
        """The child whose support `[-l.w, -l.w + l_b)` contains the origin."""
        var t = unpack_tile(key)
        var w0 = t[2] + 2 * t[3]
        var w1 = t[1] + self.k * t[2] + t[3]
        var w2 = t[2]
        var found = -1
        var image = self.image(t[0])
        for b in image:
            var e: List[Int] = [0, 0, 0]
            e[b] = 1
            if self.length_sign(w0, w1, w2) >= 0 and self.length_sign(w0 - e[0], w1 - e[1], w2 - e[2]) < 0:
                if found >= 0:
                    raise Error("two children contain the origin")
                found = pack_tile(b, w0, w1, w2)
            w0 -= e[0]
            w1 -= e[1]
            w2 -= e[2]
        if found < 0:
            raise Error("no child contains the origin: the tile does not cover it")
        return found


struct CycleCensus(Movable):
    var tiles: Int  # interior tiles of the box
    var longest: Int  # most steps any of them took to reach its cycle
    var cycles: List[List[Int]]  # each cycle in orbit order from its least key

    def __init__(out self):
        self.tiles = 0
        self.longest = 0
        self.cycles = List[List[Int]]()


def cycle_census(mut system: OriginSystem, box: Int, cap: Int) raises -> CycleCensus:
    """Follow every interior tile with `|v_i| <= box` to its cycle."""
    var out = CycleCensus()
    var distance_to_cycle = Dict[Int, Int]()  # zero for a cycle tile
    for a in range(3):
        for v0 in range(-box, box + 1):
            for v1 in range(-box, box + 1):
                for v2 in range(-box, box + 1):
                    if not system.is_interior(a, v0, v1, v2):
                        continue
                    out.tiles += 1
                    var step = Dict[Int, Int]()
                    var path = List[Int]()
                    var cur = pack_tile(a, v0, v1, v2)
                    while cur not in step and cur not in distance_to_cycle:
                        if len(path) >= cap:
                            raise Error("orbit exceeded the step cap: census refused")
                        step[cur] = len(path)
                        path.append(cur)
                        cur = system.child(cur)
                    var tail: Int
                    if cur in distance_to_cycle:
                        tail = len(path) + distance_to_cycle[cur]
                    else:
                        tail = step[cur]
                        var least = tail
                        for i in range(tail, len(path)):
                            if path[i] < path[least]:
                                least = i
                        var cycle = List[Int]()
                        for i in range(len(path) - tail):
                            cycle.append(path[tail + (least - tail + i) % (len(path) - tail)])
                        out.cycles.append(cycle^)
                    if tail > cap:
                        raise Error("orbit exceeded the step cap: census refused")
                    out.longest = max(out.longest, tail)
                    for i in range(len(path)):
                        distance_to_cycle[path[i]] = max(tail - i, 0)
    return out^


def window_range(key: Int) -> Int:
    """Range of `{0, 3 v1 - 1, 3 (v1 + v2) - 2}`: the Lyapunov value of the tile.

    Lean (`Psc.ShiftedRadixCycle.R_window`) proves that for `k >= 2` it does
    not increase along an orbit. It is at least two, with equality exactly
    when `(v1, v2)` is `(0, 0)`, `(1, 0)` or `(0, 1)`."""
    var t = unpack_tile(key)
    var x = 3 * t[2] - 1
    var y = 3 * (t[2] + t[3]) - 2
    var hi = 0
    var lo = 0
    if x > hi:
        hi = x
    if y > hi:
        hi = y
    if x < lo:
        lo = x
    if y < lo:
        lo = y
    return hi - lo


def window_increases(mut system: OriginSystem, box: Int) raises -> Int:
    """Number of interior tiles with `|v_i| <= box` whose origin child has a
    larger window range."""
    var count = 0
    for a in range(3):
        for v0 in range(-box, box + 1):
            for v1 in range(-box, box + 1):
                for v2 in range(-box, box + 1):
                    if not system.is_interior(a, v0, v1, v2):
                        continue
                    var key = pack_tile(a, v0, v1, v2)
                    if window_range(system.child(key)) > window_range(key):
                        count += 1
    return count


def interior_cycles(census: CycleCensus) -> List[List[Int]]:
    """The cycles other than the vertex cycle, in the order found."""
    var out = List[List[Int]]()
    for i in range(len(census.cycles)):
        var t = unpack_tile(census.cycles[i][0])
        if t[1] != 0 or t[2] != 0 or t[3] != 0:
            out.append(census.cycles[i].copy())
    return out^


def tile_text(key: Int) -> String:
    var t = unpack_tile(key)
    return "(" + String(t[0]) + ";" + String(t[1]) + "," + String(t[2]) + "," + String(t[3]) + ")"


def cycle_text(cycle: List[Int]) -> String:
    var out = String("")
    for i in range(len(cycle)):
        if i > 0:
            out += " -> "
        out += tile_text(cycle[i])
    return out

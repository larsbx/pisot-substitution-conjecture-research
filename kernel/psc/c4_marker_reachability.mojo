"""All-level C4 marker-law decision for a specified pair of periodic seams.

The Parikh DFA owns the exact balance condition. The product below adds the
ordered marker register of PeriodicPartnerMarkerReachability. A negative
certificate is a target-free, successor-closed set of product states.
"""

from std.collections import Dict
from finite_automata.dfa import Dfa
from finite_linear_algebra.integer_matrix import is_primitive
from psc.coincidence_formula import parikh_equality_automaton
from psc.h1_census import legal_two_words
from substitution_dynamics import strong_coincidence as sc
from substitution_dynamics.substitution import Substitution
from substitution_dynamics.symmetry import reversed_substitution, reversed_word
from substitution_dynamics.words import parikh


comptime PHASES = 6
comptime NO_LAST = 3
comptime LAST_VALUES = 4
comptime LETTERS = 3
comptime REGISTER_STATES = PHASES * LETTERS * LETTERS * LAST_VALUES * LAST_VALUES * 2
comptime DEFAULT_PRODUCT_CAP = 1 << 20
comptime DEFAULT_LITERAL_CAP = 1 << 20


@fieldwise_init
struct Seam(Copyable, Movable):
    var left: Int
    var right: Int

    def reversed(self) -> Seam:
        return Seam(self.right, self.left)


@fieldwise_init
struct SeamPair(Copyable, Movable):
    var marker: Seam
    var top: Seam
    var bottom: Seam

    def reversed(self) -> SeamPair:
        return SeamPair(self.marker.reversed(), self.top.reversed(), self.bottom.reversed())


@fieldwise_init
struct MarkerRegister(Copyable, Movable):
    var top_last: Int
    var bottom_last: Int
    var parity: Int


@fieldwise_init
struct _TrackStep(Copyable, Movable):
    var last: Int
    var parity: Int


def _power_six(ends: List[Int]) -> List[Int]:
    var out = List[Int]()
    for a in range(len(ends)):
        var reached = a
        for _ in range(PHASES):
            reached = ends[reached]
        out.append(reached)
    return out^


def _pull(row: Int, columns: List[Int]) -> Int:
    """Pull a mod-two row through the substitution, with one bit per letter."""
    var result = 0
    for a in range(len(columns)):
        var bits = row & columns[a]
        var parity = (bits ^ (bits >> 1) ^ (bits >> 2)) & 1
        result |= parity << a
    return result


struct MarkerRegisterTable(Copyable, Movable):
    var first: List[Int]  # F^6
    var last: List[Int]   # L^6
    var _steps: List[List[_TrackStep]]
    var _size: Int

    def __init__(out self, sigma: Substitution, marker: Seam) raises:
        var n = sigma.size
        if n < 2 or n > LETTERS:
            raise Error("the marker register requires two or three letters")
        self._size = n
        var first = sigma.prefix_endpoint_map()
        var last = sigma.suffix_endpoint_map()
        self.first = _power_six(first)
        self.last = _power_six(last)

        var m = sigma.incidence()
        var columns = List[Int](length=n, fill=0)
        for a in range(n):
            for b in range(n):
                columns[a] |= (m[b * n + a] & 1) << b
        for b in range(n):
            if _pull(_pull(_pull(1 << b, columns), columns), columns) != 0:
                raise Error("the marker correction requires M^3 = 0 modulo two")

        # f_j(x,y) = [L^(6+j)(x) = a0 and F^(6+j)(y) = b0].
        var marks = List[List[Int]]()
        var image_rows = List[Int]()
        var left = self.last.copy()
        var right = self.first.copy()
        for _ in range(PHASES):
            var mark = List[Int](length=n * n, fill=0)
            for x in range(n):
                for y in range(n):
                    mark[x * n + y] = Int(left[x] == marker.left and right[y] == marker.right)
            var row = 0
            for a in range(n):
                ref image = sigma.images[a]
                var count = 0
                for d in range(1, len(image)):
                    count ^= mark[image[d - 1] * n + image[d]]
                row |= count << a
            image_rows.append(row)
            marks.append(mark^)
            var old_left = left.copy()
            var old_right = right.copy()
            for a in range(n):
                left[a] = old_left[last[a]]
                right[a] = old_right[first[a]]

        self._steps = List[List[_TrackStep]]()
        for j in range(PHASES):
            var correction = image_rows[(j + 5) % PHASES] ^ _pull(
                image_rows[(j + 4) % PHASES], columns
            ) ^ _pull(_pull(image_rows[(j + 3) % PHASES], columns), columns)
            ref mark = marks[j]
            for a in range(n):
                ref image = sigma.images[a]
                var row = List[_TrackStep]()
                var corrected = 0
                for digit in range(len(image)):
                    # At digit d, corrected is C_j(image[:d]).
                    for previous in range(LAST_VALUES):
                        # In the binary case index 2 is unused.
                        var inflated = last[previous] if previous < n else NO_LAST
                        var end = inflated
                        var parity = corrected
                        if digit > 0:
                            end = image[digit - 1]
                            if inflated != NO_LAST:
                                parity ^= mark[inflated * n + image[0]]
                        row.append(_TrackStep(end, parity))
                    corrected ^= (correction >> image[digit]) & 1
                    if digit > 0:
                        corrected ^= mark[image[digit - 1] * n + image[digit]]
                self._steps.append(row^)

    def advance(
        self, phase: Int, state: MarkerRegister, top: Int, bottom: Int, p: Int, q: Int
    ) -> MarkerRegister:
        """Lean's advance at the destination phase j, given valid image digits."""
        ref x = self._steps[phase * self._size + top][p * LAST_VALUES + state.top_last]
        ref y = self._steps[phase * self._size + bottom][q * LAST_VALUES + state.bottom_last]
        return MarkerRegister(x.last, y.last, state.parity ^ x.parity ^ y.parity)


struct _BinaryReserve(sc.DifferenceBound):
    """For equal incidence columns, equal-length differences reset under M.

    Both images have one length r. A nonzero length difference never catches
    up under d -> r*d + p-q with |p-q| < r. When the difference has length
    zero, identical columns give M*delta = 0 and only the new digits remain.
    """

    var step: sc.CheckedIncidence

    def __init__(out self, sigma: Substitution) raises:
        self.step = sc.CheckedIncidence(sigma)
        ref m = self.step.incidence
        if m[0] != m[1] or m[2] != m[3] or not is_primitive(m, 2):
            raise Error("the binary marker control requires primitive equal Parikh columns")

    def advance(self, delta: List[Int], contribution: List[Int]) raises -> List[Int]:
        return self.step.advance(delta, contribution)

    def admits(self, delta: List[Int]) raises -> Bool:
        return delta[0] == -delta[1]


@fieldwise_init
struct _State(Copyable, Movable):
    var parikh: Int
    var phase: Int
    var top: Int
    var bottom: Int
    var register: MarkerRegister

    def key(self) -> Int:
        var key = self.parikh * PHASES + self.phase
        key = key * LETTERS + self.top
        key = key * LETTERS + self.bottom
        key = key * LAST_VALUES + self.register.top_last
        key = key * LAST_VALUES + self.register.bottom_last
        return key * 2 + self.register.parity


def _state(key: Int) -> _State:
    return _State(
        key // REGISTER_STATES,
        key // (REGISTER_STATES // PHASES) % PHASES,
        key // (LETTERS * LAST_VALUES * LAST_VALUES * 2) % LETTERS,
        key // (LAST_VALUES * LAST_VALUES * 2) % LETTERS,
        MarkerRegister(key // (LAST_VALUES * 2) % LAST_VALUES, key // 2 % LAST_VALUES, key % 2),
    )


struct _Product(Copyable, Movable):
    var sigma: Substitution
    var table: MarkerRegisterTable
    var parikh_dfa: Dfa
    var pair: SeamPair
    var radix: Int

    def __init__(out self, images: List[List[Int]], pair: SeamPair, leftward: Bool) raises:
        self.sigma = (Substitution.checked(reversed_substitution(images)) if leftward
                      else Substitution.checked(images))
        self.pair = pair.reversed() if leftward else pair.copy()
        self.table = MarkerRegisterTable(self.sigma, self.pair.marker)
        var n = self.sigma.size
        var legal = legal_two_words(self.sigma.images)
        for seam in [self.pair.marker.copy(), self.pair.top.copy(), self.pair.bottom.copy()]:
            if seam.left < 0 or seam.left >= n or seam.right < 0 or seam.right >= n:
                raise Error("seam letters lie outside the alphabet")
            var periodic = (
                self.table.last[seam.left] == seam.left and self.table.first[seam.right] == seam.right
            )
            if not legal[n * seam.left + seam.right] or not periodic:
                raise Error("the marker and both source seams must be legal and periodic")
        var top_left_group = self.pair.top.left == self.pair.marker.left
        var bottom_left_group = self.pair.bottom.left == self.pair.marker.left
        var top_right_group = self.pair.top.right == self.pair.marker.right
        var bottom_right_group = self.pair.bottom.right == self.pair.marker.right
        if top_left_group == bottom_left_group or top_right_group == bottom_right_group:
            raise Error("source seams must be opposite in both endpoint groups")

        self.radix = sc.max_image_length(self.sigma)
        var top = self.pair.top.right
        var bottom = self.pair.bottom.right
        if n == LETTERS:
            self.parikh_dfa = parikh_equality_automaton(self.sigma.images, top, bottom)
        else:
            self.parikh_dfa = sc.parikh_equality_automaton(self.sigma, top, bottom, _BinaryReserve(self.sigma))

    def start(self) -> _State:
        return _State(0, 0, self.pair.top.right, self.pair.bottom.right, MarkerRegister(NO_LAST, NO_LAST, 0))

    def advance(self, state: _State, p: Int, q: Int) raises -> _State:
        var phase = (state.phase + PHASES - 1) % PHASES
        return _State(
            self.parikh_dfa.step(state.parikh, p + self.radix * q),
            phase,
            self.sigma.images[state.top][p],
            self.sigma.images[state.bottom][q],
            self.table.advance(phase, state.register, state.top, state.bottom, p, q),
        )

    def required(self, last: Int) -> Int:
        return 1 ^ Int(self.pair.top.right != self.pair.marker.right) ^ Int(self.table.last[last] != self.pair.marker.left)

    def same_last(self, top: Int, bottom: Int) -> Bool:
        return (self.table.last[top] == self.pair.marker.left) == (self.table.last[bottom] == self.pair.marker.left)

    def same_next(self, top: Int, bottom: Int) -> Bool:
        return (self.table.first[top] == self.pair.marker.right) == (self.table.first[bottom] == self.pair.marker.right)

    def target(self, state: _State) -> Bool:
        ref reg = state.register
        return (
            state.phase == 0 and self.parikh_dfa.accepting[state.parikh]
            and reg.top_last != NO_LAST and reg.bottom_last != NO_LAST
            and (
                self.same_last(reg.top_last, reg.bottom_last)
                or self.same_next(state.top, state.bottom)
                or reg.parity != self.required(reg.top_last)
            )
        )

    def count_markers(self, word: List[Int]) -> Int:
        var count = 0
        for i in range(1, len(word)):
            count += Int(self.table.last[word[i - 1]] == self.pair.marker.left
                         and self.table.first[word[i]] == self.pair.marker.right)
        return count


@fieldwise_init
struct MarkerViolation(Copyable, Movable):
    var leftward: Bool
    var top_path: List[Int]
    var bottom_path: List[Int]
    var top_word: List[Int]
    var bottom_word: List[Int]
    var top_next: Int
    var bottom_next: Int
    var balance: List[Int]
    var top_markers: Int
    var bottom_markers: Int
    var required_parity: Int
    var same_last_group: Bool
    var same_next_group: Bool


@fieldwise_init
struct MarkerRayDecision(Copyable, Movable):
    var violation: Optional[MarkerViolation]
    var certificate: List[Int]
    var parikh_states: Int


def _literal(sigma: Substitution, start: Int, path: List[Int], cap: Int) raises -> List[Int]:
    """Spell just the prefix along the address, and append its next letter."""
    var prefix = List[Int]()
    var current = start
    for digit in path:
        var size = digit
        for a in prefix:
            if len(sigma.images[a]) > cap - size:
                raise Error("literal marker witness exceeds the prefix cap")
            size += len(sigma.images[a])
        if size > cap:
            raise Error("literal marker witness exceeds the prefix cap")
        var inflated = sigma.apply(prefix)
        for i in range(digit):
            inflated.append(sigma.images[current][i])
        prefix = inflated^
        current = sigma.images[current][digit]
    prefix.append(current)
    return prefix^


def _violation(
    product: _Product, state: _State, packed: List[Int], leftward: Bool, cap: Int
) raises -> MarkerViolation:
    var paths = sc.pair_paths(product.radix, packed)
    var top = _literal(product.sigma, product.pair.top.right, paths[0], cap)
    var bottom = _literal(product.sigma, product.pair.bottom.right, paths[1], cap)
    var top_next = top.pop()
    var bottom_next = bottom.pop()
    var balance = parikh(top, product.sigma.size)
    if len(top) == 0 or len(bottom) == 0 or balance != parikh(bottom, product.sigma.size):
        raise Error("marker target failed literal Parikh replay")
    var top_last = top[len(top) - 1]
    var bottom_last = bottom[len(bottom) - 1]
    var top_count = product.count_markers(top)
    var bottom_count = product.count_markers(bottom)
    var observed = (top_count ^ bottom_count) & 1
    var required = product.required(top_last)
    var same_last = product.same_last(top_last, bottom_last)
    var same_next = product.same_next(top_next, bottom_next)
    if (
        top_next != state.top or bottom_next != state.bottom
        or top_last != state.register.top_last or bottom_last != state.register.bottom_last
        or observed != state.register.parity
        or not (same_last or same_next or observed != required)
    ):
        raise Error("marker target failed literal endpoint or parity replay")
    return MarkerViolation(
        leftward, paths[0].copy(), paths[1].copy(), top^, bottom^, top_next, bottom_next,
        balance^, top_count, bottom_count, required, same_last, same_next,
    )


def decide_marker_ray(
    sigma: List[List[Int]], pair: SeamPair, leftward: Bool = False,
    state_cap: Int = DEFAULT_PRODUCT_CAP, literal_cap: Int = DEFAULT_LITERAL_CAP,
) raises -> MarkerRayDecision:
    """Decide every prefix cut on the selected side of the original seams.

    Pair this call with its leftward/rightward counterpart to decide all
    balanced intervals. A leftward witness reads away from the origin in the
    reversed substitution. Any resource refusal raises before giving a verdict.
    """
    if state_cap < 1 or literal_cap < 1:
        raise Error("marker resource caps must be positive")
    var product = _Product(sigma, pair, leftward)
    var root = product.start().key()
    var seen = Dict[Int, Int]()
    seen[root] = 0
    var states: List[Int] = [root]
    var parents: List[Int] = [-1]
    var arrivals: List[Int] = [-1]
    var head = 0
    while head < len(states):
        var state = _state(states[head])
        if product.target(state):
            var walk = head
            var path = List[Int]()
            while parents[walk] >= 0:
                path.append(arrivals[walk])
                walk = parents[walk]
            var hit = _violation(product, state, reversed_word(path), leftward, literal_cap)
            return MarkerRayDecision(Optional(hit^), List[Int](), product.parikh_dfa.states())
        for q in range(len(product.sigma.images[state.bottom])):
            for p in range(len(product.sigma.images[state.top])):
                var key = product.advance(state, p, q).key()
                if seen.get(key, -1) >= 0:
                    continue
                if len(states) >= state_cap:
                    raise Error("marker product state cap reached before a decision")
                seen[key] = len(states)
                states.append(key)
                parents.append(head)
                arrivals.append(p + product.radix * q)
        head += 1
    return MarkerRayDecision(Optional[MarkerViolation](), states^, product.parikh_dfa.states())


def verify_marker_certificate(
    sigma: List[List[Int]], pair: SeamPair, leftward: Bool, certificate: List[Int]
) raises -> Bool:
    """Check an inductive invariant with no search and no trusted state count."""
    var product = _Product(sigma, pair, leftward)
    var seen = Dict[Int, Bool]()
    var key_limit = product.parikh_dfa.states() * REGISTER_STATES
    var n = product.sigma.size
    for key in certificate:
        if key < 0 or key >= key_limit:
            return False
        var state = _state(key)
        if state.top >= n or state.bottom >= n or (
            n == 2 and (state.register.top_last == 2 or state.register.bottom_last == 2)
        ):
            return False
        if product.target(state):
            return False
        seen[key] = True
    if not seen.get(product.start().key(), False):
        return False
    for key in certificate:
        var state = _state(key)
        for q in range(len(product.sigma.images[state.bottom])):
            for p in range(len(product.sigma.images[state.top])):
                if not seen.get(product.advance(state, p, q).key(), False):
                    return False
    return True

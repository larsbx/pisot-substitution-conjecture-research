"""Strong coincidence as a formula, and the automaton that eliminates it.

## The formula

For letters `i, j` of a substitution `sigma`, strong coincidence asks

    SC(i, j)  ==  exists k, exists p :
                      p < |sigma^k(i)|,  p < |sigma^k(j)|,
                      sigma^k(i)[p] = sigma^k(j)[p],
                      l(sigma^k(i)[0..p)) = l(sigma^k(j)[0..p))

with `l` the Parikh (abelianisation) map, and `sigma` satisfies the condition
when `SC(i, j)` holds for every pair. The last conjunct is what makes this the
*strong* condition rather than a statement about letters alone: the two
occurrences must be reached after prefixes carrying the same number of each
letter, which is exactly the balanced-pair condition of `psc.bpa` and the
offset-zero condition of the overlap graph.

## Why the four automata already here do not assemble it

`psc.dumont_thomas`, `psc.numeration_addition` and `psc.numeration_conversion`
give admissibility, the letter map, addition and the conversion between the two
numerations -- the first-order theory of positions with `+` and the letter
predicates. The Parikh conjunct is not in that theory: a counting function
`n -> |u[0..n)|_a` is not in general first-order definable from `+` and the
letter predicates, which is why Walnut counts with linear representations
rather than with formulas. So the condition cannot be assembled from what was
built, and needs its own automaton.

What rescues it is that the formula never needs either count -- only that the
two are *equal*. The difference of two Parikh vectors over prefixes reached by
the same number of substitution steps stays bounded, by the Pisot property, and
a bounded integer vector is a finite-state quantity even though neither count
is.

## The automaton

Read a Dumont-Thomas path in `sigma^k(i)` and one in `sigma^k(j)` on two
tracks, synchronously, most significant digit first. At the step whose weights
are at level `m`, a path digit `d` from letter `a` skips the first `d` child
blocks of `sigma(a)`, contributing `M^m e_b` for each skipped letter `b`, where
`M[i][j]` counts letter `i` in `sigma(j)`. Accumulating with
`x <- M x + s` therefore leaves `x` equal to the Parikh vector of the prefix
(`psc.pisot_state.incidence_step`), and the automaton carries the difference

    delta <- M delta + (s_top - s_bottom),   delta_0 = 0,

alongside the two letters the paths have reached. An inadmissible digit on
either track falls into the rejecting sink, and a word is accepted exactly when
`delta = 0` and the two letters agree. Equal Parikh vectors force equal lengths,
so an accepted word is one position `p`, read in both images at once, and its
length is the level `k`. `SC(i, j)` is therefore the language being non-empty,
and the shortest accepted word is the least level at which the pair coincides,
with the two paths naming the position. The existential quantifiers are
discharged by one breadth-first search, which is the whole of the elimination.

## Finiteness is a theorem here, not an import

`M` is primitive with irreducible characteristic polynomial, screened by
`powered_field`, so its eigenvalues are the three distinct roots
`beta, beta_2, beta_3` of that cubic with `beta > 1 > |beta_2|, |beta_3|`.
Write `delta` in the eigenbasis as `a_1 u_1 + a_2 u_2 + a_3 u_3`; the step acts
coordinatewise as `a_r <- lambda_r a_r + t_r` with `|t_r|` bounded over the
finitely many `t` a step can contribute.

* For `r = 2, 3` the map contracts and `a_r` starts at zero, so
  `|a_r| <= max|t_r| / (1 - |lambda_r|)` for the whole run, with nothing to
  enforce.
* For `r = 1` the map expands, and acceptance pins it: with `v` the left Perron
  eigenvector, `v^T delta' = beta v^T delta + v^T t` exactly, so a state that
  can still reach `delta = 0` after `r` further steps satisfies
  `|v^T delta| <= sum_(m<r) beta^(-1-m) |v^T t| < max|v^T t| / (beta - 1)`.
  That is the reserve of `psc.pisot_state`, at `slack = 1`, and here it is an
  identity rather than an estimate, because `v^T` really is an eigenvector
  functional and not an asymptotic ratio.

So every kept state is a point of `Z^3` inside a bounded region, of which there
are finitely many, and the letters are three each. The exploration terminates
for every specimen it accepts, and the state cap is a guard against a defect in
this file, not a budget: exceeding it raises rather than refusing, because
unlike the explorations of `psc.numeration_addition` and
`psc.numeration_conversion` there is no theorem left to import that could make
an honest search come back empty-handed.

## What is and is not claimed

That this decides `SC(i, j)` for a specimen it is run on. Not that any
substitution family satisfies it: the condition is checked, per specimen, and
its agreement with the overlap graph's first-coincidence depths is the census's
business (`mojo/coincidence_formula_census.mojo`). Strong coincidence for the
alphabet-3 Pisot family is open, and nothing here changes that.
"""

from finite_linear_algebra.mat3 import Mat3
from psc.automata import Dfa, Witness, witness
from psc.bpa import substitution_incidence
from psc.dumont_thomas import max_image_length
from psc.numeration_addition import powered_field
from psc.perron_field3 import CubicElt, PerronField3, TileLengths3, perron_tile_lengths_in
from psc.pisot_state import completion_reserve, incidence_step, within_reserve
from psc.words import ALPHABET


comptime STATE_CAP = 1 << 20
"""A guard against a defect here, not a budget: the state set is finite by the
argument above, so reaching this means the argument or this file is wrong."""


def _key(top: Int, bottom: Int, delta: List[Int]) -> String:
    var out = String(top) + "," + String(bottom)
    for i in range(len(delta)):
        out += "," + String(delta[i])
    return out


def _skipped(sigma: List[List[Int]], letter: Int, digit: Int) raises -> List[Int]:
    """The Parikh vector of the first `digit` letters of `sigma(letter)`."""
    if digit < 0 or digit > len(sigma[letter]):
        raise Error("path digit outside the image")
    var out = List[Int](length=ALPHABET, fill=0)
    for r in range(digit):
        out[sigma[letter][r]] += 1
    return out^


struct _Frontier(Copyable, Movable):
    """Everything a step needs, built once per pair rather than per state."""

    var sigma: List[List[Int]]
    var incidence: Mat3
    var field: PerronField3
    var eigenvector: TileLengths3
    var reserve: CubicElt
    var radix: Int

    def __init__(out self, sigma: List[List[Int]], slack: Int) raises:
        if len(sigma) != ALPHABET:
            raise Error("this state carries one coefficient per letter of three")
        self.sigma = sigma.copy()
        self.incidence = Mat3(substitution_incidence(sigma))
        self.field = powered_field(sigma)
        self.eigenvector = perron_tile_lengths_in(self.field, self.incidence)
        self.radix = max_image_length(sigma)
        self.reserve = completion_reserve(self.eigenvector, self.radix, slack)

    def letters(self) -> Int:
        return self.radix * self.radix

    def step(
        self, top: Int, bottom: Int, delta: List[Int], packed: Int
    ) raises -> List[Int]:
        """The successor of a live state, as `(top, bottom, delta)`, or an empty
        list where the transition is inadmissible or can no longer reach zero.

        One place where a transition is decided, so the whole-language build and
        the search that stops at the first witness cannot drift apart."""
        var p = packed % self.radix
        var q = packed // self.radix
        if p >= len(self.sigma[top]) or q >= len(self.sigma[bottom]):
            return List[Int]()
        var contribution = _skipped(self.sigma, top, p)
        var below = _skipped(self.sigma, bottom, q)
        for letter in range(ALPHABET):
            contribution[letter] -= below[letter]
        var next = incidence_step(self.incidence, delta, contribution)
        if not within_reserve(self.field, self.eigenvector, next, self.reserve):
            return List[Int]()
        var out: List[Int] = [self.sigma[top][p], self.sigma[bottom][q]]
        for letter in range(ALPHABET):
            out.append(next[letter])
        return out^


def _accepting(top: Int, bottom: Int, delta: List[Int]) -> Bool:
    return top == bottom and delta[0] == 0 and delta[1] == 0 and delta[2] == 0


def coincidence_automaton(sigma: List[List[Int]], top: Int, bottom: Int) raises -> Dfa:
    """Pairs of paths of one length reaching one letter after prefixes of one
    Parikh vector, over digit pairs packed as `p + radix q`.

    The whole language. `coincidence_witness` answers the emptiness question
    without building it, and is what a caller that only wants the verdict should
    use; this is for the questions that need the automaton itself."""
    return coincidence_automaton_with(sigma, top, bottom, 1, STATE_CAP)


def coincidence_automaton_with(
    sigma: List[List[Int]], top: Int, bottom: Int, slack: Int, cap: Int
) raises -> Dfa:
    """The construction with the pruning bound named, so a regression can widen
    it and see that the language does not move. `slack = 1` is the derived
    bound; anything larger only admits states a minimisation merges back."""
    if top < 0 or top >= ALPHABET or bottom < 0 or bottom >= ALPHABET:
        raise Error("a coincidence pair is two letters of the substitution")
    if cap < 2:
        raise Error("a state cap leaves room for the start state and the sink")
    var frontier = _Frontier(sigma, slack)

    # State 0 is the zero difference at the two starting letters; state 1 is the
    # rejecting sink an inadmissible or hopeless transition falls into.
    var zero = List[Int](length=ALPHABET, fill=0)
    var keys: List[String] = [_key(top, bottom, zero), String("dead")]
    var index = Dict[String, Int]()
    index[keys[0]] = 0
    var tops: List[Int] = [top, -1]
    var bottoms: List[Int] = [bottom, -1]
    var deltas: List[List[Int]] = [zero.copy(), zero.copy()]
    var dead: List[Bool] = [False, True]
    var delta = List[Int]()
    var letters = frontier.letters()

    var done = 0
    while done < len(keys):
        for packed in range(letters):
            if dead[done]:
                delta.append(1)
                continue
            var next = frontier.step(
                tops[done], bottoms[done], deltas[done], packed
            )
            if len(next) == 0:
                delta.append(1)
                continue
            var reached = List[Int]()
            for i in range(ALPHABET):
                reached.append(next[2 + i])
            var key = _key(next[0], next[1], reached)
            var at = index.get(key, -1)
            if at < 0:
                if len(keys) >= cap:
                    raise Error("coincidence state set past the cap: see the finiteness argument")
                keys.append(key)
                index[key] = len(keys) - 1
                tops.append(next[0])
                bottoms.append(next[1])
                deltas.append(reached^)
                dead.append(False)
                at = len(keys) - 1
            delta.append(at)
        done += 1

    var accepting = List[Bool]()
    for s in range(len(keys)):
        accepting.append(
            not dead[s] and _accepting(tops[s], bottoms[s], deltas[s])
        )
    return Dfa(letters, delta, accepting)


def coincidence_witness(sigma: List[List[Int]], top: Int, bottom: Int) raises -> Witness:
    """A shortest pair of paths witnessing `SC(top, bottom)`, or the fact that
    there is none. The word's length is the level, and `pair_paths` splits it
    into the two paths that name the position."""
    return coincidence_witness_with(sigma, top, bottom, 1, STATE_CAP)


def coincidence_witness_with(
    sigma: List[List[Int]], top: Int, bottom: Int, slack: Int, cap: Int
) raises -> Witness:
    """Breadth-first over the same state space, stopping at the first accepting
    state rather than building the whole language first.

    Same answer as `witness(coincidence_automaton(...))` and much less work for
    a pair that coincides early, which is most of them: a shallow search visits
    a handful of states where the full construction would close a set of
    thousands. The regression checks the two agree."""
    if top < 0 or top >= ALPHABET or bottom < 0 or bottom >= ALPHABET:
        raise Error("a coincidence pair is two letters of the substitution")
    if cap < 1:
        raise Error("a state cap is positive")
    var frontier = _Frontier(sigma, slack)
    var zero = List[Int](length=ALPHABET, fill=0)
    var keys: List[String] = [_key(top, bottom, zero)]
    var seen = Dict[String, Int]()
    seen[keys[0]] = 0
    var tops: List[Int] = [top]
    var bottoms: List[Int] = [bottom]
    var deltas: List[List[Int]] = [zero.copy()]
    var parent: List[Int] = [-1]
    var arrival: List[Int] = [-1]
    var letters = frontier.letters()

    var done = 0
    while done < len(keys):
        if _accepting(tops[done], bottoms[done], deltas[done]):
            var reversed = List[Int]()
            var walk = done
            while parent[walk] >= 0:
                reversed.append(arrival[walk])
                walk = parent[walk]
            var word = List[Int]()
            for i in range(len(reversed)):
                word.append(reversed[len(reversed) - 1 - i])
            return Witness(word, False)
        for packed in range(letters):
            var next = frontier.step(
                tops[done], bottoms[done], deltas[done], packed
            )
            if len(next) == 0:
                continue
            var reached = List[Int]()
            for i in range(ALPHABET):
                reached.append(next[2 + i])
            var key = _key(next[0], next[1], reached)
            if key in seen:
                continue
            if len(keys) >= cap:
                raise Error("coincidence state set past the cap: see the finiteness argument")
            seen[key] = len(keys)
            keys.append(key)
            tops.append(next[0])
            bottoms.append(next[1])
            deltas.append(reached^)
            parent.append(done)
            arrival.append(packed)
        done += 1
    return Witness(List[Int](), True)


def coincidence_level(sigma: List[List[Int]], top: Int, bottom: Int) raises -> Int:
    """The least `k` with a coincidence of the pair inside `sigma^k`, or `-1`.

    `-1` is a decided negative, not an exhausted budget: the language is empty."""
    var found = coincidence_witness(sigma, top, bottom)
    return -1 if found.empty else len(found.word)


def strong_coincidence_level(sigma: List[List[Int]]) raises -> Int:
    """The least `k` at which *every* pair of distinct letters has coincided,
    which is the largest per-pair level, or `-1` if some pair never does.

    A pair of equal letters coincides at level zero and is not asked about."""
    var worst = 0
    for i in range(ALPHABET):
        for j in range(i + 1, ALPHABET):
            var here = coincidence_level(sigma, i, j)
            if here < 0:
                return -1
            if here > worst:
                worst = here
    return worst


def pair_paths(radix: Int, word: List[Int]) raises -> List[List[Int]]:
    """The two path words a packed pair word carries, top track first."""
    if radix < 2:
        raise Error("a digit alphabet has at least two digits")
    var top = List[Int]()
    var bottom = List[Int]()
    for i in range(len(word)):
        if word[i] < 0 or word[i] >= radix * radix:
            raise Error("a packed digit pair lies outside the alphabet")
        top.append(word[i] % radix)
        bottom.append(word[i] // radix)
    var out = List[List[Int]]()
    out.append(top^)
    out.append(bottom^)
    return out^


def path_prefix_parikh(
    sigma: List[List[Int]], letter: Int, path: List[Int]
) raises -> List[Int]:
    """The Parikh vector of what a Dumont-Thomas path skips: the prefix of
    `sigma^|path|(letter)` before the position the path names.

    Independent of the automaton, so a witness can be checked rather than
    trusted. The position itself is the sum of the coordinates."""
    if letter < 0 or letter >= len(sigma):
        raise Error("a path starts at a letter of the substitution")
    var m = Mat3(substitution_incidence(sigma))
    var parikh = List[Int](length=ALPHABET, fill=0)
    var current = letter
    for t in range(len(path)):
        var digit = path[t]
        if digit < 0 or digit >= len(sigma[current]):
            raise Error("inadmissible path digit for this letter")
        parikh = incidence_step(m, parikh, _skipped(sigma, current, digit))
        current = sigma[current][digit]
    return parikh^


def path_letter(sigma: List[List[Int]], letter: Int, path: List[Int]) raises -> Int:
    """The letter a path reaches, which is the one standing at its position."""
    var current = letter
    for t in range(len(path)):
        if path[t] < 0 or path[t] >= len(sigma[current]):
            raise Error("inadmissible path digit for this letter")
        current = sigma[current][path[t]]
    return current

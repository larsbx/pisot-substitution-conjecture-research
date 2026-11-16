"""Two parametric families of ternary Pisot substitutions, read with the
canonical kernel: `sigma_{r,s,n}` and `tau_n` of the FC3-family note.

docs/c4-fc3-family-2026-11-16.md (stop/go:
docs/c4-fc3-family-stop-go-2026-11-16.md); the class they are measured
against is that of docs/c4-geometric-f-class-2026-11-16.md, decided on the
standing corpus by `psc.c4_geometric_f`.

    sigma_{r,s,n} = (1^r, 0 1^n 2, 0 1^s),    r >= 1, s >= 0, n >= 1,
    tau_n         = (1, 2 1^n 0, 0 1),        n >= 1.

Both have the incidence matrix `M = [[0,1,1],[r,n,s],[0,1,0]]` (`tau_n` that
of `sigma_{1,1,n}`), so `det M = r`, `tr M = n`, `e_2(M) = -(r+s)` and
`chi_M = t^3 - n t^2 - (r+s) t - r` (`family_charpoly`).

What is a theorem and what is computed here
-------------------------------------------
The statements for *all* parameters are the recorded proofs of the note
(single prover plus independent adversarial re-derivation, not
machine-checked, independent human review pending): PIP3 for `n >= r+s+1`
and for every `tau_n`; property (F) for `n >= 3r+s` and for `tau_n`,
`n >= 5`; the endpoint maps and `dim H^1`; the strong-coincidence witnesses
at levels at most 3. Nothing in this module proves any of them. It builds a
member, asks the canonical kernel about that one substitution, and returns
what the kernel said, so that a regression can pin the statements on a
finite grid of parameters (`kernel/tests/test_c4_fc3_family.mojo`). A grid
is finite evidence: it is not the statement for all parameters, and it
changes no claim status. Universal C4 is open; the witnesses make C4
elementary on these families, which are therefore not new C4 cases.

Which kernel entry points accept these images
---------------------------------------------
The longest image has `n + 2` letters, and the proved regime `n >= 3r+s`
starts at `n = 3`. `psc.c4_geometric_f.decide_geometric_f` and `fc3_profile`
build their `PrototileMap` with `build_seed_overlap_tables`, whose field
comes from `build_perron_field3`: certified for images of length at most
`MAX_CERTIFIED_COLUMN_SUM = 6`, and refusing every longer one. Inside the
proved regime that leaves `sigma_{1,0,3}`, `sigma_{1,0,4}`, `sigma_{1,1,4}`
and no `tau_n`. The refusal is kept: nothing in `psc.c4_geometric_f` is
changed or bypassed, and no `PrototileMap` is built for a longer image.

The entry points that accept long images, each exact and fail closed:

- `psc.pisot` (`is_primitive`, `is_irreducible_cubic`, `is_pisot_charpoly`):
  the cubic decision the corpus is screened with, on coefficients.
  `psc.pisot_screen.screen`, the degree-`n` Routh screen, also runs, and
  *refuses* (neither verdict) at `n = 2r - s - 3`, where the second Routh row
  of the half-plane image starts with `3 + n + s - 2r = 0`; that module names
  `x^3 - 3x^2 - 3x - 3`, the cubic of `sigma_{3,0,3}`, as its known refusal.
  For `r >= 2s + 4` the refused member lies in the range `n >= r+s+1` where
  the note proves PIP3 (`sigma_{4,0,5}`, `sigma_{5,0,7}`): there the PIP3
  verdict is that of `psc.pisot` alone.
- `psc.endpoint_core`, `psc.h1_census.h1_profile`: words and finite graphs.
- `psc.closed_component_search.coincidence_profile` (the literal-word
  `left_witness` search) and `psc.coincidence_formula` (the automaton, on
  the screened field; exact at every length, but slow on some long-image
  members: about 26 s for the six pair questions of `sigma_{5,2,17}`,
  measured 2026-11-16).
- `psc.overlap_seed_patch.build_seed_overlap_tables_screened`: the tables of
  `build_seed_overlap_tables` on the coefficient-screened field
  (`screened_perron_field3`: primitive on Boolean supports, irreducible and
  Pisot over unbounded rationals), all later arithmetic checked. With it,
  `psc.c4_geometric_f.stable_radii`, `psc.vertex_coincidence.box_start_states`
  and `psc.leftmost_chain.leftmost_step` take any `SeedOverlapTables`.

(F) beyond the audited image length
-----------------------------------
`decide_f_screened` decides (F) for a PIP3 substitution of any image length
with those entry points and no second state map:

- the box is `stable_radii` of the screened tables: Lemma B of
  `psc.c4_geometric_f`, a statement about any PIP3 substitution (the image
  bound of `PrototileMap` comes from `build_perron_field3`, not from the
  lemma), and `stable_radii` replays its unchecked `Mat3` steps exactly;
- the candidates are the box start states `(0, j, t)` with `t < 0`: the
  overlap in which a tile of type `0` starts inside a tile of type `j` at
  position `x = -t`, `0 < x < ell_j`, i.e. the prototile state `(j, v)`,
  `x = <ell, v>`, `v != 0` (a superset of the box in the solved coordinate,
  which changes no verdict);
- one step is `psc.leftmost_chain.leftmost_step`: for a negative offset its
  child is `(g(i), f(j, x))` (the bridge of the `psc.c4_geometric_f`
  docstring), and `f(j, x)` does not depend on the top letter, which is
  reset to `0`;
- the walk is that of Lemma W: every orbit is followed to a vertex state,
  to settled ground, or until it closes on itself, so every interior f-cycle
  is recorded once.

The result is a `FamilyFDecision` with `audited = False`. It is not a
`GeometricFVerdict`: `psc.c4_geometric_f` remains the decision on its
domain, and `decide_family_f` uses it there, replaying the address equation
of every interior cycle state. A state cap raises. Lemma B and Lemma W are
recorded proofs, not machine-checked; what the regression holds against the
screened walk is:

- on every standing corpus specimen the screened tables equal the audited
  ones and the walk in the canonical box returns the canonical interior
  cycles (number and periods); on a stride of the corpus and on every grid
  member of at most six letters `decide_f_screened` returns the canonical
  verdict, radii and periods, members that fail (F) included;
- the radii on the long-image grid members are pinned, and twice the radii
  hold no further cycle;
- on six long-image members the literal box graph of Corollary LC5
  (`psc.vertex_coincidence.build_box_graph`, whose radii are the independent
  Sturm-Tarski ones) has no terminal cycle of `psc.leftmost_chain`: the same
  verdict without `stable_radii` and without this module's walk.

`interior_periods_in_box` is the walk in a box the caller names. Like
`psc.c4_geometric_f.interior_cycles_in_box` it returns a search and no
verdict.

The FC3 profile beyond the audited image length
-----------------------------------------------
`screened_fc3_profile` passes the same exact PIP3 gate
(`screened_perron_field3`) and fills the canonical `FC3Profile` from the
functions `fc3_profile_of` reads (`principal_minor_sum`, `h1_profile`,
`periodic_letter_count` of the two endpoint maps), with the determinant and
the trace in checked arithmetic and compared with `Mat3.charpoly`.
`clause_b`, `clause_c` and `nontrivial_fc3_member` are the note's clauses on
that profile: (b) `det M` odd and `dim H^1 <= 4`; (c) `det M` odd and
`tr M != e_2(M) (mod 2)`; a member of the non-trivial part of the FC3 class
has (F), at least two periodic letters for both endpoint maps, and (b) or
(c). Membership is a statement about hypotheses: the conclusion `cr = 1` of
Theorem FC3 is conditional on its imports and is not computed here.

Replay of the finite parts of the written proof of (F)
------------------------------------------------------
With `v = (a, b, c)`, `eps = beta - n` and `theta = 1 / beta`, the proof
has a trapping lemma (every f-periodic state has `b` and `c` in a small
set), which is an argument and is not replayed, and finite statements per
member, which are:

- `sigma_trapping_sign`, `tau_trapping_sign`: the exact sign at the Perron
  root of `beta^2 - (n+1) beta + 2r` (negative iff `eps + 2 r theta < 1`)
  and of `beta^2 - 5 beta - 2` (positive iff `5 theta + 2 theta^2 < 1`): the
  hypothesis of the trapping lemma, which the note shows equivalent to
  `n >= 3r+s`, resp. `n >= 5`. `sigma_kappa_sign` is the sign of
  `beta^2 - (n+1) beta + r` (negative iff `kappa = eps + r theta < 1`), the
  hypothesis of the table lemma.
- `trapped_transients`: every state `(j, (a, b, c))` with `(a, b, c) != 0`
  and `b`, `c` in a stated range is followed to a vertex state; the longest
  transient is returned, and a state that has not arrived within the step
  budget is counted as unresolved (an exhausted budget, not a verdict). The
  note's table lemma is: at most four steps for `b`, `c` in `{0,1}` when
  `kappa < 1`; for `tau_n`, `n >= 5`, at most six for `b` in `{0,1}`, `c`
  in `{-1,0,1}`.

Fail closed (all in the "refuse to conclude" column)
----------------------------------------------------
Parameters outside `1 <= r, n <= FAMILY_MAX_PARAMETER`,
`0 <= s <= FAMILY_MAX_PARAMETER` raise. A malformed substitution raises
before any kernel call (the alphabet-3 views abort on it). A substitution
that is not PIP3 raises in every decision and profile here: outside PIP3
neither (F) nor the clauses mean anything. A state cap raises. A walk whose
leftmost child has a positive offset, a characteristic polynomial that
disagrees with its checked recomputation, and a scan that does not
terminate raise. No floating point is used.
"""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_linear_algebra.mat3 import Mat3
from psc import pisot_screen
from psc.bpa import substitution_incidence
from psc.c4_geometric_f import (
    FC3Profile,
    GEOMETRIC_F_STATE_CAP,
    PrototileMap,
    StableRadiiCache,
    decide_geometric_f_with,
    fc3_profile,
    interior_address,
    periodic_letter_count,
    principal_minor_sum,
    stable_radii,
)
from psc.endpoint_core import prefix_endpoint_map, suffix_endpoint_map
from psc.h1_census import h1_profile
from psc.leftmost_chain import leftmost_step
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapTables,
    build_seed_overlap_tables_screened,
    cached_sign,
)
from psc.perron_field3 import (
    CubicElt,
    MAX_CERTIFIED_COLUMN_SUM,
    cubic_add_checked,
    cubic_scale_checked,
    cubic_sub_checked,
    screened_perron_field3,
    sign_at_perron,
)
from psc.pisot import is_irreducible_cubic, is_pisot_charpoly, is_primitive
from psc.vertex_coincidence import box_start_states
from psc.words import ALPHABET

# Largest parameter the constructors accept: the image `0 1^n 2` then has 64
# letters, the image budget of the C4 word modules and the incidence bound of
# the coincidence automaton.
comptime FAMILY_MAX_PARAMETER = 62

# Iterations after which a monotone integer scan is declared not to terminate.
comptime SCAN_CAP = 1 << 20


def sigma_family(r: Int, s: Int, n: Int) raises -> List[List[Int]]:
    """`sigma_{r,s,n} = (1^r, 0 1^n 2, 0 1^s)`."""
    if r < 1 or n < 1 or s < 0:
        raise Error("sigma_{r,s,n} needs r >= 1, s >= 0, n >= 1")
    if r > FAMILY_MAX_PARAMETER or s > FAMILY_MAX_PARAMETER or n > FAMILY_MAX_PARAMETER:
        raise Error("sigma_{r,s,n}: a parameter beyond FAMILY_MAX_PARAMETER is refused, not built")
    var image0 = List[Int](length=r, fill=1)
    var image1: List[Int] = [0]
    image1 += List[Int](length=n, fill=1)
    image1.append(2)
    var image2: List[Int] = [0]
    image2 += List[Int](length=s, fill=1)
    var out = List[List[Int]]()
    out.append(image0^)
    out.append(image1^)
    out.append(image2^)
    return out^


def tau_family(n: Int) raises -> List[List[Int]]:
    """`tau_n = (1, 2 1^n 0, 0 1)`."""
    if n < 1:
        raise Error("tau_n needs n >= 1")
    if n > FAMILY_MAX_PARAMETER:
        raise Error("tau_n: a parameter beyond FAMILY_MAX_PARAMETER is refused, not built")
    var image1: List[Int] = [2]
    image1 += List[Int](length=n, fill=1)
    image1.append(0)
    var out = List[List[Int]]()
    out.append([1])
    out.append(image1^)
    out.append([0, 1])
    return out^


def family_charpoly(r: Int, s: Int, n: Int) raises -> List[Int]:
    """`t^3 - n t^2 - (r+s) t - r`, low degree first: the characteristic
    polynomial of `[[0,1,1],[r,n,s],[0,1,0]]`, written out. `tau_n` has that
    of `(r, s) = (1, 1)`."""
    return [checked_sub(0, r), checked_sub(0, checked_add(r, s)), checked_sub(0, n), 1]


def eval_cubic(chi: List[Int], x: Int) raises -> Int:
    """`chi(x)` for a cubic given low degree first, in checked arithmetic."""
    if len(chi) != 4:
        raise Error("a cubic has four coefficients")
    var acc = chi[3]
    for k in range(2, -1, -1):
        acc = checked_add(checked_mul(acc, x), chi[k])
    return acc


def _require_ternary(sigma: List[List[Int]]) raises:
    """Three non-empty images over `{0,1,2}`. The alphabet-3 views of the
    kernel abort on anything else; here it is a refusal."""
    if len(sigma) != ALPHABET:
        raise Error("the families live on three letters")
    for a in range(ALPHABET):
        if len(sigma[a]) == 0:
            raise Error("an image is empty")
        for k in range(len(sigma[a])):
            if sigma[a][k] < 0 or sigma[a][k] >= ALPHABET:
                raise Error("an image letter lies outside 0..2")


def longest_image(sigma: List[List[Int]]) raises -> Int:
    _require_ternary(sigma)
    var longest = 0
    for a in range(ALPHABET):
        if len(sigma[a]) > longest:
            longest = len(sigma[a])
    return longest


def within_audited_domain(sigma: List[List[Int]]) raises -> Bool:
    """Whether every image has at most `MAX_CERTIFIED_COLUMN_SUM` letters: the
    image-length domain of `build_perron_field3`, hence of
    `psc.c4_geometric_f.PrototileMap`, `decide_geometric_f` and `fc3_profile`.
    Outside it those entry points refuse; the regression pins that this
    predicate and their refusals agree."""
    return longest_image(sigma) <= MAX_CERTIFIED_COLUMN_SUM


def checked_charpoly(sigma: List[List[Int]]) raises -> List[Int]:
    """`[-det M, e_2(M), -tr M, 1]` of the incidence matrix, in checked
    arithmetic. Raises unless it is what the unchecked `Mat3.charpoly`
    returns, so a wrapped coefficient cannot pass as a polynomial."""
    _require_ternary(sigma)
    var m = Mat3(substitution_incidence(sigma))
    var det = 0
    for i in range(3):
        var j = (i + 1) % 3
        var k = (i + 2) % 3
        var minor = checked_sub(checked_mul(m.at(1, j), m.at(2, k)), checked_mul(m.at(1, k), m.at(2, j)))
        det = checked_add(det, checked_mul(m.at(0, i), minor))
    var trace = checked_add(checked_add(m.at(0, 0), m.at(1, 1)), m.at(2, 2))
    var out: List[Int] = [checked_sub(0, det), principal_minor_sum(m), checked_sub(0, trace), 1]
    if out != m.charpoly():
        raise Error("FC3 family: the checked characteristic polynomial disagrees with Mat3.charpoly")
    return out^


struct FamilyFacts(Copyable, Movable):
    """What the kernel says about one primitive substitution, one entry point
    a field: the checked characteristic polynomial; irreducibility and the
    Pisot property by `psc.pisot`; the answer of the Routh screen
    (`pisot_screen.SCREEN_PISOT`, `SCREEN_NOT_PISOT` or `SCREEN_REFUSED`); the
    two endpoint maps with their numbers of periodic letters; and
    `dim H^1(Omega; Q)` by `psc.h1_census.h1_profile`."""

    var charpoly: List[Int]
    var irreducible: Bool
    var pisot: Bool
    var routh: Int
    var first_letters: List[Int]
    var last_letters: List[Int]
    var left_periodic: Int
    var right_periodic: Int
    var h1_dimension: Int

    def __init__(
        out self,
        charpoly: List[Int],
        irreducible: Bool,
        pisot: Bool,
        routh: Int,
        first_letters: List[Int],
        last_letters: List[Int],
        left_periodic: Int,
        right_periodic: Int,
        h1_dimension: Int,
    ):
        self.charpoly = charpoly.copy()
        self.irreducible = irreducible
        self.pisot = pisot
        self.routh = routh
        self.first_letters = first_letters.copy()
        self.last_letters = last_letters.copy()
        self.left_periodic = left_periodic
        self.right_periodic = right_periodic
        self.h1_dimension = h1_dimension

    def determinant(self) -> Int:
        return -self.charpoly[0]

    def e2(self) -> Int:
        return self.charpoly[1]

    def trace(self) -> Int:
        return -self.charpoly[2]

    def pip3(self) -> Bool:
        """Primitive (the gate of `family_facts`), irreducible and Pisot."""
        return self.irreducible and self.pisot


def family_facts(sigma: List[List[Int]]) raises -> FamilyFacts:
    """The facts of one substitution. Raises unless its incidence matrix is
    primitive: `h1_profile` needs primitivity, and every member of the two
    families is primitive (`M^3 > 0`). No PIP3 gate: the Pisot screens are
    reported, also where they reject."""
    var chi = checked_charpoly(sigma)
    if not is_primitive(Mat3(substitution_incidence(sigma))):
        raise Error("FC3 family: the incidence matrix is not primitive")
    var first = prefix_endpoint_map(sigma)
    var last = suffix_endpoint_map(sigma)
    return FamilyFacts(
        chi,
        is_irreducible_cubic(chi),
        is_pisot_charpoly(chi),
        pisot_screen.screen(chi),
        first,
        last,
        periodic_letter_count(first),
        periodic_letter_count(last),
        h1_profile(sigma).dimension,
    )


def screened_fc3_profile(sigma: List[List[Int]]) raises -> FC3Profile:
    """The `FC3Profile` of a PIP3 substitution of any image length. The gate
    is `screened_perron_field3`, which raises unless the incidence matrix is
    primitive with an irreducible Pisot characteristic polynomial; the six
    facts are those `psc.c4_geometric_f.fc3_profile_of` reads, with the
    determinant and the trace checked. On the audited image-length domain it
    equals `fc3_profile` (pinned by the regression)."""
    var chi = checked_charpoly(sigma)
    _ = screened_perron_field3(Mat3(substitution_incidence(sigma)))
    return FC3Profile(
        checked_sub(0, chi[0]),
        checked_sub(0, chi[2]),
        chi[1],
        h1_profile(sigma).dimension,
        periodic_letter_count(prefix_endpoint_map(sigma)),
        periodic_letter_count(suffix_endpoint_map(sigma)),
    )


def family_fc3_profile(sigma: List[List[Int]]) raises -> FC3Profile:
    """`fc3_profile` on its audited image-length domain, `screened_fc3_profile`
    beyond it. Raises unless `sigma` is PIP3."""
    if within_audited_domain(sigma):
        return fc3_profile(sigma)
    return screened_fc3_profile(sigma)


def clause_b(profile: FC3Profile) -> Bool:
    """Clause (b) of Theorem FC3: `det M` odd and `dim H^1 <= 4`."""
    return profile.det_odd() and profile.cohomology_clause()


def clause_c(profile: FC3Profile) -> Bool:
    """Clause (c) of Theorem FC3: `det M` odd and `tr M != e_2(M) (mod 2)`."""
    return profile.det_odd() and profile.parity_clause()


def nontrivial_fc3_member(profile: FC3Profile, holds: Bool) -> Bool:
    """The hypotheses of the non-trivial part of the FC3 class: (F), at least
    two periodic letters for both endpoint maps (clause (a') fails), and
    clause (b) or (c). `holds` is property (F), decided elsewhere. Hypotheses
    only: the conclusion of Theorem FC3 is not computed."""
    return holds and not profile.endpoint_trivial() and profile.arithmetic_clause()


struct FamilyFDecision(Copyable, Movable):
    """Property (F) of one PIP3 substitution with the periods of its interior
    f-cycles, ascending. `audited` says which decision it is: `True` for
    `psc.c4_geometric_f` on its image-length domain, `False` for
    `decide_f_screened`. `radii` is the box of `stable_radii`; `candidates`
    and `visited` are the sizes of the search (the screened candidates are a
    superset of the box in the solved coordinate, so the two routes are not
    compared on them)."""

    var holds: Bool
    var audited: Bool
    var radii: List[Int]
    var candidates: Int
    var visited: Int
    var periods: List[Int]

    def __init__(
        out self, holds: Bool, audited: Bool, radii: List[Int], candidates: Int, visited: Int, periods: List[Int]
    ):
        self.holds = holds
        self.audited = audited
        self.radii = radii.copy()
        self.candidates = candidates
        self.visited = visited
        self.periods = periods.copy()

    def cycles(self) -> Int:
        return len(self.periods)


def _ascending(values: List[Int]) -> List[Int]:
    var out = values.copy()
    for i in range(1, len(out)):
        var x = out[i]
        var j = i
        while j > 0 and out[j - 1] > x:
            out[j] = out[j - 1]
            j -= 1
        out[j] = x
    return out^


def decide_f_audited(sigma: List[List[Int]], max_states: Int = GEOMETRIC_F_STATE_CAP) raises -> FamilyFDecision:
    """`psc.c4_geometric_f` on one substitution: the verdict of
    `decide_geometric_f_with` in the box of `stable_radii`, every state of
    every interior cycle replaying its address equation `(M^k - I) v = p(P)`
    through `interior_address` (which raises on failure). Raises on an image
    longer than `MAX_CERTIFIED_COLUMN_SUM` and on input that is not PIP3: the
    refusals of `PrototileMap`."""
    _require_ternary(sigma)
    var m = PrototileMap(sigma)
    var boxes = StableRadiiCache()
    var verdict = decide_geometric_f_with(m, boxes, max_states)
    var periods = List[Int]()
    for c in range(len(verdict.cycles)):
        for t in range(verdict.cycles[c].period()):
            _ = interior_address(m, verdict.cycles[c], t)
        periods.append(verdict.cycles[c].period())
    return FamilyFDecision(
        verdict.holds, True, verdict.radii, verdict.candidates, verdict.visited, _ascending(periods)
    )


def _prototile_child(
    tables: SeedOverlapTables, mut cache: Dict[CubicElt, Int], state: OverlapState
) raises -> OverlapState:
    """`f` on the overlap `(0, j, -x)`, `0 < x < ell_j`: the leftmost child
    with its top letter reset to `0`. The leftmost child keeps the sign of the
    offset or lands on zero; anything else is an impossible state."""
    var child = leftmost_step(tables, cache, state).child
    if cached_sign(tables, cache, child.shift) > 0:
        raise Error("FC3 family: a leftmost child of a negative offset has a positive offset")
    return OverlapState(0, child.bottom, child.shift)


struct ScreenedBoxSearch(Copyable, Movable):
    """What walking the prototile states of one box found, on the screened
    tables: the periods of the interior f-cycles their orbits enter, in the
    order met, and the size of the search. Like `psc.c4_geometric_f.BoxSearch`
    it is not a verdict and has no `holds`: an empty `periods` is property (F)
    only when the box holds every f-periodic state, which is what Lemma B
    says of `stable_radii` and of no box a caller names."""

    var radii: List[Int]
    var candidates: Int
    var visited: Int
    var periods: List[Int]

    def __init__(out self, radii: List[Int], candidates: Int, visited: Int, periods: List[Int]):
        self.radii = radii.copy()
        self.candidates = candidates
        self.visited = visited
        self.periods = periods.copy()


def interior_periods_in_box(
    tables: SeedOverlapTables, radii: List[Int], max_states: Int = GEOMETRIC_F_STATE_CAP
) raises -> ScreenedBoxSearch:
    """The interior f-cycles that the orbit of a prototile state of the box
    enters, in particular every one that meets the box. The candidates are
    the box start states `(0, j, t)` with `t < 0` (module docstring); each
    orbit is followed until it reaches a vertex state, settled ground, or
    closes on itself, as in Lemma W. A search, not a verdict. Raises when the
    walk visits more than `max_states` states."""
    if max_states <= 0:
        raise Error("FC3 family: the state cap must be positive")
    if len(radii) != 3 or radii[0] < 0 or radii[1] < 0 or radii[2] < 0:
        raise Error("FC3 family: malformed box radii")
    var cache = Dict[CubicElt, Int]()
    var starts = box_start_states(tables, radii, cache)
    # depth + 1 while on the current walk, 0 once settled
    var mark = Dict[OverlapState, Int]()
    var periods = List[Int]()
    var candidates = 0
    for i in range(len(starts)):
        if starts[i].top != 0 or cached_sign(tables, cache, starts[i].shift) >= 0:
            continue
        candidates += 1
        if starts[i] in mark:
            continue
        var path = List[OverlapState]()
        var s = starts[i]
        while True:
            if s.shift.is_zero():
                break
            if s in mark:
                var depth = mark[s]
                if depth > 0:
                    periods.append(len(path) - (depth - 1))
                break
            if len(mark) >= max_states:
                raise Error("FC3 family: state cap reached; inconclusive, not a verdict")
            path.append(s)
            mark[s] = len(path)
            s = _prototile_child(tables, cache, s)
        for k in range(len(path)):
            mark[path[k]] = 0
    return ScreenedBoxSearch(radii, candidates, len(mark), periods)


def decide_f_screened(sigma: List[List[Int]], max_states: Int = GEOMETRIC_F_STATE_CAP) raises -> FamilyFDecision:
    """Property (F) of a PIP3 substitution of any image length, with the
    periods of every interior f-cycle (module docstring, "(F) beyond the
    audited image length"): `interior_periods_in_box` in the box of
    `stable_radii` on the coefficient-screened tables.

    Raises unless `sigma` is PIP3 (the screen of
    `build_seed_overlap_tables_screened`), when a radius cannot be certified,
    and when more than `max_states` states are visited: a capped walk is not
    a verdict."""
    _require_ternary(sigma)
    var tables = build_seed_overlap_tables_screened(sigma)
    var search = interior_periods_in_box(tables, stable_radii(tables), max_states)
    return FamilyFDecision(
        len(search.periods) == 0, False, search.radii, search.candidates, search.visited, _ascending(search.periods)
    )


def decide_family_f(sigma: List[List[Int]], max_states: Int = GEOMETRIC_F_STATE_CAP) raises -> FamilyFDecision:
    """Property (F): `decide_f_audited` when every image has at most
    `MAX_CERTIFIED_COLUMN_SUM` letters, `decide_f_screened` otherwise. The
    result says which. Raises unless `sigma` is PIP3."""
    if within_audited_domain(sigma):
        return decide_f_audited(sigma, max_states)
    return decide_f_screened(sigma, max_states)


def sigma_contraction_sign(r: Int, s: Int, n: Int, weight: Int) raises -> Int:
    """The exact sign at the Perron root of `sigma_{r,s,n}` of
    `beta^2 - (n+1) beta + weight r = beta (eps + weight r theta - 1)`,
    `eps = beta - n`, `theta = 1 / beta`. Never zero (`beta` is a cubic
    irrational). Raises unless the member is PIP3."""
    if weight < 1:
        raise Error("FC3 family: the contraction weight is a positive integer")
    var field = screened_perron_field3(Mat3(substitution_incidence(sigma_family(r, s, n))))
    return sign_at_perron(field, CubicElt(checked_mul(weight, r), checked_sub(0, checked_add(n, 1)), 1))


def sigma_kappa_sign(r: Int, s: Int, n: Int) raises -> Int:
    """Negative exactly when `kappa = eps + r theta < 1`: the hypothesis of
    the table lemma (every state with `b`, `c` in `{0,1}` reaches a vertex
    state within four steps)."""
    return sigma_contraction_sign(r, s, n, 1)


def sigma_trapping_sign(r: Int, s: Int, n: Int) raises -> Int:
    """Negative exactly when `eps + 2 r theta < 1`: the hypothesis of the
    trapping lemma, which the note shows equivalent to `n >= 3r + s` for
    `n >= r + s + 1`."""
    return sigma_contraction_sign(r, s, n, 2)


def tau_trapping_sign(n: Int) raises -> Int:
    """The exact sign at the Perron root of `tau_n` of `beta^2 - 5 beta - 2 =
    beta^2 (1 - 5 theta - 2 theta^2)`: positive exactly when
    `5 theta + 2 theta^2 < 1`, the hypothesis of the trapping lemma for
    `tau_n`. Raises unless the member is PIP3."""
    var field = screened_perron_field3(Mat3(substitution_incidence(tau_family(n))))
    return sign_at_perron(field, CubicElt(-2, -5, 1))


struct TrapReplay(Copyable, Movable):
    """`states`: the states `(j, (a, b, c))`, `(a, b, c) != 0`, with `b` and
    `c` in the stated ranges. `longest`: the largest number of f-steps one of
    them takes to reach a vertex state. `unresolved`: those that had not
    reached one within the step budget, which is an exhausted budget and not
    a statement about them."""

    var states: Int
    var longest: Int
    var unresolved: Int

    def __init__(out self, states: Int, longest: Int, unresolved: Int):
        self.states = states
        self.longest = longest
        self.unresolved = unresolved


def trapped_transients(
    sigma: List[List[Int]], b_lo: Int, b_hi: Int, c_lo: Int, c_hi: Int, max_steps: Int
) raises -> TrapReplay:
    """Every prototile state `(j, v)`, `v = (a, b, c) != 0`,
    `0 <= <ell, v> < ell_j`, with `b_lo <= b <= b_hi` and `c_lo <= c <= c_hi`,
    followed under `f` (`leftmost_step` on the screened tables) until it is a
    vertex state or `max_steps` steps have been taken. For each `(b, c)` the
    admissible `a` form an integer interval, found by exact monotone scans
    (`ell_0 > 0`). Raises unless `sigma` is PIP3."""
    _require_ternary(sigma)
    if b_lo > b_hi or c_lo > c_hi or max_steps < 1:
        raise Error("trapped transients: empty range or step budget")
    var tables = build_seed_overlap_tables_screened(sigma)
    var cache = Dict[CubicElt, Int]()
    var unit = tables.lengths.at(0)
    var longest_tile = tables.lengths.at(0)
    for j in range(1, ALPHABET):
        if cached_sign(tables, cache, cubic_sub_checked(tables.lengths.at(j), longest_tile)) > 0:
            longest_tile = tables.lengths.at(j)
    var states = 0
    var longest = 0
    var unresolved = 0
    for b in range(b_lo, b_hi + 1):
        for c in range(c_lo, c_hi + 1):
            var base = cubic_add_checked(
                cubic_scale_checked(tables.lengths.at(1), b), cubic_scale_checked(tables.lengths.at(2), c)
            )
            # least a with base + a ell_0 >= 0
            var a = 0
            var x = base
            var scanned = 0
            if cached_sign(tables, cache, x) >= 0:
                while cached_sign(tables, cache, cubic_sub_checked(x, unit)) >= 0:
                    x = cubic_sub_checked(x, unit)
                    a -= 1
                    scanned += 1
                    if scanned > SCAN_CAP:
                        raise Error("trapped transients: the scan for the first state did not terminate")
            else:
                while cached_sign(tables, cache, x) < 0:
                    x = cubic_add_checked(x, unit)
                    a += 1
                    scanned += 1
                    if scanned > SCAN_CAP:
                        raise Error("trapped transients: the scan for the first state did not terminate")
            while cached_sign(tables, cache, cubic_sub_checked(x, longest_tile)) < 0:
                if not (a == 0 and b == 0 and c == 0):
                    for j in range(ALPHABET):
                        if cached_sign(tables, cache, cubic_sub_checked(x, tables.lengths.at(j))) >= 0:
                            continue
                        states += 1
                        var s = OverlapState(0, j, cubic_sub_checked(CubicElt(), x))
                        var steps = 0
                        while not s.shift.is_zero() and steps < max_steps:
                            s = _prototile_child(tables, cache, s)
                            steps += 1
                        if not s.shift.is_zero():
                            unresolved += 1
                        elif steps > longest:
                            longest = steps
                x = cubic_add_checked(x, unit)
                a += 1
                scanned += 1
                if scanned > SCAN_CAP:
                    raise Error("trapped transients: the scan over a tile did not terminate")
    return TrapReplay(states, longest, unresolved)

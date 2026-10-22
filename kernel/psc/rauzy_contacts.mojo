"""Exact contact structure of the Rauzy fractal on T², from the box automaton.

`psc.rauzy_torus` draws the fractal `R = ⋃ R(i)` in the coordinates of
`H = {Σx = 0}`, where `w ∈ Z³` acts as the translation `P(w) = w - |w|₁ f`.
Its lift profile is a finite sample and certifies nothing. This module puts
in its place what the project's overlap automata decide exactly.

* **Overlaps are translates.** An oriented overlap `(i, j, t)` of
  `psc.overlap_seed_patch` has `t = <l, w>` for a unique `w ∈ Z³`
  (`psc.vertex_coincidence.offset_vector`). In `H` it is the pair
  `R(i) + P(w)`, `R(j)`. The potential-overlap window `-l_j < t < l_i` is the
  Siegel--Thuswaldner self-replicating translation condition, and the sign of
  `P(w)` was fixed against the exact sample (evidence README).
* **Contacts are the descendants of cycles.** By the set equation, a point of
  `R(i) + P(w) ∩ R(j)` lies in `h(R(k) + P(w') ∩ R(k')) + c` for a parent
  overlap `(k, k', w')`, so the intersection is nonempty iff `(i, j, w)` has
  an infinite chain of ancestors (the boundary-graph criterion of
  Siegel--Thuswaldner, Mém. SMF 118, 2009, for unimodular `σ`). In the finite
  potential-overlap graph that means: reachable from a cycle. Every cycle
  vertex lies in the box (`BoxCycleContainment`) and the box is closed under
  inflation, so the contacts are exactly the descendants of the box's
  recurrent components, coincidences excluded. This step is cited, not a
  ledger import.
* **Reversal.** Swapping top and bottom maps the potential-overlap graph to
  itself, so the contacts are closed under `(i, j, w) ↦ (j, i, -w)`; the
  kernel checks it and raises on a violation.
* **The seed graph is not evidence.** Its swap seeds are formal pairs: a seed
  `ab | ba` occurs in a tiling only if both words do. On 1368 of the 2628
  unimodular standing specimens some seed-reachable overlap is not a contact
  (specimen 1, `1 2 5`, has no word `01`, and its `(0, 1)` seeds are the
  strays), so seed membership is not recorded.
* **Lattice neighbours.** Contacts with `|w|₁ = 0` translate by
  `P(w) = (w₀, w₁) ∈ Z²`: they are the neighbours of `R` in its `Z²` tiling.
* **Verdict.** The same box decides formal productivity (Theorem Omega,
  `BoxAutomatonCertificate`), which gives pure discrete spectrum
  (`BoxAutomatonPDSCertificate`). For unimodular `σ`, pure discrete spectrum
  is equivalent to covering degree 1 (Ito--Rao 2006; Barge--Kwapisz 2006):
  cited, not a ledger import. Only the box verdict is recorded here.

Every quantity is exact: `S P(w)_i = S w_i - |w|₁ S f_i` is enclosed by the
certified frequency floors of `psc.rauzy_torus`, with width `| |w|₁ |`.
"""

from psc.overlap_obstruction import recurrent_sccs
from psc.overlap_seed_patch import (
    OverlapState,
    SeedOverlapAutomaton,
    SeedOverlapTables,
    build_overlap_graph_from_seeds,
    build_seed_overlap_tables,
)
from psc.perron_field3 import CubicElt
from psc.rauzy_torus import FrequencyFrame
from psc.vertex_coincidence import (
    VERTEX_COINCIDENCE_STATE_CAP,
    VertexCoincidenceVerdict,
    _verdict_on,
    box_radii,
    box_start_states,
    length_matrix,
    offset_vector,
)

struct Contact(ImplicitlyCopyable, Copyable, Movable, Equatable):
    """`R(top) + P(w)` meets `R(bottom)`. `S P(w)_i` lies between `hi_i` and
    `hi_i - mass`, where `mass = |w|₁` may have either sign."""

    var top: Int
    var bottom: Int
    var w0: Int
    var w1: Int
    var w2: Int
    var hi0: Int
    var hi1: Int

    def __init__(out self, top: Int, bottom: Int, w: List[Int], frame: FrequencyFrame):
        var s = w[0] + w[1] + w[2]
        self.top = top
        self.bottom = bottom
        self.w0 = w[0]
        self.w1 = w[1]
        self.w2 = w[2]
        self.hi0 = frame.scale * w[0] - s * frame.f0
        self.hi1 = frame.scale * w[1] - s * frame.f1

    def __eq__(self, o: Contact) -> Bool:
        return self.top == o.top and self.bottom == o.bottom and self.w0 == o.w0 and self.w1 == o.w1 and self.w2 == o.w2

    def __ne__(self, o: Contact) -> Bool:
        return not (self == o)

    def mass(self) -> Int:
        return self.w0 + self.w1 + self.w2

    def reversed(self, frame: FrequencyFrame) -> Contact:
        return Contact(self.bottom, self.top, [-self.w0, -self.w1, -self.w2], frame)

    def is_coincidence(self) -> Bool:
        return self.top == self.bottom and self.w0 == 0 and self.w1 == 0 and self.w2 == 0

    def is_lattice(self) -> Bool:
        """`|w|₁ = 0`: `P(w) = (w₀, w₁)` exactly, a translation of `Z²`."""
        return self.mass() == 0


struct TileContacts(Copyable, Movable):
    """The box verdict and the exact contacts of one substitution."""

    var verdict: VertexCoincidenceVerdict
    var contacts: List[Contact]

    def __init__(out self, var verdict: VertexCoincidenceVerdict, var contacts: List[Contact]):
        self.verdict = verdict^
        self.contacts = contacts^

    def lattice_neighbours(self) -> List[List[Int]]:
        """Distinct nonzero `(w₀, w₁)` over the lattice contacts, first-seen order."""
        var out = List[List[Int]]()
        for c in self.contacts:
            if not c.is_lattice() or (c.w0 == 0 and c.w1 == 0):
                continue
            var seen = False
            for v in out:
                if v[0] == c.w0 and v[1] == c.w1:
                    seen = True
            if not seen:
                out.append([c.w0, c.w1])
        return out^


def _index_of(cs: List[Contact], c: Contact) -> Int:
    for k in range(len(cs)):
        if cs[k] == c:
            return k
    return -1


def cycle_descendants(a: SeedOverlapAutomaton) raises -> List[Bool]:
    """Per state: reachable from (or on) a recurrent component of `a`."""
    if a.capped:
        raise Error("cycle descendants are undefined on a capped graph")
    var mark = List[Bool](length=a.size(), fill=False)
    var stack = List[Int]()
    for comp in recurrent_sccs(a):
        for i in comp:
            if not mark[i]:
                mark[i] = True
                stack.append(i)
    while len(stack) > 0:
        var i = stack.pop()
        for j in a.adj[i]:
            if not mark[j]:
                mark[j] = True
                stack.append(j)
    return mark^


def contacts_of(tables: SeedOverlapTables, box: SeedOverlapAutomaton, frame: FrequencyFrame) raises -> List[Contact]:
    """The non-coincidence descendants of the box's cycles. Raises when they
    are not closed under reversal, which would contradict the criterion."""
    var lengths = length_matrix(tables)
    var mark = cycle_descendants(box)
    var out = List[Contact]()
    for k in range(box.size()):
        if not mark[k]:
            continue
        var c = Contact(box.states[k].top, box.states[k].bottom, offset_vector(lengths, box.states[k].shift), frame)
        if not c.is_coincidence():
            out.append(c)
    for c in out:
        if _index_of(out, c.reversed(frame)) < 0:
            raise Error("the cycle descendants are not closed under reversal")
    return out^


def tile_contacts(sigma: List[List[Int]], frame: FrequencyFrame) raises -> TileContacts:
    """Box verdict and exact contacts from one box build. A capped graph raises:
    a capped run is not a verdict, and its contact list would be incomplete."""
    var tables = build_seed_overlap_tables(sigma)
    var cache = Dict[CubicElt, Int]()
    var verdict = VertexCoincidenceVerdict()
    verdict.radii = box_radii(tables)
    var starts = box_start_states(tables, verdict.radii, cache)
    verdict.starts = len(starts)
    var box = build_overlap_graph_from_seeds(tables, starts, cache, VERTEX_COINCIDENCE_STATE_CAP)
    if box.capped:
        raise Error("the box automaton reached its state cap: no verdict")
    verdict = _verdict_on(box, verdict^)
    var contacts = contacts_of(tables, box, frame)
    return TileContacts(verdict^, contacts^)

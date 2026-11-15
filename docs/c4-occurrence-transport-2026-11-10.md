# C4 affine digit edges and literal finite reachability

**Scope:** the concrete transport continuation after
[PR #533](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/533),
based on `main@666e701d7cffde398e1265dd4ee95becf54fef53`.
The [targeted stop/go review](c4-address-transport-literature-2026-11-10.md)
preceded the new source. Exact-revision compilation, axiom audit and replay
receipts belong to the implementation PR; source statements alone do not
establish that acceptance.

The new [OccurrenceTransport](../proof/PscVerif/PscVerif/OccurrenceTransport.lean)
module supplies two directions of refinement, with different inputs:

1. Literal source and digit occurrences project to the independently
   defined affine digit relation.
2. From an actual source realization, every affine digit edge whose
   descendant tiles have a strict common interior constructs a common
   actual child, its ordinal and the two local occurrences.

Finite packet-state reachability therefore lifts to a coherent **chosen**
address history and an actual `Descendants.Child` path. A diagonal packet
then forces a literal coincident target and yields the existing one-step
newborn conclusion. The statement does not claim that such a productive
packet route exists for every forced crossing.

## 1. Literal source and digit data

`Mark w` contains actual words `before`, `[letter]` and `after` with

```text
w = before ++ letter :: after.
```

Its zero-based index is `before.length`. A source mark `m : Mark w` and a
digit mark `d : Mark (s m.letter)` construct `m.inflate s d`, with prefix

```text
subst s m.before ++ d.before.
```

`Mark.inflate_index` proves the global address equation

\[
  i'=|\sigma(w[:i])|+d.
\]

Every digit is an actual image occurrence. A source image with no letters
has no digit mark. Other images may erase: affine transport and valid
occurrence lookup do not require global nonerasure. The final interior
newborn theorem retains the existing nonerasure hypothesis.

`MarkedPair` keeps both complete physical tracks and their independently
selected marks. It does not identify two occurrences merely because their
letters, residuals, or containing factor labels agree.

## 2. Affine residual and physical sign

The integral convention agrees with
[`target_packets.mojo`](../kernel/psc/target_packets.mojo):

\[
r=\pi(p_{\rm top})-\pi(p_{\rm bottom}),\qquad
r'=M r+\pi(d_{\rm top})-\pi(d_{\rm bottom}).
\]

`parikhZ_subst` derives the integral incidence action from the existing
natural-count substitution theorem. `residual_inflate` proves the affine
identity from the two literal inflated prefixes. `residual_trim` proves
that removing whole balanced prefixes from the tracks preserves the
residual.

For a supplied positive length row, write `offset = ℓ·r`. This is the top
start minus the bottom start. A top-relative point `x` has bottom-relative
coordinate `x + offset`, so strict overlap means

\[
  \exists x:\quad 0<x<L_{\rm top},\qquad
  0<x+\ell\cdot r<L_{\rm bottom}.
\]

`Packet.interior_iff_bounds` proves the equivalent inequalities

\[
  -L_{\rm top}<\ell\cdot r<L_{\rm bottom}.
\]

Both inequalities are strict. Endpoint contact does not justify a common
factor. `MarkedPair.overlaps_iff` derives this relative condition from the
actual global prefix lengths. Swapping physical tracks exchanges the
letters and digits and negates the complete residual; it also exchanges
the two interval lengths.

These finite-word identities require neither Pisot assumptions nor an
independently assumed rational independence of the lengths. They do not
identify zero real offset with zero integral residual. Whenever that
additional conversion is needed, the previously proved
`OccurrenceNewborn.physicalLength_eq_iff` retains the substitution's own
irreducible incidence cubic and nonzero left eigenrow hypotheses.

## 3. Constructing the common child

`DigitStep s p q` is defined solely by the packet's source letters, valid
digit marks in their substitution images, and the affine formula. Its
definition contains no actual-parent or realization witness.

`MarkedPair.localize` uses the new
[OccurrenceAddress](../proof/PscVerif/PscVerif/OccurrenceAddress.lean)
lookup on the actual global positions. The positive-interior condition and
`red_common_factor_lookup` identify one common ordinal in the complete
`Reduction.red`. The returned `Localization` records:

- the exact ordinal and actual child words;
- the two local selected letters, prefixes and suffixes;
- decomposition of each original prefix into the preceding complete
  factors followed by its selected child's local prefix.

The preceding top and bottom factor prefixes are balanced.
`Localization.packet_eq` uses that fact and `residual_trim` to **derive**
packet equality. Residual equality is not an assumed field of the lookup.

`LiftedStep` retains the source block, both digit marks and this localization.
`LiftedStep.top_address` and `LiftedStep.bottom_address` prove the numerical
commuting squares from source index and digit through global image index
to actual factor ordinal and local index. `LiftedStep.digitStep` supplies
forward soundness.

The converse `lift_digitStep` starts with any actual marked irreducible
balanced source and an independently specified affine edge with strict
descendant overlap. It constructs a `LiftedStep`; it does not assume that
the edge already has a common-child realization. The fixed-input
`lift_digits` constructor retains the supplied top and bottom digit marks
definitionally, as recorded by `lift_digits_top` and `lift_digits_bottom`.

## 4. Orientation relative to representatives

The raw path uses physical track order. `orient false` retains a
representative's order and `orient true` swaps it. The associated signs are
`+1` and `-1`.

`child_ordinal_orient` proves that swapping a parent swaps every child at
the same ordinal. `normalized_child_orientation` proves that parent and
child frame flips compose by Boolean XOR, equivalently multiplication of
their signs. `LiftedStep.normalized_target` attaches this result to the
actual selected child: from checked source-frame and representative-child
equalities, it derives the target frame and composed sign.

This works for any supplied representative choice whose literal equalities
hold. It does not implement a graph-state ID assignment or a lexicographic
normalizer in Lean. Raw `AddressedPath` does not store production canonical
IDs or normalization signs; those are related by the separate frame
theorems. Endpoint side, physical track order and newborn side are separate
notions. Track swapping does not change a right-end route into a claim
that its newborn is necessarily `SyncMinus`.

## 5. Finite reachability and newborn extraction

`InteriorStep` combines the independent affine digit relation with strict
overlap of its target. `AddressedPath.cons` retains a `LiftedStep` and starts
the tail at **that exact marked target**. Equal packet labels alone cannot
splice different literal contexts in this witness.

`packet_path_lift` proves that finite `InteriorStep` reachability from any
actual irreducible marked source has a coherent chosen `AddressedPath` to
an irreducible realization of the target. `AddressedPath.child_path`
forgets the marks only after constructing them and yields an actual literal
`Child` path.

Both relations are proposition-valued reachability witnesses. The theorem
does not expose a separately supplied ordered state/digit transcript or a
length-preserving list map. Existential digits are chosen compatibly with
the finite route. Fixed one-step digit preservation is the stronger
interface of `lift_digits` described above.

A `Packet.Diagonal` requires equal selected letters **and zero integral
residual**. In an irreducible balanced realization, the selected prefixes
are balanced. `red_split_at_diagonal` puts the equal-letter singleton in
the complete reduction, while irreducibility says that reduction is the
single parent block. `MarkedPair.diagonal_coincident` therefore derives
coincidence of the parent. It does not assume the containing parent is
already coincident.

`packet_path_literal_target` now returns an actual child path to a
coincidence. `packet_path_newborn` composes that result with the accepted
`child_path_newborn`: for a nonerasing substitution and noncoincident
irreducible source, it returns a reachable noncoincident immediate parent,
its actual coincident child edge, and an interior noninherited cut with
`SyncPlus` or `SyncMinus`.

## 6. Composition with a supplied strict carrier

The separate
[`OccurrenceStrict`](../proof/PscVerif/PscVerif/OccurrenceStrict.lean)
adapter uses the existing `StrictSystem` definition. Its input is a supplied
finite carrier of actual irreducible noncoincident balanced pairs, closed
under every literal child in the complete reduction.

`Realized C p` means that `p` is the projection of actual selected marks in
a member of this carrier. `realized_closed` derives successor closure under
the independent `InteriorStep` relation by constructing the actual child
with `lift_digitStep` and applying the carrier's child closure.
`realized_avoids_diagonal` applies `diagonal_coincident` and the supplied
noncoincidence condition. Thus this realized set is a concrete
successor-closed, diagonal-free region.

`packet_path_mem` transports realization along finite packet reachability,
and `addressed_path_mem` preserves carrier membership along an actual
addressed path. `no_diagonal_route` also gives the direct contradiction:
a diagonal packet route would lift to a literal coincident descendant,
which a strict system excludes. `strictComponent_no_diagonal_route`
specializes this to the existing strict-component interface; strong
connectivity is not needed for this deduction.

The remaining uniform C4 task is to prove that at least one genuinely
forced crossing under the full PIP and hub hypotheses has a productive
route, contradicting this avoiding region. The adapter supplies no such
existence theorem and does not extract a finite strict carrier from a
general substitution failure. It also does not establish completeness of
the production packet graph.

## 7. Verification and remaining interfaces

The affine and sign/overlap layers have narrow pinned Lean checks during
development. Acceptance requires compiling the complete production module
with `OccurrenceAddress` and auditing the full bank at the final revision:

```sh
cd proof/PscVerif
lake build PscVerif.OccurrenceTransport
```

The independent bounded model and source-bound runner are
[`C4OccurrenceBridge.qnt`](../proof/quint/C4OccurrenceBridge.qnt) and
[`check_c4_occurrence_quint.py`](../tools/check_c4_occurrence_quint.py).
Canonical replay uses the existing Mojo packet/address machinery. Controls
must distinguish missing incidence action, missing digit correction,
incorrect residual sign, repeated occurrences, split descendants and
boundary contact. The finite binary/integer-length domain is not a Pisot
corpus or a universal proof.

The formal relation may inflate a coincident block, whereas the canonical
target-packet graph makes such states terminal. Its finite reachability
lifting theorem is therefore not a full refinement of the production
graph's terminal policy, interning, serialization, caps or completeness.
Production `success` also requires an interior left boundary and applies
its configured target-letter or eventual-synchronization filter. Formal
`Packet.Diagonal` is equal selected letters with zero integral residual;
the newborn theorem handles an exterior-left singleton by taking its
interior right boundary and returning `SyncMinus`. These target predicates
are not identified.
Every step present in a formal path still has valid digit marks; reaching
an earlier diagonal does not validate an invalid later digit.

Consistent lifting of arbitrary infinite quotient paths, legal limit
configurations, global G1 extraction and existence of a productive forced
crossing remain separate obligations. General C4, Concentration and PSC are
not promoted by these local and finite-path implications.

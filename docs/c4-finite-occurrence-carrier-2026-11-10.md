# C4 finite actual occurrence carriers and recurrence

The packets realized by a supplied finite carrier of word pairs form a
finite set with an explicit bound. With positive letter lengths satisfying
the exact substitution scaling equations, every geometric interior packet
has an interior digit successor. For an actual strict child-closed carrier,
these successors lift to actual marked children in the same carrier. Every
actual interior marked root therefore reaches a nonempty cycle of compatible
actual marked states.

These are necessary properties of a supplied strict carrier. They do not
exclude one. The new modules are
[`OccurrenceFinite`](../proof/PscVerif/PscVerif/OccurrenceFinite.lean),
[`OccurrenceSuccessor`](../proof/PscVerif/PscVerif/OccurrenceSuccessor.lean), and
[`OccurrenceRecurrence`](../proof/PscVerif/PscVerif/OccurrenceRecurrence.lean).
The [pre-code literature stop/go](c4-finite-carrier-dual-literature-2026-11-10.md)
records the decision to formalize these elementary finite-word consequences,
while keeping the independent [descendant-span route](c4-descendant-span-dual-2026-11-10.md)
separate.

## Work shown

### Assumptions and hypotheses

The alphabet is `Fin 3`. A `WordPair` contains its two complete ordered
words. A `MarkedPair` retains that pair and a genuine letter occurrence in
each word, with its prefix, selected letter, suffix and exact splitting
equation. Its packet is the existing top-letter, bottom-letter and
top-minus-bottom prefix-Parikh residual from `OccurrenceTransport`.

Finiteness needs only a supplied `Finset WordPair`. It does not require
balanced words, nonempty images, a Pisot spectrum or a guessed bound on
residual coordinates. Positive lengths are used to prove that the first
marks of two nonempty words overlap geometrically.

Successor existence uses a substitution `s`, letter lengths `ℓ`, a scalar
`β`, and precisely the equations

\[
  \ell(a)>0,\qquad \beta>0,\qquad
  \operatorname{physicalLength}_{\ell}(s(a))=\beta\ell(a)
  \quad\text{for all }a.
\]

These equations imply nonempty letter images. The theorem needs no separate
nonerasure premise. Positivity alone is insufficient, as the explicit
control below demonstrates.

The recurrence composition additionally supplies the existing
`Psc.StrictSystem.StrictSystem s C`: `C` is finite and nonempty, every
member is an actual irreducible balanced block and is noncoincident, and
every member's actual child lies in `C`. Strong connectivity, legality,
primitivity and irreducibility of the incidence polynomial are not required
for this implication. In applications to C4, those additional hypotheses
remain available for the still-open exclusion argument.

### Derivation / reduction

#### 1. Enumerate actual marks before projecting to labels

For each word `w`, `markAt w i` reconstructs the literal mark at the valid
index `i : Fin w.length`. `mark_index_injective` proves that the index
determines the entire mark: its prefix is `w.take i`, the selected letter
is the indexed letter, and its suffix is `w.drop (i+1)`. The resulting
`markEquiv` identifies actual marks with valid indices.

For a supplied carrier `C`, `Indexed C` enumerates triples

\[
  (T,i,j),\qquad T\in C,\quad i<|T_{\rm top}|,\quad j<|T_{\rm bottom}|.
\]

The map `indexedPair` covers every actual marked member of `C`.
`markedSupport` is its finite image; `packetSupport` is the further packet
image. Their membership theorems identify these sets with the exact actual
definitions, rather than a bounded coordinate approximation. In particular,

\[
  |\operatorname{packetSupport}(C)|
  \le |\operatorname{markedSupport}(C)|
  \le \sum_{T\in C}|T_{\rm top}|\,|T_{\rm bottom}|.
\]

`interiorSupport` and `interiorMarkedSupport` filter these finite sets using
the existing geometric `Packet.Interior ℓ`; their cardinalities satisfy the
same bound. The theorem is a support bound. It does not turn a set of labels
into a weighted list of edge occurrences.

#### 2. Produce a successor from an open overlap

`OccurrenceSuccessor.interiorStep_exists` starts with the open intersection
of the two selected tile interiors. Positive scaling produces a nonempty
open interval in their substituted images. Remove the finitely many prefix
boundaries of the two image words and select a point left over. The literal
weighted-word locator places this point strictly inside a digit tile in
each image. The exact offset/scaling identities give the existing affine
`DigitStep`, and the common point witnesses its target's strict interior.

The [successor note](c4-interior-successors-2026-11-10.md) gives the interval,
boundary-avoidance and affine equations. Boundary contact without an open
intersection is outside this argument.

#### 3. Lift each edge from the actual supplied source

`OccurrenceRecurrence.actual_step_exists` invokes the existing
`OccurrenceTransport.lift_digitStep` on the supplied actual marked source.
The lift retains its digit witnesses, common factor ordinal, target words
and both target marks. Actual `StrictSystem.closed` then puts the child
back into `C`. The target packet remains interior.

`ActualStep s ℓ m n` records the existence of precisely such a `LiftedStep`
whose complete target is `n`. Its `child` and `packet` theorems project to
the actual child relation and interior affine relation, respectively.
It is not defined by equality of packet labels. This is why successive
edges in an `ActualStep` path have compatible actual sources and targets.

The packet support is also successor-closed and diagonal-free, by the
already accepted `OccurrenceStrict` adapter. Its membership interface is
identified explicitly by `packetSupport_iff_realized`.

#### 4. Apply finite recurrence to the actual marked carrier

`finite_serial_recurrent` is the standard finite graph argument. Choose one
successor for each vertex. Two iterates from any root coincide; the
positive difference of their indices gives a nonempty cycle, with a finite
path from the root to that cycle.
Here a cycle means the formal `Relation.TransGen R n n`: a nonempty closed
walk. No simple-cycle certificate or bound on its length is asserted.

`marked_reaches_cycle` applies this argument to the finite subtype of
actual marks in `interiorMarkedSupport C ℓ`, with relation `ActualStep`.
The output includes an actual marked state `n` in `C`, its geometric
interiority and diagonal avoidance, a finite actual path from the supplied
root `m` to `n`, and a nonempty actual cycle from `n` to itself. Projection
of a subtype path preserves each actual edge.

Finally, any strict system supplies a nonempty block. Its first top and
bottom marks have zero residual and positive lengths, hence intersecting
interiors. `strict_actual_cycle` therefore produces at least one such
nonempty actual cycle from the strict-system hypotheses alone plus the
positive scaling equations.

### Evidence and replay

The universal statements use the actual repository definitions and Lean's
finite-type and relation-closure lemmas. There are no new axioms, admitted
proofs or private theorem-facing declarations. Development replay uses the
complete new proof bodies and the complete existing occurrence proofs;
the production imports and isolated whole-bank audit are the acceptance
checks for the integrating PR.

From the repository root:

```sh
cd proof/PscVerif
lake build PscVerif.OccurrenceFinite PscVerif.OccurrenceSuccessor PscVerif.OccurrenceRecurrence
```

The [bounded/native control note](c4-finite-carrier-dual-controls-2026-11-10.md)
records exact fixtures, finite domains and replay commands. The dedicated
C4 workflow runs the new canonical Mojo regression, the extended descendant
mass regression, independent existing Python controls and the full
source-bound Quint runner. The bounded suite contains 28 tests and 12
assertion-failing mutations; infrastructure failure is not a mutation
receipt. Published-revision receipts belong to the integrating PR, not to
the earlier development run or to #534's revision.

### Negative controls

- For `s=1/012/1`, the four ordered strict states are `01/10`, `10/01`,
  `12/21`, and `21/12`. With `ℓ=(1,2,1)` and `β=2`, the indexed carrier
  has 16 marks, 16 packet labels and 12 interior labels. Every interior
  mark admits an actual interior successor, and an ordinal-zero actual
  two-cycle returns `01/10 → 10/01 → 01/10`. This demonstrates that the
  new structural conclusions can hold in a strict non-PIP control.
- For the same substitution and source `01/10`, use the wrong positive
  row `ℓ=(2,1,1)` and source marks `(0,1)`. The source intervals `[0,2]`
  and `[1,3]` overlap, but the unique selected image digits occupy `[0,1]`
  and `[4,5]`. There is no interior successor. This rejects deletion of
  the exact scaling hypothesis while preserving positive lengths.
- Repeated diagonal `00/00` has four indexed marks but only three packet
  labels and one interior label. Packet membership loses occurrence
  multiplicity; it cannot supply a weighted adjacency identity.
- The native two-cycle's geometric overlaps coexist with false native
  `TargetPacket.interior` flags. That flag tests an interior left balanced
  factor boundary; it is distinct from Lean's geometric overlap predicate.

The established productive PIP avoiding cycles and full-rank flat cones
remain controls against concluding either universal path termination or
depth-two synchronization from these structural facts.

### Non-claims / remaining gaps

Actual finite recurrence removes the ambiguity of splicing equal labels
from incompatible word contexts. It still does not construct a shared
legal limit configuration or synchronize two recognizable substitution
hierarchies. Those require additional realization and alignment arguments.

The construction supplies no productive route, no contradiction to an
avoiding cycle and no weighted physical-mass conservation law. In particular,
the forward geometric subdivision convention has not been identified with
the transpose mass-budget convention of `PhysicalMass`; multiplicities and
source/sink orientation must be proved at that interface before reuse.

The independent descendant-span theorem does not supply the nonzero fixed
annihilating row proposed in #461. Neither development closes the uniform
productive forced-crossing theorem, general C4, Concentration, global G1
or PSC. Independent human review remains final validation debt.

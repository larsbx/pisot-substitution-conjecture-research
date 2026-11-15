# C4: local incoming admissibility and actual paired pieces

This continues the [bounded compact-cover construction](c4-bounded-compact-cover-2026-11-11.md)
from merged `main@222ce957cf5ffc85cf482937b735b27e22f46379` (#539).
The [three-source pre-code stop/go](c4-local-admissibility-literature-2026-11-11.md)
records the literature passages and the transferred and missing hypotheses.

**New boundary:** the original literal tile equation gives a complete finite
union over *all selected paired pieces*, before any integral inverse test.
Local lifting of the nonempty pairs suffices to turn this into an actual
integral-occurrence cover. A represented lift for every nonempty pair at
every source in a supplied finite domain gives a cover at every prescribed
finite depth.
An exact, weaker set-cover criterion includes nonintegral pairs as well.

The development contains 35 named Lean proofs in
[`OccurrenceAdmissibility.lean`](../proof/PscVerif/PscVerif/OccurrenceAdmissibility.lean),
a [canonical Mojo constructor](../kernel/psc/c4_local_admissibility.mojo),
and an [independent integer/set oracle](../oracles/python/c4_local_admissibility.py).
It supplies no authentic compact Pisot tile instance of the local lifting
or finite-domain representation hypotheses. It supplies no measure
recurrence, nonunit product-Haar scaling, or strict-cut positivity theorem.
C4, global G1, Concentration, and general PSC closure remain unproved;
[issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
remains open. No governed claim status is changed.

## 1. Literal paired pieces before integral filtering

Let `s` be a substitution on three letters, `M=incidenceZ s`, `G` an
additive commutative group, `A : G →+ G`, `star : Z^3 →+ G`, and
`K_a ⊆ G`. For a packet `p=(i,j,z)`, use the existing convention

\[
E(p)=K_i\cap(K_j+\star z).
\]

The hypothesis `TileEquation s A star K` is the original literal union

\[
K_i=\bigcup_{s(a)=P\,i\,S}(A K_a+\star\pi(P)).
\]

Every marked decomposition includes its parent letter and its position
in the actual word. The new type `SelectedPair s p` retains two such full
marks, selecting `i` and `j`, without testing an inverse equation. For
`d=(a,P,i,S;b,Q,j,T)`, define

\[
C_d=(A K_a+\star\pi(P))\cap
     (A K_b+\star(z+\pi(Q))).
\]

Intersecting the two original tile unions proves

\[
\boxed{E(p)=\bigcup_{d:\mathrm{SelectedPair}(s,p)} C_d.}
\]

`overlap_eq_iUnion_pairPiece` needs only `TileEquation` and the indicated
additive structures. It needs no injectivity of `A` or `M`, commutation,
integral lifting, topology, or measure. Each raw pair is also proved to be
a subset of the original overlap.

If `d_i` counts all incoming literal marks selecting `i`, then
`selectedPair_card_eq` proves the exact count `d_i*d_j`.
`selectedPair_card_le` proves the bound `D^2`, where
`D=sum_a length(s(a))`. `pairAddress_injective` proves that the two parent
letters and two numeric positions recover the complete selected pair.
These statements hold even for singular incidence.

The finite index and its union answer different questions. Equal paired
sets, equal ancestor packets, or equal image masks never identify two
literal occurrences. Set-cover equalities authorize no deletion from a
counting or measure sum.

## 2. Local integral lifting and retained histories

The exact inverse equation of `d` is

\[
M y=z+\pi(Q)-\pi(P).
\]

`pairLift` turns a supplied integer solution into the existing
`InverseOccurrence s p (a,b,y)` record using those same marks. Under

\[
A\text{ injective},\qquad A(\star y)=\star(My)\quad(y\in\mathbb Z^3),
\]

the existing occurrence-piece identity gives

\[
C_d=A E(a,b,y)+\star\pi(P).
\]

The new contracts keep the missing geometry explicit:

| Contract | Exact quantifier at source `p` | Consequence with the tile/action hypotheses |
| --- | --- | --- |
| `LocalAdmissible` | Every nonempty `C_d` has an integral solution `y` | Complete union over actual integral inverse occurrences |
| `RepresentedAt S p` | Every nonempty `C_d` has some integral solution with `(a,b,y) in S` | Complete retained one-step cover |
| Representation at every `p in S` | The previous contract holds at every intermediate source | Retained cover through every prescribed finite depth |

`localAdmissible_iff_nonintegral_empty` is an equivalence: all selected
nonintegral pairs must be empty. Similarly,
`representedAt_iff_unrepresented_empty` says that every pair with no
retained integral lift must be empty. These are useful exclusion
interfaces, not assertions that the exclusions hold in the intended
geometry.

`overlap_eq_iUnion_inverse_of_local` removes the previous need for global
integral-range reflection at sources where local admissibility is supplied.
It does not require injective incidence for its set identity. The full
integral incoming type may nevertheless be infinite for singular `M`.

`finite_restrictedHistory` proves finiteness of the retained history type
using only finite `S` and the finite full-mark fibres at fixed endpoints.
It remains valid for singular incidence. The history type is the previous
dependent `OccurrenceCover.History`: it keeps every intermediate packet,
both literal marks, and their order. Under representation at every source
in `S`, `overlap_eq_iUnion_restrictedHistory_of_representedAt` proves the
cover at each finite depth. A premise at the initial source alone does not
justify the same premise at a later source.

### Some represented lift versus every represented ancestor

With an injective integral incidence action, the new theorem
`representedAt_iff_local_and_all_ancestors` proves equivalence with local
admissibility plus representation of every nonempty actual inverse
ancestor. Incidence injectivity cannot be dropped from this general
some-lift-to-all-ancestors implication: it identifies
the represented solution with the displacement in any other actual record
for the same pair. The converse implication needs no incidence injection.
The singular control in Section 5 refutes deleting this hypothesis.

## 3. The exact retained-set criterion

Let `R_S(p)` be the existing union of actual inverse pieces whose ancestors
belong to `S`. Its inclusion in `E(p)` follows from the original tile and
action hypotheses. The raw-pair union gives the exact criterion

\[
\boxed{E(p)=R_S(p)\quad\Longleftrightarrow\quad
       \forall d,\ C_d\subseteq R_S(p).}
\]

This is `overlap_eq_restricted_iff_all_pairs`. It requires neither local
admissibility nor global range reflection. Its quantifier includes *every*
raw pair, including pairs with no integral inverse. The more general
`overlap_eq_set_iff_pairPiece_subset` needs only `TileEquation` and an
explicit premise `R subset E(p)`.

The criterion is weaker than `RepresentedAt`: an omitted nonempty piece
may already be contained in the union of retained pieces. It is a criterion
for equality of sets, not a multiplicity-preserving replacement of an
incoming-occurrence sum. A test restricted to omitted *integral* pieces is
unsound unless a complete integral cover has already been established.
The zero-integral-occurrence control below makes that stronger test pass
vacuously while the actual overlap remains nonempty.

## 4. Sound profile exclusions and the nonunit carrier issue

Let `rho : G →+ R`, `B : R →+ R`, and `C_a ⊆ R` satisfy

\[
\rho(Ax)=B(\rho x),\qquad \rho(K_a)\subseteq C_a.
\]

`image_pairPiece_subset` proves

\[
\rho(C_d)\subseteq
 (B C_a+\rho(\star\pi(P)))\cap
 (B C_b+\rho(\star(z+\pi(Q)))).
\]

If this outer projected intersection is empty, the actual `C_d` is empty.
The proof does not need injective `rho`, finite `R`, or integral-incidence
injection. `localAdmissible_of_projected_exclusions` applies this certificate
to every nonintegral pair. `representedAt_of_projected_exclusions` applies
it to every pair with no retained integral lift.

| Proposed exclusion | Justified conclusion |
| --- | --- |
| Exact nonintegral inverse equation alone | No integral record; no emptiness conclusion |
| Empty projected pair with proved commutation and actual tile enclosure | Actual paired piece is empty |
| Nonempty projected pair | Inconclusive about actual intersection |
| A stable box enclosing the entire actual set, with strict separation | Sound emptiness exclusion, using the previous `OccurrenceCover` enclosure lemmas |
| Boundary contact, an undersized box, sampled points, or a resource cap | No geometric exclusion |
| Outside the supplied finite domain | No geometric exclusion without a retained-cover/emptiness premise |

`isCompact_pairPiece` proves compactness when the tiles are compact, `A`
is continuous, and the ambient topological group is Hausdorff. Compactness
does not imply admissibility, domain representation, or positive measure.

The new global obstruction is also explicit in Lean:

\[
A\text{ surjective}\quad\Longrightarrow\quad
\bigl(\mathrm{ReflectsIntegralRange}\iff
       M:\mathbb Z^3\to\mathbb Z^3\text{ surjective}\bigr).
\]

For nonunit incidence, a surjective ambient action therefore cannot supply
the old global reflection premise. The point is to prove the relevant
tile-local restriction or change to an authenticated admissible translation
module, not to assume global reflection on unrestricted completion fields.

There is a related residue caveat. A product of characteristic-zero fields
is divisible as an additive group. Every additive map from that whole group
to a finite group is zero: if `n` annihilates the target, write `x=n*y` and
obtain `rho(x)=n*rho(y)=0`. This elementary observation is explained in the
pre-code note; it is not one of the new Lean declarations. A nontrivial
finite residue test for the authentic model must instead use a proved
support module/valuation ring, or projection to a local field followed by
authenticated module-coset enclosures. The relevant translations and action
must stay in that carrier. No such authentic instance is supplied here.

## 5. Reproducible finite controls

The canonical fixture models use finite discrete cyclic groups. All sets,
maps, tile equations, commutation, action injection, and profile enclosure
premises are exhaustively checked. They are compact abstract interface
models, not primitive irreducible Pisot substitutions or Rauzy-tile instances.

In the table, `L`, `R`, and `C` mean local admissibility, represented-pair
coverage, and retained set coverage on the declared domain. `all` means
the whole cyclic group; packets are accompanied by their track swaps.

| ID | Substitution; carrier/action/star; tiles | Sources/domain | Raw pairs | L / R / C |
| --- | --- | --- | ---: | --- |
| 0 | `00/1/2`; `Z/3`, `A=id`, `star=z1+z2`; all tiles full | `(1,2,0)` and swap | 2 | 1 / 1 / 1 |
| 1 | `00/11/22`; `Z/3`, `A=2`, `star=z0+z1+z2`; all full | `(0,1,0)` and swap | 8 | 0 / 0 / 1 |
| 2 | Same as 1 | `(0,1,e2)` and swap | 8 | 0 / 0 / 0 |
| 3 | `1/2/0`; `Z/3`, `A=id`, coordinate-sum star; all full | `(0,1,0)` and swap | 2 | 1 / 0 / 0 |
| 4 | `01/1/2`; `Z/3`, `A=id`, `star=0`; all full | `(0,1,0)` and swap | 4 | 1 / 0 / 1 |
| 5 | `00/1/2`; `Z/6`, `A=id`, `star=z1+z2`; `K_a={a,a+3}` | Domain: `(1,2,e0)`, `(1,2,-e1)` and swaps. Additional queries: `(1,2,e0-e1)` and swap | 6 | 1 / 1 / 1 on domain only |

Model 0 has `M=diag(2,1,1)`. At `e0`, `A(0)=star(e0)` but there is no
integral lift. Global reflection fails while both domain sources have
their unique nonempty pair represented.

In model 1, each source has four literal pairs and all four paired sets are
the whole group. Only the zero/zero positional pair is integral; its piece
already covers the overlap. The other three addresses remain in the
inventory despite their set-theoretic redundancy. In model 2 every inverse
equation has odd third coordinate, so the complete integral union is empty
while the original overlap and every raw paired piece have three points.

Model 3 has a nonempty integral ancestor outside the domain, so local
lifting alone does not give a retained cover. Model 4 also has a nonempty
outside ancestor, but its set is redundant with a retained piece. This
separates the sufficient represented-pair contract from exact set coverage.
A further regression uses a diagonal source for `00/11/22`: two retained
positions share both their ancestor and nonempty image, and are counted twice.

Model 5 uses the authenticated quotient `Z/6 → Z/3`, `C_a={a}`. At
displacement `e0`, a nonintegral pair is excluded by disjoint projected
profiles. At `-e1`, the integral self-ancestor has nonempty overlap. The two
additional queries at `e0-e1` have nonintegral, nonempty paired pieces and
are explicitly outside the accepted domain; the computation must not
promote the domain verdict to them. Replacing the profiles by valid larger
sets makes some tests inconclusive. Replacing them by a false enclosure is
rejected before any coverage verdict.

### Singular control

For `s=0/0/0`, all incidence columns equal `e0`. Take `G=Z/3`, `A=id`,
`star=0`, `K_0=G`, and `K_1=K_2=empty`. The original tile equation holds.
At `p=(0,0,0)`, only the parent-zero/parent-zero selected pair is nonempty.
It has the represented lift `y=0` in `S={p}` and the distinct lift
`y=(1,-1,0)` outside `S`. Both actual inverse pieces are full and nonempty.
These two explicit integer witnesses refute an all-ancestor representation
conclusion without incidence injection. The generic nonsingular constructor
refuses this model; the control does not pretend to enumerate its infinite
integral fibre.

### Mandatory inverse-closed, forward-leaking control

The existing `forward_leak_control()` is replayed unchanged. For
`00/11/22` and `S={(0,1,0),(1,0,0)}`, integer parity forces each actual
integral inverse ancestor to stay in `S`. The forward positional pair
`(1,1)` from `(0,1,0)` has displacement `(1,-1,0)` and leaves `S`. With the original
physical calibration it has positive interval length. Across both sources,
the receipt is `full=4, retained=2, positive_exits=2`.

This is a physical-length diagnostic only. No interval length is assigned
to a compact group piece or substituted for compact-overlap Haar measure.
Inverse closure remains insufficient for forward completeness or deletion
of a positive forward contribution.

## 6. Packet, bounds, independence and replay

The fixed protocol is `c4-local-admissibility-v1`. It contains six complete
models, 16 source rows, 30 literal pairs, three basis probes per nonsingular
model, the singular witnesses, and the original forward-leak control.
Every image word, source, domain packet, digit prefix, equation right-hand
side, integral verdict, ancestor, and actual/profile set is serialized.

Each `pair` has 22 fields after its model/id:

```text
source topDigit bottomDigit rhs[3] integral parentTop parentBottom y[3]
inDomain topImage bottomImage pairedSet ancestorOverlap inverseImage retainedSet
projectedTop projectedBottom projectedPair
```

For a nonintegral pair, `y`, ancestor-overlap, inverse-image, and retained-set
fields are zero sentinels controlled by the integral flag. They do not
declare an empty actual paired set. The 20-field `row` separately reports
raw/integral/retained unions, complete occurrence counts, local/represented/
set-cover flags, duplicate retained images, redundant omitted nonempty
pieces, and projected exclusions.

The group modulus is at most 15; source/domain inventories at most 64;
image length at most 27; coordinates at most 64 in absolute value. Existing
bounded-constructor limits are 4,096 states, 20,000 histories, 200,000
candidates, and 100,000 expanded letters. Limits are refusals, not pruning
rules. Complete basis-probe rows obey those limits too. A regression has
every individual basis lift in bounds but another selected mark in the
same probe outside the bound; that whole probe must refuse.

The Mojo path reuses the existing bounded constructor and vendored checked
integer/adjugate arithmetic. Python independently rescans prefixes, uses
permutation determinants and Cramer's rule, and computes `frozenset`
images/intersections/unions instead of native bitmasks. It compares the
entire ordered packet, rejecting missing, duplicated, substituted, unknown,
or altered records. Public guards remain active under `python -O`.

From the repository root:

```bash
./tools/check_lean.sh
python tools/make_proof_bank.py --check
python -m pytest --assert=plain -o addopts='' -q tests/test_c4_local_admissibility_oracle.py
```

For canonical native replay, install the pinned environment first, then:

```bash
cd kernel
pixi install --locked
export MODULAR_HOME="$PWD/.pixi/envs/default/share/max"
export MODULAR_TELEMETRY_ENABLED=0
.pixi/envs/default/bin/mojo run -I . tests/test_c4_local_admissibility.mojo
.pixi/envs/default/bin/mojo run -I . c4_local_admissibility.mojo > /tmp/c4-local-native.txt
cd ..
PSC_LOCAL_ADMISSIBILITY_NATIVE_OUTPUT=/tmp/c4-local-native.txt \
  python -m pytest --assert=plain -o addopts='' -q tests/test_c4_local_admissibility_oracle.py
python -O oracles/python/c4_local_admissibility.py \
  --native /tmp/c4-local-native.txt --output /tmp/c4-local-receipt.json
```

[`c4-local-admissibility.yml`](../.github/workflows/c4-local-admissibility.yml)
checks the exact PR head, tree, clean initial checkout and SHA-256 source
inventory before replay; runs the locked native tests/driver and independent
oracle; rechecks source identity; and publishes the native packet and
receipts. The full canonical Lean/axiom audit is a separate required gate.
The introducing PR records the accepted revision and observed workflow
results. Source review, reduced-import development checks, and oracle-only
tests are not substitutes for those receipts. The finite numeric fixtures
are checked by native/oracle replay; they are not new closed Lean evaluations.

## 7. Minimal remaining authentic geometric obligation

For a faithful integral incoming cover in the intended compact model, the
unproved local lemma is:

> At every admitted genuine source, a nonempty selected paired piece in
> the authenticated compact tile geometry has an admissible integral
> inverse displacement, with its exact two literal marks preserved.

To use the proposed finite constructor, strengthen the conclusion to a
represented ancestor in `S`, or prove local lifting and complete
representation separately. Under incidence injection this represents every
nonempty actual inverse ancestor. At finite depth, the premise must hold
at each intermediate source. If the faithful translation module is larger
than `Z^3`, its representation and record type must first be authenticated;
this development does not assume that the integral encoding suffices.

If only a set cover is sought, the exact and weaker missing fact is
containment of every raw paired piece in the retained union. Neither
condition follows from inverse closure, boundedness, internal graph
completeness, an arithmetic nonintegrality test, or compactness alone.

Authenticated stable enclosures or support-module residue profiles can
discharge individual exclusions, but their enclosure and carrier premises
remain geometric obligations. After coverage, product-Haar scaling,
measure additivity with the appropriate multiplicity/boundary conditions,
and positivity at strict-cut roots are still needed. The supplied proofs
and controls do not close any of these remaining C4 dependencies.

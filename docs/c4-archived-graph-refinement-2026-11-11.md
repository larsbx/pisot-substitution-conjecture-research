# Source-bound refinement of the archived named overlap graphs

## Scope and status

Baseline: main `99748ca29ee4bc3daf259da1fdabaffa3d5d4793`, merging
[#549](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/549)
with accepted proof head `0e6db2d6edd37b87dbb6a42e42783170906ac33a`.
The separately committed [primary-source gate](c4-archived-graph-refinement-literature-2026-11-11.md)
precedes this implementation.

This increment connects the original sharp-box, rooted inverse graph
construction to the actual named prefix geometry. It supplies a complete
sharp-digit proof, actual-prefix box argument, exact matrix-square residue
decoder, and a conditional literal-table refinement and nullity consumer.
Canonical Mojo and an independent Python oracle reconstruct both archived
finite objects with complete addresses and ancestry.

**The finite payload is not yet deserialized into the Lean table proof
terms.** The theorem states those remaining finite obligations explicitly.
Native/oracle success is not called a kernel proof of the concrete graph
instance. Exact published-revision acceptance is recorded in the PR and
[evidence directory](../evidence/c4-archived-graph-refinement-2026-11-11/README.md);
source statements and successful local development are distinguished from
that acceptance. No governed claim is promoted.

## Assumptions and hypotheses

The named substitutions stay exactly

- `sigma_0 = 1/021/001`;
- `sigma_1 = 1/012/001`.

They have the same incidence matrix, but their original order, actual
period-two word and all occurrence marks remain separate. The ambient
space is the same `Stable × H_M` constructed by the accepted code; no
adelic or tiling identification is introduced. Its measure is coordinate
Lebesgue measure times normalized additive Haar measure on `H_M`.

The three original roots are `(0,1,0)`, `(0,2,0)` and `(1,2,0)`, together
with their track swaps for the ordered ancestry statement. The certificate
rate is indexed by the original source: `99/20` for fixture zero and
`101/20` for fixture one. The later `24,12` eighteen-source certificate
remains separate.

A finite table presented to the final theorem must supply:

1. `TableBinding`: each certificate slot has its actual parent letters,
   both positions in `sigma^2`, raw integral ancestor and normalization
   orientation. Rows are complete on the ordered lift, address keys are
   injective and stored IDs denote distinct swap orbits. Its degrees and
   targets are definitionally the same as the numerical certificate's.
2. `CandidateClosed`: every actual integral inverse candidate passing the
   proved sharp-box test is in the ordered lift. This quantifies beyond
   already stored endpoints. `candidateClosed_iff_decoded` proves this is
   equivalent to `DecodedCandidatesClosed`, a finite check over complete
   literal selected pairs using the unique exact inverse. The final named
   consumers accept this explicitly finite formulation.
3. For the rooted-domain equivalence, the exact three root IDs and
   `TableDiscovery`: every nonroot has a literal slot from an earlier
   state. No circular or self-justifying ancestry record is admitted.
4. An accepted positive integer potential with the source's rate and
   denominator twenty.

All actual geometric admission, tile-equation, action, matrix-adic
range-reflection, compactness and Haar-scaling inputs are discharged by
named Lean theorems. The remaining table obligations are the precise
boundary for a subsequent concrete Lean payload importer.

## Derivation / reduction

### 1. Authenticate every literal sharp digit

`NamedSharpDigits` defines an integer prefix summary `(total,lower,upper)`.
Concatenation combines two summaries by

```text
total = left.total + right.total
lower = min(left.lower, left.total + right.lower)
upper = max(left.upper, left.total + right.upper).
```

A structural induction proves that this encloses every prefix of the
actual concatenated word. Iterating summaries in each original
substitution's literal order is proved equal in scope to every prefix of
`iterateImages sigma 12`. The final word endpoint is included as well,
which strengthens the proper-prefix requirement.

Kernel arithmetic checks all three parent words for both sources at the
four chart endpoints

```text
1,000,000*x0 - 828,911*x1
1,000,000*x0 - 828,912*x1
1,000,000*x2 - 440,619*x1
1,000,000*x2 - 440,620*x1.
```

The corresponding absolute bounds are `4,600,000` and `2,800,000`.
The existing authenticated real bounds on `a,b`, together with the
nonnegative prefix count `x1`, give

```text
|W(prefix)_0| <= 23/5,       |W(prefix)_1| <= 14/5
```

for **every** actual block-twelve mark. There is no sampled digit set,
floating computation, native-reduction axiom or supplied numeric premise.
The proof uses twelve levels of compositional summaries rather than a
quadratic scan of long word prefixes.

### 2. Derive the original box for every actual prefix and tile point

`NamedSharpBox` uses the existing proved absolute entry bounds

```text
|B^12| <= [[19/40, 2/5], [3/20, 7/20]].
```

These slightly wider bounds already suffice for the archived radii:

```text
[[19/40,2/5],[3/20,7/20]] * (16,8) + (23/5,14/5)
  = (77/5,8) <= (16,8).
```

The actual literal address theorem gives every output prefix a parent
ordinal no greater than its own ordinal. Strong induction handles a
smaller parent. In the self-parent case the two coupled coordinate
inequalities themselves imply the bounds by linear elimination. Thus no
boundedness or compact maximum is assumed to prove boundedness.

Closed coordinate inequalities then pass from every actual prefix point
to the closure defining the actual tiles. Therefore `Q=[-16,16]×[-8,8]`
is authenticated for the same geometry used by #549. An overlap witness
is a difference of two enclosed tile points, so its stable translation
lies in `Q-Q=[-32,32]×[-16,16]`.

The strict integer interval test in the historical graph is defined
literally in Lean. Both rational endpoint values must lie strictly beyond
the same boundary to reject. This implies actual overlap emptiness.
Boundary contact and uncertain interval separation stay represented.

### 3. Authenticate the nonunit residue decoder

For the original named matrix,

```text
M^2 = [[1,3,1],[1,3,3],[1,1,1]],   det(M^2)=4,
adj(M^2) = [[0,-2,6],[2,0,-2],[-2,2,0]].
```

`NamedInverseDecoder` proves that native modulo-four divisibility is
exactly the integral-image condition. Equivalently, all coordinates of

```text
(3*z2-z1, z0-z2, z1-z0)
```

are even, and their halves give the unique integral preimage. This is
valid for negative integers too. In particular `(1,1,1)` is a genuine
image with preimage `(1,0,0)`; coordinatewise evenness of `z` would be the
wrong test.

For literal top and bottom prefixes `p,p'`, the same proof binds

```text
M^2 * z_new = z + p' - p.
```

The existing original matrix-adic range-reflection theorem proves that a
failed residue test removes an empty paired cylinder. Integer division by
itself is not treated as a geometric exclusion.

`NamedArchivedGraph.decodedCandidate_of_occurrence` then proves that every
actual inverse occurrence is exactly the candidate decoded from its full
selected pair. Conversely, an accepted residue constructs that occurrence
with the same original marks. Thus checking every finite selected pair,
and requiring every admitted decoded candidate in the ordered table,
is **equivalent** to unrestricted `CandidateClosed`. This is the precise
finite closure contract for the eventual payload importer; it does not
assume a bound on arbitrary integer offsets or inspect only stored edges.

### 4. Refine normalized rows to actual covers

`ArchivedGraphRefinement` binds a table's slots directly to the existing
`OccurrenceGraphBinding.Slot`. It proves that exact rows enumerate actual
incoming occurrences, preserving their raw parent and both full marks.
Parallel endpoint labels remain different slots.

For a normalized target, the affine translation depends on the swap bit:

```text
unswapped target: topPrefix
swapped target:   current.delta + bottomPrefix.
```

The existing paired-piece identity proves this as equality of sets, not
merely equality of scalar measures. Complete rows, sound admission and
candidate closure then give the exact union of original overlap pieces.
No desired set-cover equation is supplied as a numerical-certificate
hypothesis.

Completeness is propagated to every intermediate ancestor at every finite
history depth. Conversely, earlier-index discovery records prove that
stored states really come from the roots, with whole-path swap transport.
The resulting equivalence is

```text
p in orderedLift(table) AND actualOverlap(p) is nonempty
  iff
p is an original literal inverse ancestor of an archived root
  AND actualOverlap(p) is nonempty.
```

This is a rooted representation theorem. It does not identify the table
with every element of `strictPackets`, and it does not assert that any
strict overlap has positive Haar measure.

### 5. Feed the original contraction consumer

`NamedArchivedGraph` combines the complete digit proof, sharp admission
soundness and literal-table bridge. Every piece uses the already proved
original product-Haar scaling. With `v_i` the finite actual overlap measure,

```text
beta^2 * v_i <= sum_over_positional_slots(v_target).
```

The authenticated real root bracket proves `103/20 < beta^2`. The accepted
integer potential is passed to the existing
`OverlapContraction.Certificate.null_of_cover`, with the same degree and
target functions used by the literal slots. The resulting theorem gives
nullity of represented overlaps and the exact three roots when the
remaining concrete table proof terms are supplied. The rooted representation
then extends nullity to every original literal inverse ancestor at arbitrary
finite depth; geometrically empty ancestors need not be stored in the table.

The finite weighted-maximum argument is standard. This increment's
contribution is the preserved-source and occurrence-level connection to
these original geometric objects.

## Evidence and replay

The new canonical Mojo checker reconstructs the original `sigma^2` words,
all fifteen complete block positions per source, and all incoming pairs.
Each position retains the parent, flat block index, outer/local two-level
indices, selected letter and complete prefix. Each retained edge records
both positions and the swap bit. Every nonroot has a first-discovery slot
from an earlier state. A separate forward computation checks the full
ordered inventory with multiplicity.

The independent Python oracle uses rational Gaussian inversion and literal
prefix rescans. Full packet parity compares every source, state, address,
slot, ancestry record and potential. Both original graph hashes are
reproduced, rather than replaced by new address hashes.

| Original source | States | Positional slots | Ordered lifted positions | Rate | Historical graph SHA-256 |
| --- | ---: | ---: | ---: | --- | --- |
| `1/021/001` | 7,150 | 34,826 | 69,652 | `99/20` | `23f85af92c327a64f70983db990753a84cd1489e3c72c3047e51f14e97afce6e` |
| `1/012/001` | 7,083 | 34,853 | 69,706 | `101/20` | `a63d544b25b5f7146abbd25f1960fed77f85584a1f20957b5869bea30b389256` |

The [native/oracle receipt](../evidence/c4-archived-graph-refinement-2026-11-11/native-oracle/receipt.json)
records exact source hashes, historical and addressed graph digests, rates,
root weights and all observed oracle mutations. Local native controls
reject 24 mutation attempts; the independent oracle rejects 30. Nine new
Python tests pass with the actual native packet. Maximum first-discovery
depth is thirteen in both finite graphs; the formal history theorem is
not bounded to thirteen.

Canonical replay:

```bash
./tools/check_lean.sh
python tools/make_proof_bank.py --check
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_archived_graph_refinement.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_archived_graph_refinement.mojo) > /tmp/c4-archived-native.txt
PSC_ARCHIVED_GRAPH_REFINEMENT_NATIVE_OUTPUT=/tmp/c4-archived-native.txt python -m pytest -q tests/test_c4_archived_graph_refinement_oracle.py
python oracles/python/c4_archived_graph_refinement.py --native /tmp/c4-archived-native.txt --controls
```

The focused workflow binds the published head and uploads the complete
98,184-line native packet plus receipts. The existing isolated-source
Lean workflows compile the complete proof bank and audit every compiled
declaration against the established axiom allowance. Local cached probes
are development evidence only. Failed, interrupted and resource-killed
attempts are retained separately from successful acceptance.

## Negative controls

Direct Lean controls and independent executable mutations cover omitted
positional edges, duplicated slots, reversed inverse directions, wrong
track-swap orientation, wrong boxes, substituted source words sharing the
same incidence, incorrect period, nonintegral residue admission, altered
exclusion counts, missing intermediate ancestry and graph/domain mismatch.
The integer interval tests also retain exact box-boundary contacts.

A particularly sharp countercontrol removes a repeated positional edge:
the numerical inequality becomes easier and still passes, while the
source-bound row checker rejects it. Swapping an orientation bit or
removing a discovery witness can likewise preserve every numerical
weight inequality. These are structural checks, not merely certificate
rejection caused by a worse rate.

The existing inverse-closed but forward-leaking `4 / 2 / 2` calibration
and nonempty-null/zero-deficit boundaries remain in the accepted proof
bank. No inverse-completeness statement is used as forward conservation.

## Non-claims / remaining gaps

1. **Concrete Lean payload import remains.** The entire original finite
   graphs and positive potentials are independently replayed in native
   and oracle code, but their serialized payloads are not instantiated as
   Lean `TableBinding`, `CandidateClosed`, exact root/discovery and
   accepted-certificate proof terms. Source-bound finite replay and a
   proved conditional consumer do not silently close this last trust
   boundary. An efficient proof-producing decoder should enumerate all
   literal candidate pairs, use the authenticated exact inverse and sharp
   admission predicates, and retain every original slot and discovery
   record. It should reject the same countercontrols under kernel
   evaluation. Checking only state counts or graph hashes would not do.
2. The rooted table is not all noncomputable `strictPackets`. An all-domain
   statement needs a separate coverage argument, if required by a later
   consumer.
3. Nullity is not emptiness, and a conservative component does not supply
   positive strict-root Haar measure. The strict positive-measure bridge
   remains independent.
4. There is no promotion of C4, BH, A1', G1, Concentration, pure discreteness
   or the general Pisot Substitution Conjecture. Independent human review
   remains pending and does not block correctly scoped research progress.

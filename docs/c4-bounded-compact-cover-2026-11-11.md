# C4: bounded literal histories and conditional compact-piece covers

Base: `main@67921a747a16b6998156f807f7f391ecfa3fcd88`, after the
integration of #537 and #497. The [three-primary-source stop/go](
c4-compact-cover-literature-2026-11-11.md) preceded implementation.
No governed claim is promoted. C4, global G1, Concentration and PSC remain
open; independent human review remains final validation debt.

## 1. What advances beyond the previous union theorem

`OccurrencePiece.overlap_eq_iUnion_inverse` already derived the union over
all integral incoming ancestors from the original tile equation and explicit
ambient-space hypotheses. The new [OccurrenceCover module](
../proof/PscVerif/PscVerif/OccurrenceCover.lean) turns that union into a
bounded, occurrence-preserving construction without assuming that the full
ancestor graph is finite.

For any prescribed depth, injective integral incidence gives finitely many
actual incoming histories. Each history retains its entire sequence of
ancestor packets and both literal positions at every level. Its affine
piece is the image of its terminal overlap under the correctly composed
prefix translation. Under the existing geometric hypotheses, these pieces
cover the starting overlap. Under additional topological hypotheses they
are compact.

Restricting this construction to a particular finite graph is a different
statement. The new proofs give both the exact set-cover criterion and a
stronger local sufficient condition. Neither an internally complete row nor
an operational coordinate cap supplies that condition.

| Layer | Result | Additional boundary |
| --- | --- | --- |
| Literal finite construction | Every actual integral incoming mark pair is expanded through the declared depth, including ancestors outside a supplied diagnostic domain. | Nonsingular incidence and explicit resource budgets; a cap raises rather than returns a partial certificate. |
| Lean full-history cover | The starting overlap equals the union of its actual depth-`n` history pieces. | Original tile equation, injective commuting internal action and integral-range reflection. |
| Lean compactness | Each supplied overlap and history piece is compact. | Compact tiles, a Hausdorff topological additive group and continuous internal action. |
| Lean finite restriction | Omitted-piece containment is necessary and sufficient for set equality; omitted emptiness or nonempty-ancestor representability suffices. | These are geometric premises for the chosen finite domain, not conclusions of finite row equality. |
| Canonical Mojo / independent integer oracle | Four bounded inventories, actual iterated-word addresses, exact residue refusals and reproducible stronger-statement counterexamples. | The numeric packet is not a closed Lean evaluation, and finite fixtures do not instantiate authentic Pisot compact tiles. |

## 2. The bounded object and its exact addresses

Fix a ternary substitution `s`, incidence `M`, and a current packet
`p=(a,b,z)`. An incoming occurrence consists of an ancestor `u=(A,B,y)`,
both actual decompositions

\[
s(A)=P\,a\,S,\qquad s(B)=Q\,b\,T,
\]

and the integral equation

\[
My=z+\pi(Q)-\pi(P).
\]

`Incoming s p` is the dependent pair of this ancestor and its complete
`InverseOccurrence` record. Its key consists of the two source letters and
two full marks. If `y -> M y` is injective, equal keys force equal integral
ancestors. Since the literal words have finitely many positions,
`incomingFintype` constructs a finite incoming type. No globally bounded
offset or stable box is assumed.

`History s 0 p` has one empty history. `History s (n+1) p` consists of one
incoming occurrence followed by a depth-`n` history at that ancestor. This
recursive type is finite under the same incidence-injectivity assumption.
For total digit count `D=sum_A length(s(A))`, the cardinal-bound proofs give
at most `D^2` branches per node and `(D^2)^n` histories. Finiteness and these
bounds are derived rather than supplied as a constructor cap.

The history address is the full list

```text
[(ancestor1, topPosition1, bottomPosition1), ..., (ancestorn, topPositionn, bottomPositionn)]
```

`historyAddress_injective` proves that this address identifies the history.
Equal endpoints are not equal histories. With successive prefixes `P_i,Q_i`,
the composed vectors are

\[
T_h=\pi(P_1)+M\pi(P_2)+\cdots+M^{n-1}\pi(P_n),
\quad
B_h=\pi(Q_1)+M\pi(Q_2)+\cdots+M^{n-1}\pi(Q_n).
\]

The proofs bind them to the exact powered equation

\[
M^n y=z+B_h-T_h.
\]

The native constructor separately authenticates `T_h` and `B_h` against
the complete literal words `s^n(A)` and `s^n(B)`: their coordinate sums are
the selected numeric positions, their vectors equal the actual prefix
Parikh counts, and the letters at those positions equal the root letters.
A correct vector equation alone does not substitute for those checks.

## 3. From records to compact pieces, with hypotheses visible

In an additive commutative group `G`, let `A:G ->+ G` be the internal action,
`star:Z^3 ->+ G` the integral translation homomorphism, and `K_a` the tiles.
Use the existing positive-prefix overlap convention

\[
E(a,b,z)=K_a\cap(K_b+\operatorname{star}(z)).
\]

The nested affine map of a history is proved equal to

\[
f_h(x)=A^n x+\operatorname{star}(T_h).
\]

Its exact set piece is `f_h(E(terminal(h)))`. The first occurrence is the
outermost affine map, so the order of matrix powers and prefixes matters.
The construction uses ordered packets without canonicalizing them. Thus no
orientation bit is silently lost. A future serialized canonical binding
must still use the already proved orientation-dependent translations of
`OccurrencePiece.slot_piece_eq_stored` at every normalization.

The full bounded cover theorem assumes:

1. `Function.Injective A`;
2. `A(star z)=star(M z)` for every integral vector;
3. `TileEquation`, the original complete incoming literal tile unions;
4. `ReflectsIntegralRange`: an ambient preimage of `star z` under `A`
   implies an integral preimage of `z` under `M`.

The previous one-step theorem supplies an actual incoming piece containing
each point. Induction repeats that decomposition at its preimage. The
opposite inclusion follows because every actual piece lies in its current
overlap. Consequently,

\[
E(p)=\bigcup_{h:\mathrm{History}(s,n,p)} f_h(E(\mathrm{terminal}(h))).
\]

The identity itself does not require a finite index. Integral incidence
injectivity makes this a **finite** cover at every prescribed depth. With
compact `K_a`, continuous `A`, and a Hausdorff topological additive group,
the overlap is a compact intersection and each history piece is a continuous
image of a compact set. These results do not construct the intended compact
matrix-adic space or authenticate its tiles as substitution prefix tiles.

## 4. Exactly what finite pruning requires

For a supplied finite packet set `S`, let `R_S(p)` retain **all** actual
incoming occurrences whose ancestor belongs to `S`. This preserves every
parallel mark pair within the represented domain.

The exact set-cover criterion is

\[
E(p)=R_S(p)
\quad\Longleftrightarrow\quad
\forall u\notin S,\ \forall e:p\leftarrow u,
\quad A E(u)+\operatorname{star}(\pi(P_e))\subseteq R_S(p).
\]

It permits an omitted nonempty piece that is already covered by retained
pieces. Such set redundancy does **not** justify removing its multiplicity
from an adjacency matrix or an additive recurrence.

A stronger convenient sufficient condition is

\[
\forall u,\ \forall e:\mathrm{InverseOccurrence}(s,p,u),
\quad u\notin S\Longrightarrow E(u)=\varnothing,
\]

equivalently the representability condition that every nonempty incoming
ancestor lies in `S`. An image is empty exactly when its domain is empty;
this particular equivalence does not need injectivity of the affine map.
`overlap_eq_iUnion_restrictedHistory` extends the sufficient condition to
all bounded histories provided it holds at **every represented intermediate
source**, and the starting source is represented.

There is a useful distinction about closure. Genuine inverse closure under
**all** actual integral occurrences does imply this incoming set cover once
the tile/action/range hypotheses are available. It does not imply forward
closure. Closure under rows that were already pruned by a constructor is
weaker and does not discharge the representability premise.

### Sound exclusions and remaining geometric instances

| Proposed exclusion | Formal sufficient reason | What must still be established for the historical graph |
| --- | --- | --- |
| Invalid selected letter, position or prefix | The record is not an actual occurrence. | Full literal authentication, retaining the mark identity. |
| No integral inverse solution | The paired piece is empty under `ReflectsIntegralRange`, as in `OccurrencePiece`. | Construct the intended compact matrix-adic range instance. The new residue-detector lemma reduces this to annihilation of the internal-action range and an exact integral-kernel implication. |
| Stable enclosure separation | `K_a subset B_a` for every entire tile and `E_B(u)=empty` imply `E_K(u)=empty`. | A certified enclosure of the authentic tiles, correct coordinates and strict separation. Boundary contact is retained. |
| A strictly separating real coordinate | Bounds on both actual tiles and `upper(top)<lower(bottom)+coordinate(star(delta))`. | A proved projection/chart and those global bounds; sampled extrema do not suffice. |
| Physical strip/carrier rejection | No general compact-emptiness theorem is supplied by a physical interval test. | Actual ancestry, positive exact scaling and the compact stable/chart/carrier implications. |
| State, coordinate, word or history cap | Inconclusive computation; the run raises. | No cap can become an emptiness proof. |

For #497's graph, a precise next sufficient local lemma is: **at each
represented source, every nonempty actual paired piece has an integral
ancestor whose canonical representative occurs in the serialized domain**.
The existing exact literal row binding then provides its incoming record,
including both positions and the required orientation translation. This
lemma must be proved for the actual compact tiles; it is not inferred from
the new finite fixtures or from the old internal adjacency agreement.

## 5. Canonical finite construction and independent replay

The [canonical Mojo module](../kernel/psc/c4_bounded_cover.mojo) expands
every integral incoming occurrence breadth first. A node stores its root,
parent history node, depth, both digit IDs, full ordered ancestor packet,
composed top and bottom prefixes, membership in the supplied domain, and
whether the **entire** path has remained inside that domain. All integral
ancestors are expanded even after leaving the domain. Nonintegral candidates
are serialized separately; they are arithmetic refusals, not unqualified
geometric emptiness claims.

The format is `c4-bounded-cover-v1`. Limits are depth 6, image length 27,
integral coordinates `[-64,64]`, 4,096 distinct states, 20,000 history nodes,
200,000 candidates and 100,000 letters in an iterated word. Singularity and
resource exhaustion raise. Determinant/adjugate inputs are bounded by the
image limit; subsequent integer arithmetic uses the existing checked
vendored kernels. No vendored arithmetic is modified.

The [independent integer oracle](../oracles/python/c4_bounded_cover.py)
rebuilds literal prefixes by rescanning words and solves each equation by
Cramer's rule with a determinant computed from signed permutations. It
independently expands every positional history and compares the complete
ordered serialization. Public rejection guards remain active under
`python -O`. A missing nonintegral refusal, substituted same-endpoint
history, forged prefix, duplicated record or undeclared control is rejected.

| Fixture | Presentation and inverse depth | Nodes | Candidate pairs | Nonintegral refusals | Terminal histories | Histories entirely in diagnostic domain | Repeated terminal packets |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | `00/11/22`, distinct-letter roots and swaps, depth 3 | 8 | 24 | 18 | 2 | 2 | 0 |
| 1 | `00/11/22`, diagonal root, depth 3 | 15 | 28 | 14 | 8 | 8 | 7 |
| 2 | `01/1/2`, distinct-letter roots and swaps, depth 2 | 12 | 10 | 0 | 6 | 2 | 0 |
| 3 | Actual `sigma^2` for `sigma=11/210/10`, depth 2 | 128 | 558 | 432 | 114 | 0 | 30 |

The last fixture's terminal addresses belong to `sigma^4`, since each
inverse step uses the squared presentation. Its diagnostic domain consists
only of the two roots, **not** the full historical graph. The 122 outside
nodes expose that intentional restriction; they do not refute completeness
of #497's substantially larger domain. Totals are 163 nodes, 620 candidate
pairs and 130 terminal histories.

The complete fixture packet contains 24,607 bytes and 862 lines, with
SHA-256 `318d8f210399bb1acfadb63a4100b1bbe2294d2194db4a6ddb3ba56aa82d167b`.
The new native regression reaches ten altered-record controls, nine
input/budget refusals and all eight compact/set/forward-leak controls.
The focused independent suite has 25 tests when supplied the native packet.

## 6. Counterexamples to stronger statements

- **Inverse closure is not forward completeness.** For `00/11/22` on
  `{(0,1,0),(1,0,0)}`, parity forces the only integral incoming digits at
  each root to be `(0,0)` with zero ancestor residual. Forward `(1,1)`
  reaches an unrepresented packet with residual `e0-e1` (or its swap) and
  positive physical interval mass one. Across both roots, full/retained
  physical masses are `4/2` with two positive exits. This is the mandatory
  reducible nonprimitive control, not a PIP counterexample or compact loss.
- **Repeated endpoints do not identify occurrences.** At the diagonal root
  for the same substitution, depth three has eight literal histories with
  the same endpoint and eight distinct prefix positions `0..7`.
- **Compactness does not supply range reflection.** In the finite compact
  group `Z/3`, set `A(x)=2x`, `star(z)=sum(z) mod 3`, and every tile equal to
  the whole group. The action is injective, commutes with `M=2I`, and the
  actual `00/11/22` tile equation holds. At `p=(0,1,e2)`, all four candidate
  right-hand sides have odd third coordinate: there is no integral
  incoming occurrence, although the overlap and every paired piece contain
  all three points. Omitting range reflection makes the full union false.
- **Physical exclusion is not compact emptiness.** With the identity
  substitution, identity action, the same `star` and full `Z/3` tiles,
  all base algebraic/range/tile hypotheses hold. The packet with residual
  `2e0` has zero physical interval mass under unit lengths and three compact
  overlap points.
- **Internal completeness does not give coverage.** For `1/2/0` in that
  finite group with identity internal action, represent `(0,1,0)` and its
  swap. The unique actual incoming ancestor of `(0,1,0)` is `(2,0,0)`, outside
  the domain. The internal row is exactly empty while the overlap has three
  points. Incidence is unimodular, so range reflection is available.
- **Omitted emptiness is sufficient but not necessary for set coverage.**
  For `01/1/2`, identity action, `star=0` and full `Z/3` tiles, the packet
  `(0,1,0)` has two actual incoming occurrences. Their ancestors are itself
  and `(0,0,(1,-1,0))`; both pieces are the whole group. Retaining just the
  first ancestor preserves set coverage and loses one occurrence.
- **An undersized enclosure and boundary contact cannot justify deletion.**
  In the identity finite-group model, the false enclosure `{0}` rejects a
  translated overlap that actually has three points. The closed exact
  integer enclosures `[0,1]` and `[1,2]` meet at `1`; a non-strict separation
  test would incorrectly delete that point. No continuum measure is
  attributed to the integer-set control.

These finite compact-group models test the explicit abstract interfaces.
They are not authentic Pisot prefix-tile instances and do not claim to
refute an implication with the full standing PIP hypotheses.

## 7. Replay and acceptance

```sh
python tools/make_proof_bank.py --check
./tools/check_lean.sh
cd kernel
pixi run --locked mojo run -I . tests/test_c4_bounded_cover.mojo
pixi run --locked mojo run -I . c4_bounded_cover.mojo > /tmp/bounded-cover-native.txt
cd ..
PSC_BOUNDED_COVER_NATIVE_OUTPUT=/tmp/bounded-cover-native.txt python -m pytest --assert=plain -o addopts='' -q tests/test_c4_bounded_cover_oracle.py
python -O oracles/python/c4_bounded_cover.py --native /tmp/bounded-cover-native.txt --output /tmp/bounded-cover-receipt.json
```

The [dedicated workflow](../.github/workflows/c4-bounded-cover.yml) installs
the complete locked environment, binds the exact head/tree and source
digests before execution, compares every native record independently, and
checks source immutability afterward. The existing fresh isolated whole-bank
Lean/axiom audit is the production proof gate. Development compiles, local
extracted compiler packages and pending hosted jobs are not credited as
that full acceptance. Published-revision results belong in the implementation
PR after observation.

## 8. What this does not establish

The bounded cover has explicit ambient and tile hypotheses. The authentic
nonunit compact representation, its range detector, original prefix-tile
equations and the historical finite constructor's exclusions still require
their geometric instances. There is no claim of a globally finite inverse
domain merely because each finite level is finite.

An equality recurrence for compact overlap measure additionally needs
measurability, the correct nonunit product-Haar scaling, and the necessary
measure-disjointness of distinct occurrence pieces. Positive compact
measure at a represented strict-cut root remains separate. Set coverage
and physical interval positivity supply none of these measure conclusions.
No losing compact source, governed C4 promotion, global G1 or general PSC
closure is inferred.

# C4 inverse occurrences: finite control inventory

Date: 2026-11-10. The
[literature stop/go](c4-inverse-occurrence-literature-2026-11-10.md)
preceded this implementation. These controls accompany the
[formal inverse-occurrence adapter](c4-inverse-occurrence-2026-11-10.md).
They certify their declared finite inputs, not universal C4 or a compact
inverse-overlap domain.

## 1. Representations and exact domains

Both implementations use the Lean convention
`p=(a,b,r)` with **top prefix minus bottom prefix**. Every digit edge retains
the two actual positions `i,j`. Its child is

\[
q=\bigl(\sigma(a)_i,\sigma(b)_j,
Mr+\pi(\sigma(a)_{<i})-\pi(\sigma(b)_{<j})\bigr).
\]

The independently checked inverse predicate verifies the selected letters,
valid position bounds, and the equation

\[
Mr=q.r+\pi(\sigma(b)_{<j})-\pi(\sigma(a)_{<i}).
\]

It does not divide by `M`, assume unimodularity, or identify distinct digit
positions. Track swap exchanges both source letters **and** both indices,
and negates the integral residual. A diagonal packet means equal letters
and the zero integral vector, not merely zero physical displacement.

The canonical native regression is
[`test_c4_inverse_occurrence.mojo`](../kernel/tests/test_c4_inverse_occurrence.mojo).
It reuses `AffineTraceTables`, the production incidence action and prefix
Parikh tables, `prefix_difference3`, and the actual `canonical_pair` rule
from `c4_pair_overlap_graph`. Its fixture loops use bounded integers with
starting coordinates in `[-2,2]`, image length two, and at most two forward
steps. These test-local operations are far below `Int` limits. No new
rational type, graph engine, or geometric certificate is introduced.

The independent specification is
[`C4InverseOccurrence.qnt`](../proof/quint/C4InverseOccurrence.qnt).
Its explicit finite quantifiers are exhausted under the TypeScript backend:

| Domain | Exact scope |
|---|---|
| Binary substitutions | Each of `sigma(0)` and `sigma(1)` is one of `00,01,10,11`; `sigma(2)=00`: 16 substitutions |
| Parent packet inputs | Four ordered source-type pairs and 25 residuals `(x,y,0)`, `x,y in [-2,2]`: 1,600 substitution/packet inputs |
| One-step occurrences | Four ordered index pairs per parent: 6,400 occurrences |
| Two-step histories | Four further index pairs per child: 25,600 complete two-step histories |
| Strict non-PIP fixture | `sigma=1/012/1`, length row `(1,2,1)`, scale two; the four literal word pairs `01/10`, `10/01`, `12/21`, `21/12` give 12 positive packet labels in six free swap orbits |
| Induced subdomains | All 64 unions of those six free orbits, including the empty domain; every actual digit edge whose two endpoints lie in the chosen domain is retained |
| Mixed fixed/free fixture | `sigma=00/00/00`; ordered states `(0,1,0)`, `(1,0,0)`, `(0,0,0)`; six distinct occurrence edges |
| Inverse-closed, forward-leaking fixture | `sigma=00/11/22`; domain `{(0,1,0),(1,0,0)}`; both target roots, nine candidate parent type pairs, 125 residuals in `[-2,2]^3`, and four digit choices: 9,000 candidate incoming occurrences |

The native control additionally authenticates the **existing** nonunit
adjugate/divisibility arithmetic on the production source `1/021/001` at
step two. It checks every ordered pair of actual positions in the three
second-iterate images, for residuals `0` and `(1,-1,1)`. The sum of those
image lengths is 15, so this is `2*15^2=450` inverse reconstructions. The
determinant of `M^2` is four. All genuine reconstructed numerators divide
exactly by four, while at least one unit-coordinate input fails that
divisibility condition. This control does not authenticate stable boxes,
all inverse pieces, a compact set, or the historical graph's completeness.

## 2. Actual edge inventories and orbit counts

The finite counting tests build edges from the displayed substitution and
supplied packet domain. An edge carries `(parent,i,j,child)`, so equal
endpoint labels at different positions remain separate edges. For every
swap-closed domain, the exact edge map is

\[
(p,i,j,q)\longmapsto(p^{\mathrm{swap}},j,i,q^{\mathrm{swap}}).
\]

The tests check its full image membership and uniqueness. They then count
outgoing and incoming occurrences at **every** representative, verify that
both counts are constant on each orbit, and check
`m_i*T_ij=m_j*F_ji`. Every free orbit has size two, making `T_ij=F_ji` valid.
The full strict fixture has a nonempty transition inventory, preventing a
vacuous all-zero transpose check. A subdomain is only an induced finite
inventory: omitted outside edges do not become geometrically impossible.

The mixed fixture exhibits two separate positive occurrences `(i,j)=(0,0)`
and `(1,1)` with exactly the same endpoints. Its canonical orbit order is
the free `(0,1,0)` orbit followed by the fixed `(0,0,0)` orbit. Thus

\[
m=(2,1),\qquad
F=\begin{pmatrix}0&2\\0&2\end{pmatrix},\qquad
T=\begin{pmatrix}0&0\\4&2\end{pmatrix}.
\]

The weighted correspondence holds, whereas the unweighted transpose
identity fails. Deduplicating endpoints changes the count two to one.
Deleting one member of a swapped edge pair destroys both edge-swap closure
and representative uniformity in the strict fixture. Deleting the swapped
state from a domain instead leaves a size-one fiber for a packet that is
not fixed, so the free-orbit size-two conclusion cannot be invoked.

## 3. Geometric and algebraic countercontrols

Three controls preserve distinctions needed by the Lean hypotheses:

- A diagonal parent under `sigma=00/00/00` has the off-index child
  `(0,0,-e_0)` at `(i,j)=(0,1)`. This child has zero mass and is not
  diagonal. Positivity of the child overlap is necessary for the
  diagonal-descendant conclusion.
- For `sigma=1/012/1`, parent `(0,0,(2,0,-2))`, and positive but incorrect
  lengths `(2,1,1)`, the parent has zero mass while its sole child has mass
  one. The exact image-length equations fail. Correct lengths `(1,2,1)`
  give parent mass one and child mass two. Positivity of an arbitrary
  length row does not prove interior pullback.
- With unit lengths, `(0,0,(1,-1,0))` has zero scalar displacement and
  positive overlap mass, but its integral residual is nonzero and its
  track swap is distinct. No Perron independence or integral equality is
  silently inferred from scalar cancellation.

The one-step tests preserve all four ordered digit choices, including
zero-mass boundary contacts. The two-step ancestry test considers every
declared digit history: positive final overlap forces positive intermediate
and parent overlap; a nondiagonal final packet additionally forces both
ancestors to be nondiagonal and nonfixed.
Universal finite-path induction is a Lean obligation, not a conclusion
from this depth-two test.

### Inverse closure does not supply forward closure

The reducible nonprimitive source `sigma=00/11/22` has incidence `2I`,
unit lengths and scale two. Take the swap-closed domain
`D={(0,1,0),(1,0,0)}`. For target `(0,1,0)`, the selected-letter equations
force the parent types to be `(0,1)`, and the inverse equation is

\[
2r=j e_1-i e_0,\qquad i,j\in\{0,1\}.
\]

Coordinate parity forces `i=j=0` and `r=0`. The swapped target has the
swapped argument. This elementary parity derivation has no residual cap;
the finite tests independently check all 9,000 displayed candidate
occurrences and find exactly the two predicted incoming edges.

Thus this domain is inverse-closed, yet the forward `(i,j)=(1,1)` child of
`(0,1,0)` is `(0,1,e_0-e_1)`, outside `D` and of mass one. The full row has
mass two, while the retained row has mass one. This distinguishes inverse
closure from forward conservation without contradicting the complete
strict-support theorem from PR #536. It does not supply a PIP geometric
domain, a compact-overlap cover, or a C4 loss witness.

## 4. Quint assertions and mutation binding

The runner
[`check_c4_inverse_occurrence_quint.py`](../tools/check_c4_inverse_occurrence_quint.py)
pins Quint 0.33.1, snapshots the exact source, checks the ordered test
inventory, and requires every listed run to execute. Each mutation must
reach its named assertion and fail with `QNT508`; a parser/type error,
timeout, missing test, or successful mutant refuses the acceptance receipt.
The runner records the Git head/tree, source and runner hashes, initial and
final dirty state, every mutant hash, and a final revision/source recheck.
It implements provenance orchestration only; the mathematics runs in Quint.

| Test | Guarded contract |
|---|---|
| `domainCountTest` | Exact enumerated domain sizes |
| `literalInverseIdentityTest` | All 6,400 forward occurrences satisfy the independent incoming equation |
| `incomingMarkGuardsTest` | Selected letters, actual position bounds, and exact digit identity |
| `swappedLiteralDigitsTest` | Swap exchanges indices as well as labels/residuals and is involutive |
| `interiorPullbackTest` | Positive child implies positive parent under exact scaling |
| `diagonalInteriorDescendantsTest` | Positive digit of a diagonal parent selects the same position and remains diagonal |
| `boundaryDiagonalCountercontrolTest` | Boundary contact does not satisfy the positive-child conclusion |
| `wrongScalingPullbackCountercontrolTest` | Wrong positive lengths fail the scaling premise and can reverse interior containment |
| `swapFixedIffDiagonalTest` | Integral packet fixed points are exactly diagonals |
| `scalarZeroIsNotFixedTest` | Zero physical displacement alone does not identify a fixed packet |
| `finiteTwoStepAncestryTest` | Every bounded positive path to a nondiagonal target has nondiagonal, nonfixed ancestors |
| `actualFreeDomainSwapCountsTest` | Actual strict-domain edge bijection, representative uniformity, weights and transpose |
| `allSwapClosedSubdomainsTest` | The same conclusions for all 64 induced swap-closed subdomains |
| `missingSwapEdgeCountercontrolTest` | Omitting an edge's mate destroys symmetry and uniformity |
| `actualMixedOrbitWeightsTest` | Actual mixed orbit sizes require weighted counts |
| `repeatedOccurrenceIdentityTest` | Parallel literal occurrences cannot be replaced by endpoint support |
| `nonSwapClosedDomainCountercontrolTest` | A missing swapped state prevents the size-two fiber conclusion |
| `inverseClosedForwardLeakTest` | An actual inverse-closed non-PIP domain can omit positive forward occurrences |

Thirteen separately bound weakened variants reverse the inverse prefix sign,
ignore selected letters, leave digit indices unswapped, omit the incidence
action, ignore the residual in diagonality, count boundary contact as
positive, ignore exact scaling, ignore edge-swap closure, deduplicate
outgoing endpoints, reverse incoming-count direction, force every orbit
weight to two, ignore domain-swap closure, and identify inverse closure
with positive forward closure.

## 5. Replay and acceptance boundary

```sh
python tools/check_c4_inverse_occurrence_quint.py --output /tmp/c4-inverse-occurrence-quint
cd kernel
pixi run --locked mojo run -I . tests/test_c4_inverse_occurrence.mojo
```

The development Quint replay passed all **18 tests and 13 expected
assertion-failing mutations**. Its receipt records a dirty development
checkout and is not an exact published-head receipt. Local native execution
has not been credited; the repository's pinned hosted Mojo job supplies
native acceptance. The implementation PR records the final exact revision,
hosted receipts and full Lean/axiom audit separately.

No control promotes a finite test to a universal theorem, proves compact
overlap coverage or positive measure, justifies geometric deletion of an
occurrence, supplies nonunit Haar scaling, or creates a losing vertex in
the conservative complete strict support. C4 and PSC remain open.

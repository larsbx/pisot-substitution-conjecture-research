# Corrected neutral-rank obstruction: sharp source budgets and stronger controls

**Status:** Local research-review candidate. This note proves a conditional
finite-graph upper bound, identifies the additional hypotheses needed for
its application to a strict component, and records exact counterexamples
to two proposed intermediate shortcuts. It does not exclude all literal
strict components. Universal C4 and PSC remain open; no governed claim
status changes. Independent human review is pending. Publication and
merging await the user's approval.

[Literature stop/go](c4-neutral-rank-literature-2026-11-17.md) ·
[Source hashes, commands and local evidence](../evidence/neutral-rank-obstruction-2026-11-17/README.md)

## Work shown

### Assumptions and hypotheses

#### Exact source revisions

The local integration base is
`1cf7a6ccac6b20957e153cd8e7f6fd09bb594368`. It combines the literal
constructor with the merged endpoint-alphabet correction; it is not a
published result.

| Input | Exact head | Merge / scope |
| --- | --- | --- |
| [PR #601](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/601), seam correction | `f5e2aab7d434f24dcbe618d4948984daa1e1a123` | Merged as `2d831230c9b5a2f7b21165df6756532b3f598e37`; conditional spectral identification and exact seam-cycle inputs |
| [PR #602](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/602), literal occurrence constructor | `cbb8c6c64b56bcce60c2e6031da7acb9ffc5b41d` | Draft input; bounded independent source-word identities, not strict-component realization |
| [PR #603](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/603), alphabet scope | `8d546126ebc33feac2ba9712345e087ee6cadfe1` | Merged as `9dffd8ad19085c61e211eee85645e7f5e1ab8d09`; no-two-cycle simplification only on at most three letters |

#### What transfers to an actual strict component

The finite graph theorem below is independent of the Pisot setting. Its
application to the spectral identity retains the following separate
hypotheses and previously written arguments.

1. **Standing geometry.** The source is a primitive irreducible ternary
   Pisot substitution, with unit incidence matrix `M`, a positive Perron
   length row, and the normalized BBK common-fibre interpretation of
   integral relative starts. Irreducibility supplies the rational
   independence needed to identify physical shared cuts with equal-Parikh
   cuts. Unit incidence supplies the torus normalization used in the
   periodic-pair argument.
2. **Actual literal system.** A strict system is a finite nonempty set of
   unequal irreducible balanced pairs, closed under *all* actual
   irreducible factors of their substituted words. An abstract child
   matrix does not supply this condition. Source legality for the chosen
   recurrent carrier must be obtained in the sink/joining realization
   argument; it is not an automatic consequence of a single balanced pair
   or of its tensor equations.
3. **Rank-two realization.** Coincidence rank two and that strict system,
   through [Theorem W](c4-rank-two-wall-2026-11-16.md), give the unique
   compact minimal joining `Z`, its primitive swap-closed bigon system `B`
   for the original substitution, and common-cut coding. The
   [overlap-return note](c4-periodic-overlap-returns-2026-11-17.md) identifies
   its unique aligned nonproductive overlap sink `C`.
4. **Complete occurrence data.** `A_C` uses the positive-width physical
   child intersections with original source ordinals, repeated occurrences,
   integral offsets, complete rows and track-swap compatibility. Physical
   first and last choices are taken in the original rows. The seam set
   consists of births inside those rows, closed under last/first
   inheritance; shared seams remain shared.
5. **Joint legality and trace transfer.** The completeness argument for
   that seam set uses realization in `Z`, inflation invariance and compact
   minimality. The ordinary and signed trace identities of the
   overlap-return note hold at every positive power, with the common-cut
   endpoint correspondences. Finite power sums then give nonzero
   *algebraic* eigenvalue multiplicities, as in
   [the seam-spectrum note](c4-one-track-seam-spectrum-2026-11-17.md).
6. **Actual first defect.** The rank comparison uses the first nonzero
   defect of this `B`, its intertwiner with `N`, and the hypothesis that
   the entire image has neutral weight `(m,m,m)`. It does not substitute
   an ambient tensor-space dimension for the image rank.

An aligned nonproductive sink is a finite necessary object; the repository
also gives a written sink-to-strict-system construction. The bounded
constructor and the finite sink checks do not themselves machine-check
that geometric construction or the rank-two assumption. Likewise, two
endpoint cells separately belonging to `C` do not by themselves establish
that their ordered adjacency is jointly legal in `Z`.

The #602 constructor independently authenticates source occurrences,
prefix equations, integral interior positions, endpoints and ordered seams
on its declared bounded inputs. Its four productive controls do not supply
any of the missing strict-realization or arbitrary-degree defect premises.

### Derivation / reduction

#### 1. Preserve the actual rank and the neutral sign

Write `N` for the strict bigon occurrence matrix and `N^-` for its
track-swap odd sector. If the first nonzero defect has degree `3m` and
only weight `(m,m,m)`, put

\[
\varepsilon=(\det M)^m\in\{1,-1\},\qquad
r=\operatorname{rank}D_{3m}\ge1.
\]

The first-defect transport identity and the scalar action on its image
give `D_(3m) N^- = epsilon D_(3m)`. Consequently

\[
r\le\dim\ker\bigl((N^-)^{\mathsf T}-\varepsilon I\bigr)
\le m_\varepsilon(N^-).
\tag{1}
\]

The first inequality is the row-space inclusion supplied by the actual
intertwiner. The second distinguishes geometric from algebraic
multiplicity. For degree three, the existing Lean declaration
`StrictSystem.deg23_iii` in
[`StrictSystem.lean`](../proof/PscVerif/PscVerif/StrictSystem.lean)
proves `1 <= rank Q3 <= 2` under its strict-system, primitivity,
irreducibility and Pisot hypotheses. Two is an upper bound, not the
required rank. Thus corrected multiplicity zero excludes any nonzero
neutral image, whereas corrected multiplicity one still permits rank one.
The declaration was inspected, not rebuilt in this session.

The #601 trace identity supplies

\[
m_\varepsilon(N^-)=m_\varepsilon(A_C^-)+b_\varepsilon(C),
\tag{2}
\]

where `b_(+1)=b_1` and `b_(-1)=b_2`. It does not identify Jordan blocks or
transfer geometric multiplicity.

#### 2. Decompose the seam graph by interior-state orbits

Let `E=ER(sigma)` be the connected source eventual-range graph and `F`
its endpoint automorphism. Let `I` be the complete finite set of periodic
integral interior states of the other track, with permutation `f`.
The seam-spectrum embedding places the cyclic one-track seam graph
equivariantly inside `E x I`.

Let `I_C` be the subset actually represented by cyclic germs of the
strict carrier. It is a union of `f`-orbits. For one such orbit `O`, of
length `q`, choose a state `i`. The slice `S_i` of the seam graph is a
nonempty `F^q`-invariant subgraph of `E`. It can be disconnected.

The action around the orbit is induced from the `q`-step action on this
slice. Thus, for `epsilon` equal to either sign and
`delta=epsilon^q`, its contribution to the correction is exactly

\[
b_\varepsilon(O)
=m_\delta(F^q\mid H_1(S_i;\mathbb C))
-m_\delta(F^q\mid H_0(S_i;\mathbb C)).
\tag{3}
\]

Indeed an eigenvalue of the one-step induced action is `epsilon` exactly
when the corresponding `q`-step eigenvalue is `epsilon^q`. All the graph
actions here are finite-order permutations; this reduction introduces no
Jordan-block hypothesis.

#### 3. A sharp bound for a represented orbit

Define the source-orbit budget

\[
B_\varepsilon(q)
=m_{\varepsilon^q}(F^q\mid H_1(E;\mathbb C))
-\mathbf1_{\varepsilon^q=1}.
\tag{4}
\]

**Theorem.** For every represented orbit,
`b_epsilon(O) <= B_epsilon(q)`.

**Proof.** Graph inclusion injects `H_1(S_i)` into `H_1(E)` equivariantly:
graphs have no two-dimensional boundaries. Since `S_i` is nonempty and
`E` is connected, the equivariant map `H_0(S_i) -> H_0(E)` is surjective,
and `H_0(E)` is one copy of the trivial representation. Its
`delta`-multiplicity is therefore at least `1` if `delta=1`, and at least
zero otherwise. Apply these two inequalities to (3). The full slice
`S_i=E` attains the bound. This proof uses no graph connectedness
assumption on `S_i`. QED.

The equivariant graph chain exact sequence gives an executable formula:

\[
B_\varepsilon(q)
=m_{\varepsilon^q}(F^q\mid\mathbb C^{E^1})
-m_{\varepsilon^q}(F^q\mid\mathbb C^{E^0}).
\tag{5}
\]

A permutation cycle contributes one to the `+1` multiplicity, and one
to the `-1` multiplicity precisely when its length is even. Powering a
cycle of length `a` by `q` gives `gcd(a,q)` cycles of length
`a/gcd(a,q)`. Formula (5) therefore needs only exact integer cycle data.
For `epsilon=+1`, (4) subtracts one for every represented interior orbit.
For `epsilon=-1`, it subtracts one for every represented *even* orbit.

#### 4. Unknown represented orbits require positive parts

If precisely `I_C` is known, summing gives

\[
b_\varepsilon(C)\le\sum_{O\subseteq I_C}B_\varepsilon(|O|).
\tag{6}
\]

One cannot replace `I_C` by all of `I` in this signed sum: an absent orbit
contributes zero, not its potentially negative budget. The safe source-only
envelope is

\[
\boxed{U_\varepsilon(\sigma)
=\sum_{O\subseteq I}\max\{0,B_\varepsilon(|O|)\},\qquad
b_\varepsilon(C)\le U_\varepsilon(\sigma).}
\tag{7}
\]

**Sharpness and its scope.** For each fixed sign, among arbitrary
`F x f`-invariant graph subobjects of `E x I`, take the full `E` over
each orbit with positive budget and omit the other orbits. This attains
(7). Thus (7) is optimal using only the source graph and full interior
orbit inventory. The choices attaining the two signs can differ; this is
componentwise sharpness, not simultaneous realizability. The construction
does not assert a literal child-closed strict carrier. A stronger bound
must use additional restrictions on such a carrier.

Combining (1), (2) and (7) gives the narrower conditional exclusion:

\[
\boxed{m_\varepsilon(A_C^-)+U_\varepsilon(\sigma)<r
\quad\Longrightarrow\quad
\text{the proposed neutral strict component cannot exist}.}
\tag{8}
\]

The inequalities are proved; their strictness for every possible actual
candidate remains unproved. When representation is known, (6) can improve
(8). A negative exact corrected multiplicity also contradicts (2).

#### 5. Established source and alphabet restrictions

For irreducible PIP3, `E` is connected: a nontrivial eventual component
coboundary would inject a root-of-unity representation into the incidence
direct limit, contradicting the irreducible noncyclotomic characteristic
polynomial. [Barge--Diamond, Theorem 4](https://arxiv.org/pdf/math/0702669)
gives `dim H^1 = 3 + beta_1(E)`.
[Barge, Theorem 22](https://arxiv.org/pdf/1301.7094), the odd-norm
coincidence-rank-two bound, then implies

\[
\operatorname{cr}(\sigma)=2,\quad |\det M|=1
\quad\Longrightarrow\quad \beta_1(E)\ge2.
\]

This is the previously established literature filter, not a new result.
In particular, source cycle rank at most one already excludes unit rank
two. A sign corollary proved only on that class would not remove a new
case from the surviving problem.

Under property (F), `I` is empty and `U_+=U_-=0`. Empty bounded return
lists through finitely many powers do not establish (F). More generally,
the #603 minus-one simplification requires all interior periods and all
cycles in both endpoint maps to be odd. On at most three letters,
absence of a two-cycle ensures the endpoint condition. On larger
alphabets it does not: an endpoint four-cycle is a counter-calibration.

### Evidence and replay

#### Canonical code and finite scope

- `kernel/psc/neutral_seam_budget.mojo` implements (5)--(7), using the
  validated connected `ERGraphMap`, its exact powered cycle types and
  checked integer accumulation. A represented-orbit list and an optional
  complete source list have deliberately different interfaces. Nonpositive
  periods and targets other than the two signs are refused.
- `kernel/tests/test_neutral_seam_budget.mojo` independently enumerates
  invariant nonempty edge subsets, builds their actual incident vertices,
  walks the powered permutations and checks the inequality and equality
  at the full slice. For the seven named sources and powers `q=1,...,6`,
  this gives 1,476 subgraph/sign checks. It also computes the complete
  certified interior inventory and the canonical full-box seam cycles.
- The augmented targeted test compares independent literal endpoint,
  ordered seam and interior identities at powers four, two and three
  for the three new sources below. Source ordinals and expanded words
  are retained. This adds new controls; it does not repeat the earlier
  48-comparison table as evidence for a universal theorem.
- `kernel/neutral_seam_probe.mojo` enumerates the existing canonical
  4,554-specimen PIP corpus, filters to unit determinant and source cycle
  rank at least two, and uses the complete certified prototile box with
  a shared `StableRadiiCache`. No floating screening or bounded-prefix
  substitute for completeness is used.

Replay with the pinned repository runtime:

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_neutral_seam_budget.mojo
pixi run --locked mojo run -I . -I tests tests/test_neutral_rank_one_control.mojo
pixi run --locked mojo run -I . neutral_seam_probe.mojo
```

The evidence directory records the equivalent exact local runtime command,
source hashes and actual exit statuses. The final augmented seam test
completed with exit zero: all 1,476 subgraph/sign checks, seven full-box
calculations, the three new complete literal-identity comparisons, and
the reducible strict-control replay and refusal below passed. The
rank-one calibration and the canonical source probe also completed with
exit zero. No full Mojo suite, Lean build, isolated proof audit or hosted
acceptance is claimed here.

#### Four inherited controls and three new controls

All seven canonical full-box calculations have zero aligned nonproductive
sinks. The corrections in the table are calculations on these productive
boxes, not multiplicities of an existing strict bigon system.

| Ordered images | `det M` | `beta_1(E)` | Complete interior periods | Full-box `(b_+,b_-)` | Optional `(U_+,U_-)` |
| --- | ---: | ---: | --- | --- | --- |
| `01/12/021` | 1 | 1 | `1` | `(-1,+1)` | `(0,1)` |
| `1/02/202` | -1 | 0 | `2` | `(-1,-1)` | `(0,0)` |
| `1/2/021` | 1 | 2 | empty | `(0,0)` | `(0,0)` |
| `01/02/0` | 1 | 0 | empty | `(0,0)` | `(0,0)` |
| `01/122/201` | 1 | 2 | `4` | `(+1,+1)` | `(1,1)` |
| `12/012/221` | -1 | 2 | `1,1` | `(0,+2)` | `(0,2)` |
| `12/120/221` | -1 | 2 | `3,1` | `(0,0)` | `(1,0)` |

The old positive correction at `-1` of `01/12/021` is still necessary
against a sign-blind nonpositivity assertion. Its determinant is `+1`,
however, so that sign is not `(det M)^m`; and its source cycle rank is
only one. The two new positive controls address both limitations.

#### Exact source witnesses at the selected neutral signs

For `01/122/201`,

\[
M=\begin{pmatrix}1&0&1\\1&1&1\\0&2&1\end{pmatrix},\qquad
\chi_M=x^3-3x^2+x-1,\qquad\det M=1.
\]

The source ER is `K_(2,3)`. Its six edges are
`10,11,12,20,21,22`; the endpoint action swaps the two left vertices
and fixes the three right vertices. The single interior orbit is

```text
(1; -1,0,1) -> (1; 0,0,1) -> (2; 1,0,0) -> (1; 0,1,-1)
source ordinals: 0,2,2,0
```

The literal address `sigma^4(1)=P 1 Q` has
`v=(-1,0,1)`, `(M^4-I)v=(6,8,8)=Parikh(P)`, `|P|=22`, and total
image length 69. The fourth endpoint action is the identity, so both
budgets are `6-5=1`. In particular `b_+=1` occurs at the determinant-
selected neutral sign `epsilon=+1`, with source `dim H^1=5`.

For `12/012/221`,

\[
M=\begin{pmatrix}0&1&0\\1&1&1\\1&1&2\end{pmatrix},\qquad
\chi_M=x^3-3x^2+1,\qquad\det M=-1.
\]

Its source ER is again `K_(2,3)`. The two fixed interior states have
one-step witnesses

\[
\sigma(1)=0\,1\,2,\quad (M-I)(-1,0,1)=e_0;
\qquad
\sigma(2)=2\,2\,1,\quad (M-I)(1,1,-1)=e_2.
\]

Both occurrences have ordinal one. Each orbit contributes `(0,1)`,
giving `b_-=2`, which is at the selected neutral sign for odd `m`.
This source also has `dim H^1=5`. Neither source is a strict example;
both refute the proposed determinant-selected sign inequality on source
literal geometry even after imposing the known source cohomology bound.

#### Completed finite probe

The canonical source probe completed with exit zero, no caps and no
arithmetic refusals. Among 4,554 corpus specimens it evaluated the 492
unit specimens with source cycle rank at least two, using 144 distinct
cached incidence matrices. Twelve have positive full-product `b_+`;
twelve determinant-minus-one specimens have positive full-product `b_-`.
Twenty-four have positive optional `U_+`, and twelve determinant-minus-one
specimens have positive optional `U_-`. Twelve sources contain a negative
orbit whose omission makes the plus envelope strictly larger than the
nonnegative part of the full-product sum. These counts concern the stated
finite source inventory, not arbitrary image lengths or strict carriers.

### Negative controls

#### A source-word witness against ambient signed-sum monotonicity

The literal reordering `12/120/221` has the same incidence matrix as
`12/012/221`, but different endpoint dynamics. Its source ER is
`K_(3,2)`: six edges, five vertices, two three-cycles on edges, and a
three-cycle plus two fixed vertices. Its complete interior orbit periods
are three and one.

The period-three states are

```text
(1;1,1,-1) -> (2;1,0,0) -> (2;0,1,0)
source ordinals: 1,1,2
```

They give `sigma^3(1)=P 1 Q`, with
`(M^3-I)(1,1,-1)=(1,4,8)=Parikh(P)`, occurrence index 13 and image
length 23. The fixed state `(2;1,1,-1)` is witnessed by the middle
`2` in `221`.

At `+1`, the period-three source slice contributes `6-5=+1`, whereas
the fixed slice contributes `2-3=-1`. The full-box correction is zero.
The invariant source-seam subgraph retaining only the period-three
orbit has correction one. Thus a complete literal source catalogue does
not upper-bound its possible invariant subgraphs by its *signed total*.
This is a literal-source graph witness, not a child-closed strict-system
counterexample. The small auxiliary one-edge control gives the same
failure as `-1 > -2` when one of two fixed copies is absent.

#### Neutral image rank one is not excluded by the ambient dimension

`test_neutral_rank_one_control.mojo` pins the previously scratch-only
unit calibration of [round three, Section 5.3](c4-round3-2026-11-16.md).
The irreducible balanced literal pair

```text
1222200110120 / 2201121220001
```

has `K1=K2=0`, nonzero `K3`, and a one-dimensional span of `K3` and its
swap. The explicit positive integer matrix

\[
M=\begin{pmatrix}
7969&34278&1370\\
9750&41941&1676\\
9138&39306&1571
\end{pmatrix}
\]

is a Pisot unit with determinant `-1` and characteristic polynomial
`x^3-51481x^2+30023x+1`; it satisfies `M^(tensor 3) K3=-K3`.
The exact fixture guards its machine-arithmetic range and uses the
existing exact rational rank and Pisot routines.

This does not prove that a strict component can have rank one. The
displayed pair is not asserted legal in that substitution language.
For the explicit run-length substitution realizing `M`, every image
starts with `0`, and the first literal child is the coincidence `(0,0)`.
The two-dimensional ambient degree-three determinant eigenspace therefore
cannot be used as a rank-two lower bound for a single literal pair;
an actual strict-system lower bound requires an additional closure and
realization argument.

#### Alphabet and input controls

A genuine available strict control is replayed separately: `10/102/211`
has an existing four-state literal child-closed system. The targeted
test executes its exact word, child-matrix and closure checks, then
confirms that the connected-source budget refuses its disconnected
eventual-range graph. Its characteristic polynomial is
`(x-1)(x^2-2x-2)` and its determinant is `-2`. It is neither irreducible
nor unit PIP3, so this replay calibrates the hypothesis boundary rather
than providing a candidate in the standing class.

A four-letter primitive source in the targeted test has all bigrams,
identity first-letter map and a four-cycle last-letter map. Neither
endpoint map has a two-cycle, yet its source-orbit minus budget for a
hypothetical period-one interior mark is three. The mark is not claimed
to be an actual interior state of that source. This finite graph control
preserves precisely the #603 scope restriction. Invalid period and sign
inputs are refused; the complete geometric routines retain their existing
cap and exact-arithmetic refusal semantics.

### Non-claims / remaining gaps

The finite-graph upper bound and its sharpness are written proofs. The
new executable checks verify their finite inputs and controls. They do
not formalize the joining, common-cut coding, all-power trace transfer
or arbitrary-degree defect intertwiner in Lean.

Each of the seven full-box controls has no aligned nonproductive sink;
the source-only probe did not construct overlap carriers for its other
inputs. The new
positive corrections refute source-geometry sign shortcuts, including
determinant-selected ones, but do not refute a theorem assuming an actual
literal strict component. Available reducible strict controls cannot
supply that missing PIP3 realization: their irreducibility and rational-
independence interfaces differ.

The next necessary theorem must supply information beyond source ER and
interior periods. One precise target is a restriction on which positive-
budget interior orbits and source cycles can coexist in a literal
child-closed strict carrier, strong enough to force
`m_epsilon(A_C^-)+b_epsilon(C)<rank D_(3m)`. Alternatives are a new upper
bound on the actual overlap odd multiplicity, a justified literal lower
bound on the actual defect-image rank, or another literal obstruction
excluding the sink. Formula (7) is already optimal before those extra
constraints are used.

The earlier 48 literal seam comparisons remain bounded validation of the
constructor's identities. They are not counted again as a universal C4
argument, and none of the results here closes C4 or PSC.

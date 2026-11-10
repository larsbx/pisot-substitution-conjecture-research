# C4 ordered overlap mass: finite controls and replay

Date: 2026-11-10. The
[literature stop/go](c4-overlap-mass-literature-2026-11-10.md) was recorded
before this implementation. The
[proof and scope note](c4-overlap-mass-2026-11-10.md) states the universal
Lean interfaces; this document describes the separate executable controls.

**Development status at preparation:** the new Quint model passed all sixteen tests and
all nine expected assertion-failing mutations. The canonical Mojo test is
implemented but has not yet been compiled or executed in this development
environment. Its acceptance requires the hosted native replay on the new
published revision. A clean exact-head Quint receipt is also required;
the successful development receipt records a dirty checkout and must not
be relabelled as a clean published-head result. Subsequent exact-revision
acceptance receipts belong in the implementation PR; this paragraph records
the preparation-stage observation, not a permanent native failure.

## 1. Exact finite objects and domains

The independent model is
[`C4OverlapMass.qnt`](../proof/quint/C4OverlapMass.qnt). Its integer
quantifiers exhaust the following stated domains; `--max-samples=1` runs
each whole quantified assertion once, rather than sampling one member of
the finite domain.

| Domain | Exact inventory | Count |
| --- | --- | ---: |
| Interval partitions | Ordered binary words of length zero through two on each track; `(ell_0,ell_1)` in `{0,1,2}^2`, with unused `ell_2=0`; displacement in `{-2,-1,0,1,2}` | `7 * 7 * 9 * 5 = 2,205` |
| Scaled packet subdivisions | Both binary images have length two; third image is `00`; source letters in `{0,1}^2`; residual `(x,y,0)` with `x,y` in `{-2,-1,0,1,2}`; `ell=(1,1,1)`, `beta=2` | `4 * 4 * 2 * 2 * 5 * 5 = 1,600` |
| Actual strict control | `sigma=1/012/1`, ordered pairs `01/10`, `10/01`, `12/21`, `21/12`; `ell=(1,2,1)`, `beta=2` | 16 actual marks; 12 positive packet labels |
| Retained digit subfamilies | All masks of the four ordered digit pairs for `sigma=00/00/00`, parent `(0,1,0)` | 16 masks |
| Literal quotient counts | All directed graphs on three ordered states, including loops; fixed label map `(0,0,1)` and representatives `(0,2)` | 512 graphs |

The graph test conditions the count identity on explicit uniform incoming
and outgoing counts within each fiber. It checks every one of the 512
graphs, including those that fail this premise. Named positive and
negative fixtures prevent a vacuous interpretation of that implication.
The finite graph family has at most one edge per ordered endpoint pair;
a separate repeated-edge fixture tests literal multiplicity.

## 2. The sixteen Quint tests

The runner checks this exact ordered inventory. A missing, additional or
renamed test refuses acceptance until the declared inventory is updated.

| Test | Contract or control |
| --- | --- |
| `domainCountTest` | Pins the finite domain sizes, including all 512 distinct graph encodings. |
| `finiteIntervalPartitionTest` | Sums all actual interval cells for all 2,205 word/length/displacement inputs and compares with the whole interval intersection. |
| `finiteScaledSubdivisionTest` | Checks all 1,600 packet subdivisions under exact image-length scaling. |
| `affineTranslationTest` | Pins the incidence action, digit-prefix correction and physical offset to the explicit residual `(-2,0,-1)` and offset `-3`. |
| `strictCompleteCarrierConservativeTest` | Checks all sixteen actual marks, the twelve positive labels and closure of every positive child; the full mass budget is conservative. |
| `occurrenceMultiplicityTest` | Keeps the two different positive digit occurrences with the same packet label; full mass is two, deduplicated mass is one. |
| `boundaryAndDegenerateTest` | Boundary touch, disjoint intervals, zero-length intervals, empty images with scale zero, and zero length rows have their exact zero-mass semantics. |
| `positiveWrongRowTest` | The positive row `(2,1,1)` fails the image-length equations and the proposed scaled mass equality. |
| `omittedOccurrenceBudgetTest` | For every four-digit retention mask, deficit equals the sum of the explicitly omitted occurrence masses. |
| `literalMixedOrbitCountsTest` | Computes forward and inverse matrices from actual edge IDs with fiber sizes `(2,1)`; checks the weighted count correspondence. |
| `finiteQuotientCountsTest` | Exhausts all 512 three-state graphs and checks the correspondence whenever both fiber-uniformity premises hold. |
| `uniformityIsNecessaryTest` | A single edge from one member of a size-two fiber fails uniformity and the proposed representative-count correspondence. |
| `allFixedAndFreeOrbitsTest` | Tests size-one fibers with a repeated edge and uniformly size-two fibers where the common factor cancels. |
| `transposeOrientationTest` | Distinguishes row action from transpose action on a nonsymmetric matrix. |
| `mixedConservativeWeightedTest` | Mixed fiber sizes preserve an exactly conservative weighted budget; the unweighted shortcut violates it. |
| `mixedStrictWeightedTest` | Mixed fiber sizes transport an actual positive arithmetic deficit to the correct vertex and weight. |

### Occurrences, boundary cells and omission

For `sigma=00/00/00`, unit lengths, scale two and parent packet `(0,1,0)`,
the lexicographically ordered digit pairs `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)`
have masses `[1,0,0,1]`. The first and last give the same packet label but
remain two actual occurrences. Replacing their list by a set changes total
mass from two to one and manufactures a deficit.

Omitting the two boundary-only cells loses zero mass. Omitting one positive
cell loses exactly one. These statements authenticate arithmetic for the
selected subfamily; neither licenses removing that child from the geometric
problem. The complete `1/012/1` strict non-PIP control retains every positive
child and remains conservative. It therefore calibrates the precise limit
of the subdivision identity: local conservation does not supply strict loss.

The wrong-row control uses parent `(0,0,(0,-1,0))` and `ell=(2,1,1)`.
Its parent mass is one, its sole child has mass zero, and the proposed
right-hand side at scale two is two. Positivity of the row does not imply
the required exact image-length equations.

The nonnegative interval tests include empty words and zero-length letters.
The scale-zero empty-image control belongs to that general partition
boundary. It does not supply the positive scale and positive lengths used
by interior-successor seriality.

### Fiber sizes and matrix orientation

Here `F` is forward source-to-target occurrence count per representative;
`T` is the inverse target-to-source count per representative. The ordered
edge inventory retains repetitions. With actual fiber size `m`, the relation
being checked is

\[
m_i T_{ij}=m_j F_{ji},\qquad
H_i=m_i h_i,\qquad
\beta H_j-(T^{\mathsf T}H)_j
=m_j\left(\beta h_j-\sum_i F_{ji}h_i\right).
\]

The conservative mixed example has ordered states `a,b,c`, labels
`q(a)=q(b)=0`, `q(c)=1`, and edges `a -> c`, `b -> c`, `c -> c`.
For `h=(1,1)` and `beta=1`, the literal data are

\[
m=(2,1),\quad
F=\begin{pmatrix}0&1\\0&1\end{pmatrix},\quad
T=\begin{pmatrix}0&0\\2&1\end{pmatrix}.
\]

The forward deficit and the weighted inverse deficit both vanish.
The unweighted inverse deficit is `(-1,0)`, so dropping fiber weights
violates even the nonnegative-budget premise.

The second mixed example has one fixed state and a size-two fiber, with
all four directed edges between the fixed state and the two other states.
It gives `m=(1,2)`, `F=T=[[0,2],[1,0]]`, `h=(1,1)` and `beta=2`.
The forward deficit `(0,1)` becomes weighted inverse deficit `(0,2)`.
The unweighted calculation gives `(1,0)` and assigns loss to the wrong
vertex. These are finite count examples, not realized substitution-overlap
carriers or Pisot counterexamples.

## 3. Nine deliberately weakened variants

[`check_c4_overlap_mass_quint.py`](../tools/check_c4_overlap_mass_quint.py)
mutates one uniquely located source fragment at a time. Each variant must
return a nonzero exit code, name exactly its expected failing test after
one test, and include `Error [QNT508]`. A download, parse, typecheck or
timeout error does not count as a successfully rejected mathematical
variant.

| Mutation | Deliberately invalid change | Required failing test |
| --- | --- | --- |
| `equal-packet-occurrences-deduplicated` | Replace the ordered mass sum by a set of packet labels. | `occurrenceMultiplicityTest` |
| `boundary-contact-counted-positive` | Give a boundary-only cell mass one. | `boundaryAndDegenerateTest` |
| `incidence-scaling-omitted` | Use the old residual in place of its incidence image. | `affineTranslationTest` |
| `image-length-equations-ignored` | Keep nonnegativity but discard the exact scaling equations. | `positiveWrongRowTest` |
| `omitted-positive-mass-erased` | Replace the omitted occurrence sum by zero. | `omittedOccurrenceBudgetTest` |
| `orbit-size-weights-ignored` | Replace `H_i=m_i*h_i` by `h_i`. | `mixedConservativeWeightedTest` |
| `transpose-indices-reversed` | Use row indices in the transpose action. | `transposeOrientationTest` |
| `incoming-count-direction-reversed` | Substitute outgoing counts for incoming counts. | `literalMixedOrbitCountsTest` |
| `fiber-uniformity-ignored` | Treat every quotient as count-uniform. | `uniformityIsNecessaryTest` |

## 4. Canonical Mojo controls

[`test_c4_overlap_mass.mojo`](../kernel/tests/test_c4_overlap_mass.mojo)
reuses the production affine incidence and prefix tables, rather than
introducing a second packet recurrence. Its tiny integer fixtures use
lengths at most two, image lengths at most three and residual coordinates
in `-2..2`; the test-local integer operations remain far below machine
limits. It checks the 1,600 scaled packet inputs and the actual strict
carrier against an independent literal interval-intersection calculation.
It also checks all retention masks, wrong scaling, repeated edge IDs,
mixed/free/fixed fibers, the transpose convention and the 512 graph inputs.

The production geometry check calls
[`ordered_child_occurrences`](../kernel/psc/overlap_zipper.mojo) on
`01/02/0` (Tribonacci) and `1/021/001` (the determinant-two fixture).
For each substitution it starts from all nine zero-shift letter pairs,
then checks every actual child occurrence of those parents once more.
It sums `right-left` with checked cubic-field arithmetic, checks each cell
against its translated child interval, and compares the total with the
exact Perron inflation of parent mass. This is a specified two-stage
fixture family, not a new corpus census or complete graph construction.
The native run will print the reached parent and child counts.

The native `OverlapState.shift` is **bottom-start minus top-start**.
The Lean packet offset is **top-start minus bottom-start**. The test's
native interval is therefore `[0,ell_a]` intersected with
`[shift,shift+ell_b]`; its `shift` equals the negative of the packet offset.
This explicit sign boundary avoids comparing equal-looking symbols with
opposite geometric meanings.

The test's final `require_contract` is after all assertions and includes
the finite-domain and no-geometric-promotion boundaries. There is no
native success receipt at this preparation stage for the new file; the existing sweep's earlier
acceptance does not execute these newly added assertions.

## 5. Replay and source binding

From a clean checkout of the new published revision, record `HEAD` and
`HEAD^{tree}`, then run the native test with the locked compiler:

```bash
git rev-parse HEAD HEAD^{tree}
cd kernel
pixi run --locked mojo run -I . tests/test_c4_overlap_mass.mojo
```

Run the independent Quint suite from the repository root, writing receipts
outside the checkout so output files do not dirty the source tree:

```bash
mass_replay_dir=$(mktemp -d)
python3 tools/check_c4_overlap_mass_quint.py --output "$mass_replay_dir"
```

The default command pins Quint `0.33.1`; the backend is `typescript` and
the fixed seed is `20261110`. `--quint-command` can select an already
installed copy, whose reported version must still match. Each command
has a 180-second limit, with a timeout recorded as refusal and no verdict.

The runner copies the model to a private read-only snapshot, checks its
exact test inventory and typechecks it, then checks all sixteen passing
tests. Each unique mutation receives its own read-only snapshot, expected
test binding and SHA-256. Before accepting, the runner rereads the original
model and its own source, rechecks both snapshot contents, and rechecks
Git head and committed tree. The full-worktree dirty flag is sampled at
the beginning and end. A change to unrelated working files is not claimed
to be detected continuously; clean published-head acceptance therefore
uses an isolated checkout and the source-bound hosted workflow.

The [C4 workflow](../.github/workflows/c4-recurrent-flat-exits.yml) checks
out the PR head explicitly. Its native `exact-replay` job includes the
new Mojo test. The separate `overlap-mass-quint` job records head/tree,
runs this runner, and uploads `c4-overlap-mass-quint-<head>` with the
revision record, receipt and logs. The artifact and exact completed job
must be inspected before recording hosted acceptance.

### Recorded development result

All sixteen expected tests passed and all nine variants reached their
expected QNT508 assertion. A separate log audit recomputed every mutant
hash and checked the exact pass/fail inventories. This was a dirty
development checkout over `b0a64e50bd9790c0033d7ff674c8b3a9e72b0a92`, whose
committed tree was `248bcea1a539537d4972b91daef957a182be4acc`; the new
uncommitted source bytes are identified by the hashes below. The receipt
records `worktree_dirty: true` and `source_and_revision_recheck: unchanged`.

| Development item | SHA-256 |
| --- | --- |
| Quint model | `cf223ede47c1c38c40cff953b26f7bb9271015d451d3c300fe6cca6ad7683c14` |
| Quint runner | `a6024a83c1d7c5423e2842173932b1da22e6a61edb3365c5c8e38e0ac64e968c` |
| Development receipt | `9966205677bd5ee6febbb64a591c189863d61828a8ec4cd16917deadecf0405b` |
| Unexecuted native test source | `d17a3b91a73e94fddfad3409cc4c575802ca3b7dadeb4a3bf7599bf99c5a182b` |

These hashes preserve the development observation without assigning it to
the later published commit. Exact published-head native and Quint receipts
remain integration obligations at this document's initial recording.

## 6. Scope boundary

The controls support the stated finite interpretations and calibrate
weakened variants. The universal interval and counting statements are the
separate Lean results. Neither layer constructs actual compact overlap
sets, proves nonunit Haar scaling, authenticates every relevant geometric
state, supplies a primal overlap supersolution, or establishes a justified
positive loss in every inverse source component. The conservative strict
control explicitly prevents such a promotion. C4, Concentration, global G1
and PSC remain open.

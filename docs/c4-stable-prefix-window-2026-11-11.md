# C4: compact windows for the actual prefix closures

This continuation supplies a deductive route from a commuting contracting
action to a bound on **every actual infinite-word prefix**. It continues
[the literal prefix closures](c4-prefix-closure-2026-11-11.md), developed
in [PR #542](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/542)
at `aa80845e9ccde9f4a0c90c00d1f6d6ade40559b5`. The
[targeted source gate](c4-stable-prefix-window-literature-2026-11-11.md)
was recorded before implementation in commit
`5dafd886`.

The local finite inequalities are already available in the canonical
[finite-cylinder verifier](c4-finite-cylinder-overlap-verifier-2026-11-04.md).
Its source and archived evidence remain unchanged. That earlier note's
Section 3 takes a maximum over already compact tiles. The argument there
is valid for bounding such supplied compact sets, but cannot establish
their compactness independently. The new proof instead works directly
with the actual prefix at each natural-number position.

**Scope:** a general analytic implication with explicit contracting-action
hypotheses, composed with the constructed matrix-adic carrier. The existing
named native certificates verify their finite exact inputs separately.
They are not deserialized into Lean. General C4, G1, Concentration and PSC
remain open; no governed claim is promoted. Independent human review
remains pending as nonblocking validation debt.

## 1. Actual words, local digits and the analytic premises

Let `tau` be the full literal substitution on `Fin 3` and let `w` be the
same infinite word used in `PrefixClosure.prefixTiles`. Assume
`FixedPrefix tau w` and that each image is nonempty. Write

\[
P_n=w[0,n),\qquad x_n=\pi(\operatorname{parikhZ}P_n).
\]

The additive projection `pi` has codomain a normed additive commutative
group `E`. The additive action `A` satisfies

\[
A(\pi z)=\pi(M_\tau z),\qquad
\|Ax\|\le q\|x\|,\qquad 0\le q<1.                 \tag{1}
\]

The digit bound quantifies over **every full literal Mark** of **every
image** `tau(a)`. If that Mark decomposes the image as `P c S`, then

\[
\|\pi(\operatorname{parikhZ}P)\|\le D.            \tag{2}
\]

Take `R >= 0` with

\[
qR+D\le R.                                       \tag{3}
\]

All positions count, including repeated occurrences of the same letter.
No point cloud, quotient residue or selected subinventory substitutes for
(2). The canonical choice `R=D/(1-q)` is valid when `D>=0`; equality in
(3) is allowed. Only the contraction inequality `q<1` must be strict.

The finite digit family also supplies a bound without a numerical
certificate: the sum of all its projected norms bounds each term.
This gives a general compactness implication from contraction, while a
checked tighter digit bound yields a smaller useful window.

## 2. The all-prefix proof

The existing literal address equivalence supplies for every output
position `n` a parent index `i` and its full Mark, with

\[
i\le n,\qquad x_n=A x_i+\pi(\operatorname{parikhZ}P). \tag{4}
\]

The index inequality follows from nonerasure. The vector identity follows
from the actual fixed-prefix equation, full prefix decomposition and
incidence commutation. These are the existing
`childIndex_parent_le` and `parikhZ_prefix_childIndex` interfaces.

Strong induction on `n` has two cases:

1. For `i<n`, the induction hypothesis and (1)--(3) give
   `norm(x_n) <= q norm(x_i)+D <= qR+D <= R`.
2. For `i=n`, no strict induction step is available. Equation (4) instead
   gives `(1-q) norm(x_n) <= D <= (1-q) R`. Because `1-q>0`, the desired
   bound follows directly.

Thus

\[
\forall n\in\mathbb N,\quad\|x_n\|\le R.         \tag{5}
\]

There is no assumed maximum of the infinite prefix set, no terminating
ancestry-chain premise, no strictly growing image-length premise, and no
assumed compact tile in this argument. In particular, equality between
parent and child index is handled rather than silently excluded.

## 3. Compactness in the original product carrier

If `E` is proper, the closed ball `closedBall 0 R` is compact. Under
integral incidence injectivity, the already constructed `H_M` is compact.
Every actual raw prefix point belongs to

\[
\overline B_E(0,R)\times H_M.
\]

Taking its letter-indexed closures therefore gives compact
`PrefixClosure.prefixTiles`. This uses
`prefixTiles_compact_of_window` with (5) as a proved input. The existing
history-image theorem then gives compactness of every finite inverse
history piece when the relevant action is continuous.

These are the actual prefix closures, defined from `w`. No abstract
attractor is substituted for them. Compactness alone does not imply that
a chosen finite ancestor graph represents every nonempty piece.

Closed-embedding assumptions remain where the prior tile-equation and
inverse-cover theorems use them. Contraction alone cannot supply
injectivity; the zero action is a counterexample. The compactness result
does not acquire those stronger hypotheses merely because a later cover
result needs them.

## 4. Period and contraction block

A word fixed by `sigma^k` is fixed by every multiple `sigma^(k*r)`.
This fact must be proved for the **same word** and the **literal powered
images**. Equal incidence matrices are insufficient to identify two
substitution words.

The useful native example has word period two and contraction block
twelve. Use `tau=sigma^12`, action `B^12`, and all depth-twelve literal
digits to derive (5). The resulting compactness concerns the same prefix
closures that have the period-two tile equation. Keep the original
`H_M` throughout; no identification with `H_(M^12)` is necessary.

The period-two action need not contract in the displayed coordinate norm.
Indeed it fails the native norm check in both named examples, while the
twelfth power succeeds. Neither the word period nor the block exponent
may be replaced by the other without proof.

## 5. Reused exact native certificate

The unchanged implementation supports two productive nonunit controls:

| Substitution | Word period | Contracting block | `q` | `D` | `R` |
| --- | --- | --- | --- | --- | --- |
| `1/021/001` | 2 | 12 | `7/8` | 5 | 40 |
| `1/012/001` | 2 | 12 | `7/8` | 5 | 40 |

Their common incidence has determinant two and characteristic polynomial
`x^3-x^2-2x-2`. The existing chart is

\[
Wz=(z_0-a z_1,z_2-b z_1),\quad
a=(3\beta-\beta^2)/2,\quad b=1/\beta,
\]

with `WM=BW`. The canonical `certify_radius` checks the root bracket,
canonical chart normalization, actual incidence, period-two prolongation, both row-norm
bounds of `B^12`, the complete depth-twelve prefix hull, and
`(7/8)*40+5=40`. The independent oracle uses exact arithmetic in
`Q[beta]/(x^3-x^2-2x-2)` and enumerates the actual block digits.
Its separate exact polynomial identity tests check `WM=BW` against the
actual incidence; the canonical normalization check alone is not that
symbolic commutation proof.

The depth-twelve image lengths are `10791`, `24491` and `20301`, giving
**55,583 literal block digits per control**. The existing emitted cylinder
packet uses depths `2,4,6`: **1,002 occurrence records, 283 nonempty slices,
and 18 pair upper bounds** across the two controls. Those two counts
describe different inventories and must not be conflated.

The generic Lean theorem and these computations have complementary
scopes. A complete named Lean instance still needs formal chart
commutation, sound interval/root evaluation, and the soundness of the
complete digit-hull certificate. The scalar calibration does not prove
those missing real-analytic bindings.

## 6. Independent controls and replay

`proof/quint/C4StablePrefixWindow.qnt` independently tests the
denominator-cleared scalar inequalities and bounded address systems.
Its 19 named tests include 39,312 parent-step tuples, 4,368 self-parent
tuples and 13,500 three-index norm/parent/configuration tuples. These are
full quantified domain sizes, not counts of cases satisfying the premises.
Its finite quantifiers are exhaustive within their declared domains;
they are not a universal theorem over real norms. Controls retain
self-parent addresses and demonstrate why `q=1`, an undersized radius,
an incomplete digit inventory, and an unjustified forward-parent step
cannot be admitted. A finite fully closed contracting system may still
be bounded even with forward edges; a forward-edge counterexample must
expose its unbounded or unverified tail.

The provenance runner checks its exact named-test inventory, snapshots
the source, verifies Quint `0.33.1`, and requires deliberately weakened
models to reach their named failing assertions in nine mutations. Syntax errors, missing
tests, timeouts and tool failures are not credited as counterexamples.

The dedicated workflow replays the existing Mojo cylinder and density
contracts and the literal-prefix controls, including the mandatory
`00/11/22` physical forward-leak diagnostic `4 / 2 / 2`. It emits the
unchanged cylinder protocol and runs the independent suite and optimized
oracle. It binds the clean checkout, Git head/tree and source digests
before execution and rechecks them afterward. The separate full Lean
workflow builds isolated sources and audits every local declaration.

Replays from the repository root:

```bash
./tools/check_lean.sh
python3 tools/check_c4_stable_prefix_window_quint.py --output /tmp/stable-window-quint

cd kernel
export MODULAR_HOME="$PWD/.pixi/envs/default/share/max"
.pixi/envs/default/bin/mojo run -I . tests/test_c4_finite_cylinder_overlap.mojo
.pixi/envs/default/bin/mojo run -I . tests/test_c4_cylinder_density.mojo
.pixi/envs/default/bin/mojo run -I . tests/test_c4_prefix_closure.mojo
.pixi/envs/default/bin/mojo run -I . c4_finite_cylinder_overlap.mojo > /tmp/stable-window-cylinder.txt
cd ..
PSC_CYLINDER_NATIVE_OUTPUT=/tmp/stable-window-cylinder.txt \
  python tests/test_c4_finite_cylinder_overlap_oracle.py
python -O oracles/python/c4_finite_cylinder_overlap.py /tmp/stable-window-cylinder.txt
./tools/verify_all.sh provenance
```

Exact accepted revisions and actual job/artifact receipts belong to the
implementation PR. Earlier #542 receipts cover its prior source revision,
not this new module. Local compilation with cached dependencies is useful
development feedback and does not replace the isolated whole-bank gate.

## 7. Next mathematical obligations

| Obligation | What this continuation supplies | What remains |
| --- | --- | --- |
| Uniform actual-prefix enclosure | Derivation from a commuting contraction and all literal digits, including self-parent addresses | Instantiate the intended stable realization from general Pisot data |
| Compact actual prefix tiles | Closed-ball enclosure composed with the actual compact `H_M` | Bind every concrete numerical/chart certificate into Lean if claiming a closed named formal instance |
| Complete finite ancestor constructor | Compactness is an input for geometric bounds | Prove every actual nonempty piece is represented; justify every exclusion |
| Forward completeness and mass | Earlier occurrence identities remain available | Prove the required complete-domain correspondence and product-Haar scaling |
| Contradiction at a strict root | Existing conditional null-overlap machinery remains available | Supply the actual recurrence and strictly positive compact root measure |

Boundedness and compactness advance the geometric setup. They do not
establish a losing state, overlap positivity, C4, pure discrete spectrum,
or the general Pisot Substitution Conjecture.

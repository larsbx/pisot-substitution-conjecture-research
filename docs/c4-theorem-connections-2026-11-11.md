# Direct theorem connections: exterior action and finite geometric carrier

This increment connects two already-developed parts of the PSC proof bank.
The baseline is main `2848e5f67b605669a550f362a1de4bf1c1529f7c`.
The source gates were recorded before their respective proof code:
[degree-five exterior connection](c4-degree-five-exterior-literature-2026-11-11.md)
and [geometric packet carrier](c4-geometric-packet-carrier-literature-2026-11-11.md).
The new modules are independent of the separate stable-prefix work in
PRs #542 and #543.

## 1. The degree-five polynomial has an explicit three-dimensional action

Let M be a three-by-three matrix, d its determinant and W the repository's
explicit matrix `Cyclicity.wedge2 M` of two-by-two minors, with pair basis
01, 02, 12. The new `Degree5Exterior` module proves, over any commutative
ring,

\[
\chi_{dW}(X)
=X^3-d\,\operatorname{tr}(W)X^2
 +d^3\operatorname{tr}(M)X-d^5.
\]

The proof first establishes `wedge2 (c • M) = c^2 • wedge2 M`. It then
substitutes the accepted trace and determinant identities into
`Cyclicity.charpoly_fin_three`:

\[
\begin{aligned}
\operatorname{tr}(dW)&=d\operatorname{tr}(W),\\
\operatorname{tr}(\operatorname{wedge2}(dW))
 &=d^2\operatorname{tr}(\operatorname{wedge2}W)
 =d^3\operatorname{tr}(M),\\
\det(dW)&=d^3\det W=d^5.
\end{aligned}
\]

No inverse or nonzero determinant is used. In particular, the coefficient
identity remains valid for singular matrices. Over the rationals this
identifies the exact existing definition:

\[
\operatorname{Degree5Completion.reciprocal}(M)
=\chi_{(\det M)\,\operatorname{wedge2}M}.
\]

This is standard coefficient algebra. Its purpose here is to expose the
small matrix behind the previously abstract reciprocal cubic.

### The actual degree-five image and its rank

Keep the entire hypothesis set of `Degree5Completion.q5_eq_pow_rank`:

- A normalized actual ternary child system and degree-four binomial
  equivalence on every state.
- Irreducible rational incidence characteristic polynomial.
- Primitive actual incidence matrix.
- A distinguished incidence root beta with norm greater than one, with
  all other complex roots having norm less than one.

The new theorem rewrites its conclusion as

\[
q_5=\chi_{(\det M)\,\operatorname{wedge2}M}^{\,k},
\qquad
\dim_{\mathbb Q}\operatorname{im}Q_5=3k.
\]

The zero image remains permitted: k may be zero, and the characteristic
polynomial of the zero-dimensional image is one. The positive-exponent
version requires an actual nonzero degree-five defect column.

The unit cases keep the determinant sign. For d=1 the cubic is the
characteristic polynomial of W; for d=-1 it is that of -W. Equality of
characteristic polynomials is not an isomorphism of the actual degree-five
image with copies of the exterior module. No similarity, semisimplicity,
realizable word system, or degree-five-to-degree-two defect map follows
from this identity alone.

### A direct short-image nonunit consequence

`incidence_column_sum` proves, by counting every actual letter occurrence,

\[
\sum_b M_{ba}=|\sigma(a)|.
\]

Consequently the all-ones row is subinvariant at any common image-length
bound B. Applying the already formalized positive-row spectral comparison
to an actual eigenvector proves that every complex incidence root satisfies
`norm(beta) <= B`. This general bound requires neither primitivity nor a
Pisot hypothesis.

For images of length at most three, the distinguished root has norm at
most three, hence less than eight. Under the unchanged degree-five image
hypotheses and `norm(det M) >= 2`, the accepted determinant-bound exclusion
therefore gives `columns P = 0`.

This is a conditional exclusion of degree-five defects when degree-four
agreement holds throughout the supplied system. It does not exclude
higher defect degrees or supply the existence or nonexistence of every
strict child system. No corpus enumeration is needed for the theorem, and
no new enumeration or finite-domain count is asserted.

### Algebraic controls

The Lean module retains three distinct failure boundaries:

| Control | Required behavior | False strengthening it rejects |
| --- | --- | --- |
| `diag(1,1,0)` | The exterior square is nonzero but the reciprocal polynomial is X^3 | Treating the polynomial identity as requiring invertibility |
| `-I` | The reciprocal differs from the characteristic polynomial of the unscaled exterior square | Dropping the negative determinant sign |
| `2I` | The reciprocal differs from the characteristic polynomial of the unscaled exterior square | Dropping the determinant scale |

The existing zero-image examples remain in `Degree5Completion`; the new
image theorem preserves their exponent-zero case.

## 2. Actual overlap bounds yield a finite complete ancestor carrier

`GeometricPacketCarrier` formalizes the elementary bounded-lattice part
of the written Theorem F2 in
[the earlier finite-overlap note](c4-finite-overlap-carrier-2026-11-05.md).
It then derives the represented-ancestor premise previously supplied to
the literal restricted-history cover.

### Exact inputs

Work in an arbitrary additive commutative group G. Supply the actual
integral star map, actual sets K_a, and two additive real coordinate maps
c_0,c_1. Assume the authenticated enclosure

\[
|c_i(x)|\le R_i\quad(x\in K_a).
\]

Supply positive physical letter lengths ell and an upper bound H for
all three lengths. The chart must reconstruct every integer coordinate:

\[
z_j=U_{j0}\operatorname{offset}_{\ell}(z)
    +U_{j1}c_0(\operatorname{star}z)
    +U_{j2}c_1(\operatorname{star}z).
\]

The exact reconstruction is the faithfulness assumption. Merely giving
two projection formulas, an alleged inverse matrix, or small numerical
samples does not discharge it. This theorem does not construct the stable
projection of an arbitrary Pisot incidence matrix.

### The coordinate bound

For a packet p=(a,b,z), the existing actual overlap is

\[
\{x\mid x\in K_a,\;x-\operatorname{star}z\in K_b\}.
\]

A point in that set gives two bounded coordinates. Their difference is
`c_i(star z)`, so its absolute value is at most 2R_i. The packet's physical
interior predicate separately bounds the absolute physical offset by H.
The reconstruction formula and triangle inequality then give

\[
|z_j|\le B_j
=|U_{j0}|H+2|U_{j1}|R_0+2|U_{j2}|R_1.
\]

Choose certified natural numbers N_j with B_j <= N_j. Such natural upper
bounds exist by the Archimedean property; in a numerical instance they
must be authenticated against its actual chart and enclosure. The full
integer box has exactly `product_j (2*N_j+1)` residuals and at most
`9 * product_j (2*N_j+1)` letter-pair packets.

### Why the interior filter matters

The finite carrier is the full packet box **filtered by physical
interior**. For every p in this carrier, every literal inverse occurrence
from p to u preserves interior when positive exact image scaling holds.
If the actual overlap at u is nonempty, the preceding coordinate argument
places u in the same integer box. Therefore u lies in the same filtered
carrier.

This is the exact global one-step statement required by the existing
restricted-history cover: every nonempty incoming ancestor is represented
at every admitted intermediate source. It is derived from geometry and
the actual inverse equation, not supplied as an extra completeness premise.
Filtering only at the initial root or restricting only the terminal
history state would not establish the same result.

Under the existing injective commuting ambient action, actual tile
equations and integral-range reflection, the new adapter then gives the
actual overlap as the union of all literal finite-depth history pieces
whose intermediate states stay in this finite carrier. Both incoming
marks and every occurrence history are retained.

The use of real interior predicates may require classical decidability.
This constructs a finite mathematical carrier; it does not by itself
implement an executable exact enumerator for arbitrary real chart data.
The repository's existing numerical carrier verifiers still need their
own authenticated arithmetic and complete occurrence receipts.

### What this discharges and what remains

The new result discharges the finite-domain representation premise from
an authenticated chart, enclosure and physical scaling. The elementary
bound itself needs no topology, compactness, Haar measure, primitivity,
Pisot condition or integral-incidence injectivity. Those stronger inputs
may be used elsewhere to construct its supplied geometric data.

It does not construct that data for every Pisot substitution, identify
all named numerical certificates with an actual real chart, prove a
common compact tile attractor, derive a compact-Haar recurrence, prove
strict-root positive measure, or exclude every critical overlap component.
Incoming completeness also supplies no forward-closure theorem. The
existing `00/11/22` inverse-closed but forward-leaking countercontrol
remains applicable, as do the existing boundary and omitted-occurrence
controls.

## 3. Replay and acceptance

The production aggregator imports both new modules. The generated proof
bank inventories every named theorem and checks that every local module
is reachable. The canonical acceptance command is

```bash
python3 tools/make_proof_bank.py --check
./tools/check_lean.sh
./tools/verify_all.sh provenance
```

`check_lean.sh` prepares a fresh isolated source workspace, provisions the
pinned Lean/mathlib inputs, builds the full production import, and audits
every compiled local declaration. It rejects missing source declarations
and any axiom outside `propext`, `Classical.choice` and `Quot.sound`.
Cached local module builds are development diagnostics, not substitutes
for this acceptance run.

Exact source-head, workflow and compiled-audit receipts are recorded in
the associated pull request after the jobs complete. No pass is inferred
from the presence of theorem source or a pending job. Independent human
mathematical review remains separately pending.

This increment adds deductive interfaces and controls. It changes no
canonical Mojo algorithm, enumerated source corpus, vendored dependency,
or governed C4/G1/PSC claim status.

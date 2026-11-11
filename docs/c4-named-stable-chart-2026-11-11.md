# C4: authentic named stable coordinates and compact actual prefix tiles

This continuation instantiates the analytic premises of
[the stable-prefix window theorem](c4-stable-prefix-window-2026-11-11.md)
for the two literal substitutions `1/021/001` and `1/012/001`. It builds
on mechanically certified source `8f1df32902c248baec35546e22e9145a2ea1a138`
in [PR #543](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/543).
Its own exact compilation and replay acceptance is recorded in its
implementation PR; the earlier receipt does not cover these new modules.

The [targeted source gate](c4-named-stable-chart-literature-2026-11-11.md)
was committed before implementation locally as `16c64602` and published
with the identical tree as
[`1d2c130c`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/1d2c130ca18baf4e337d7901531bb10d7121e585).
The standard stable-projection, contraction and finite-dimensional
topology machinery is not claimed as new. The contribution is the exact
named formal instance, its literal-word binding and the scope controls.

## 1. A real root and the actual incidence

The common integer incidence is

\[
M=\begin{pmatrix}0&1&2\\1&1&1\\0&1&0\end{pmatrix},
\qquad \det M=2.
\]

Let `f(t)=t^3-t^2-2t-2`. The canonical native certificate's exact
48-step bracket is

\[
L=638816140918905/281474976710656,
\qquad U=638816140918906/281474976710656.
\]

`NamedStableChart` proves `2<L<U<5/2` and the strict endpoint signs with
kernel-checked rational arithmetic. The intermediate-value theorem
constructs `beta` inside that interval. Factoring `f(x)-f(y)` proves
uniqueness of the root on `[2,infinity)`. A floating approximation,
sampled prefix cloud, supplied algebraic-number certificate or
uninterpreted root parameter is not a premise of the named theorems.

Define

\[
a=(3\beta-\beta^2)/2,
\quad b=(\beta^2-\beta-2)/2=1/\beta,
\quad c=\beta^2-\beta-1.
\]

The real coordinate space is exactly `Stable := Fin 2 -> Real` with its
sup norm. The integer projection is obtained by casting into the real
three-dimensional space and applying

\[
Wz=(z_0-a z_1,z_2-b z_1),\qquad
B=\begin{pmatrix}-a&2-a\\-b&-b\end{pmatrix}.
\]

The formal algebra proves `W M = B W`. The positive right vector
`r=(a,1,b)` satisfies `M r=beta r`; the positive left row
`ell=(1,beta,c)` satisfies `ell M=beta ell`. Thus the numerical chart
is bound to the actual incidence and its expanding eigenline.

## 2. Quotient coordinates and the genuine stable plane

The simple section `J(u,v)=(u,0,v)` satisfies `W J=I`, and

\[
Wz=0\quad\Longleftrightarrow\quad z=z_1r.
\]

These identities authenticate full rank and the exact kernel. They do
not assert that the image of `J` is the stable plane. For example,
`ell(J(1,0))=1`, so that image is not contained in `ker ell`.

The correct section is

\[
\kappa=\ell r=4\beta-\beta^2>0,\qquad
L(y)=J(y)-\frac{\ell(J(y))}{\kappa}r.
\]

The formal identities are

\[
\ell(L(y))=0,\qquad W L(y)=y,
\]
\[
z=L(Wz)+\frac{\ell z}{\kappa}r,\qquad
M L(y)=L(B y).
\]

Consequently `W` and `L` identify the real coordinates with the invariant
plane `ker ell`. The block contraction below authenticates the stable
action in those coordinates. The value `kappa` here is an algebraic
normalization in an inverse formula; this proof does not supply a Haar
normalization or a covolume theorem.

The coordinate sup norm is a specified norm on this plane through its
coordinates. It is not automatically the ambient sup norm, the canonical
quotient norm, or the Euclidean norm. An algebraically conjugate chart
can change its operator bound unless the norm is transported too.

`det B=2*b` is nonzero. Finite-dimensional real linear topology therefore
supplies the closed embedding required by the existing closure-equation
interfaces. Independently, `det M=2` gives injectivity of the original
integral incidence and hence the already proved compactness/injectivity
facts for the original matrix-adic carrier `H_M`.

## 3. A universal block-twelve contraction

The integer matrix power is proved exactly:

\[
M^{12}=\begin{pmatrix}
3941&8945&7415\\
4755&10791&8945\\
2095&4755&3941
\end{pmatrix}.
\]

Intertwining and `W J=I` give `B^n=W M^n J`, so

\[
B^{12}=\begin{pmatrix}
3941-4755a&7415-8945a\\
2095-4755b&3941-8945b
\end{pmatrix}.
\]

The exact root bracket implies the following convenient rational bounds:

\[
2.26953084\le\beta\le2.26953085,
\quad0.8289111\le a\le0.8289112,
\quad0.4406196\le b\le0.4406198.
\]

These displayed terminating decimals denote exact rationals. Lean uses
their integer numerators and denominators, not floating-point arithmetic.
The four absolute matrix entries are bounded by

\[
\begin{pmatrix}19/40&2/5\\3/20&7/20\end{pmatrix}.
\]

Their row sums are at most `7/8` and `1/2`. A proved two-dimensional
triangle-inequality argument then establishes

\[
\forall x\in\mathbb R^2,\qquad
\|B^{12}x\|_\infty\le(7/8)\|x\|_\infty.
\]

This is a universal real-vector theorem, not a finite sample of vectors
and not a matrix-norm instance selected by notation. The formal proof
uses the actual composition power of `AddMonoid.End Stable` and the
actual absolute row sums.

For contrast within the proof scope, the literal period-two action has

\[
B(1,-1)=(-2,0),\qquad B^2(1,-1)=(2a,2b).
\]

Since `2a>7/8`, it does not satisfy the same contraction estimate. The
word period must remain separate from the useful contraction exponent.

## 4. Actual words and compact prefix closures

For each literal substitution `sigma`, form its period-two substitution
and the productive prolonging seed `[0]`. The images of that seed are
respectively `021` and `012`; nonerasure and strict growth construct the
actual infinite words through `PrefixAddress.seedWord`.

Each word satisfies the full fixed-prefix identity at period two. The
already proved period transfer gives fixedness of the same word at
block twelve. Equal incidence is used for the shared real chart, never
to identify the two literal words. The carrier remains the original
`H_M`, not an unproved replacement by `H_(M^12)`.

Let

\[
D_\sigma=\operatorname{digitNormSum}(\sigma^{12},\pi),
\qquad R_\sigma=8D_\sigma.
\]

The complete finite digit sum bounds every literal depth-twelve digit
internally. Applying the accepted all-prefix theorem gives, for every
natural number `n`,

\[
\|\pi(\operatorname{parikhZ}(w[0,n)))\|\le R_\sigma.
\]

The finite-dimensional real coordinate space is proper. Its closed ball,
together with the compact original `H_M`, therefore contains every raw
prefix point. The defined letter-indexed closures are compact. Where
the existing period-two tile equation is used, the corresponding action
is `A^2`; the enclosure is supplied by `B^12` without changing the word.

This qualitative radius is not the numerical radius forty. The existing
native code checks all 55,583 depth-twelve digits per control against a
bound of five, but the present named Lean compactness proof does not
decode that hull certificate or claim the sharper bound. Authenticating
that bound remains useful for a smaller computational ancestor box.

## 5. Independent bounded controls and source binding

`proof/quint/C4NamedStableChart.qnt` checks the matrix-norm and chart
assumptions in a separate bounded integer model. Its 22 named tests
include 81 signed two-by-two matrices, 25 two-dimensional vectors,
2,025 matrix/vector pairs, 54,675 rational-contraction parameter tuples,
625 section-identity tuples and 3,125 commutation-extension tuples.
These are exact full domain sizes, not counts of accepted premises or
random simulation samples. The chart controls use separate integer
examples and do not represent the named algebraic root.

Ten intentionally incorrect models must fail at their named reached
assertions. Controls reject column sums or entrywise maxima in place
of row sums, missing absolute values, a missing second row, `q=1`, a
zero denominator, substituted matrices, wrong block exponents, a zero
projection and omitted incidence commutation. Additional controls
distinguish a raw section from a stable-plane section, an inherited
quotient norm from the chosen coordinate norm, and a changed coordinate
normalization from its copied contraction constant.

One invertible rational control is

\[
T=\begin{pmatrix}3/5&3/5\\1/10&0\end{pmatrix}.
\]

Its maximum column sum is `7/10`, and its largest absolute entry is
`3/5`, but `norm(T(1,1))=6/5` in the sup norm. Thus even injectivity
does not rescue either wrong norm certificate. The coordinate-rescaling
control conjugates `[[1,1],[0,1]]/4` by `diag(4,1)`; its copied row bound
of `1/2` fails after the conjugacy.

The provenance runner checks the complete test inventory, exact Quint
version `0.33.1`, TypeScript backend and seed `20261111`, captures a
private source snapshot, and rechecks source bytes and Git revision.
Each mutant must reach its intended `QNT508` failure. Type errors,
missing tests, timeouts and tool failures do not count as rejection.
The hosted workflow additionally binds the full clean checkout and
rechecks revision and tracked cleanliness after execution.

The unchanged stable-prefix native workflow is triggered by these Lean
changes. It replays the canonical cylinder, density and literal-prefix
contracts and the independent actual-packet oracle. Its source manifest
binds the native sources it executes. The new named Lean modules are
bound by the separate complete fresh-source Lean build and axiom audit.
No additional canonical native algorithm is introduced here.

Replays:

```bash
./tools/check_lean.sh
python3 tools/check_c4_named_stable_chart_quint.py --output /tmp/named-chart-quint
python3 tools/check_c4_stable_prefix_window_quint.py --output /tmp/prefix-window-quint
./tools/verify_all.sh provenance
```

Canonical native and independent oracle commands remain in the
[stable-prefix window note](c4-stable-prefix-window-2026-11-11.md).
Published exact-head job and artifact receipts belong to the
implementation PR. Local probes are development feedback only.

## 6. Next composition and remaining claims

The independent work in
[PR #544](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/544)
derives a finite mathematical ancestor carrier from supplied full-chart
reconstruction and enclosure premises. Its exact accepted source must
be checked before composition. The real reconstruction here and the
actual-prefix enclosure supply concrete inputs to that route; they do
not alone establish every ambient-coordinate and admissibility binding
for a combined named theorem or an executable finite constructor.

Forward completeness, nonunit product-Haar scaling, the actual
overlap-measure recurrence and positive strict-root measure remain
separate obligations. No full adelic identification, common attractor,
pure discrete spectrum or universal PIP constructor is asserted.
General C4, G1, Concentration and PSC remain open in the project; no
governed claim is promoted. Independent human review remains separate
nonblocking validation debt.

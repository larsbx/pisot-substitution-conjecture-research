# Class-A boundary-ray signs and typed occurrence kernels — 2026-10-26

**Scope:** extension of [PR #346](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/346), within the still-open class-A strip of [Issue #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139). Exact infinite-parameter *spectral/geometric* certificate and literal indexed-prefix identity, **not** an infinite boundary-hitting certificate. Human review pending. Uses [existing non-unit literature/stop-go](class-a-gap-uniformity-stopgo-2026-10-23.md), and does not use a new external transfer.

## Work shown

### Assumptions and hypotheses

`eps=±1`, `k,t>=0`; parameterise `n=k+3+t` for minus and `n=2(k+2)+t` for plus. Set `d=2n+6eps+5-k`. These are admissible determinant-two class-A PIP parameters with `n<d`; the substitution images are `xy^(n+d)x`, `cy^nx`, `xy^(n+eps)c`. All calculations use integer/Rational polynomial arithmetic, no global unimodularity or unproved independence.

### Derivation / reduction

Let
$
f(X)=X^3-(n+3+\varepsilon)X^2+(n-d+2+3\varepsilon)X-2\varepsilon,
\qquad m=k+2.
$
The characteristic polynomial satisfies `f(-1)=-(k+1)`, `f(1)=-d`, `f(2)=-2(n+d)`, `f(-2)=-2(n+k+7)`.
The numerator of the rational bracket is
$
n^3 f(-1+m/n)=n^3+(4-\varepsilon)mn^2-(6+\varepsilon)m^2n+m^3.
$
After substituting the appropriate `n` above, this numerator is a polynomial in `t,k` with **strictly positive constant coefficient and nonnegative coefficients**, as are `-f(n+2),f(n+3)` (minus) and `-f(n+4),f(n+6)` (plus).

An independent coefficient-level audit can use the following **fully expanded** expressions, all in the nonnegative cone of \(\mathbb Z[t,k]\):

| sign | \(n^3 f(-1+m/n)\) |
|---|---|
| \(-1\) | \(t^3+(8k+19)t^2+(8k^2+48k+67)t+2k^3+20k^2+64k+65\) |
| \(+1\) | \(t^3+(9k+18)t^2+(17k^2+68k+68)t+7k^3+42k^2+84k+56\) |

The real Perron-bracket endpoint signs reduce to:

| sign | negative endpoint (strictly positive after negation) | positive endpoint |
|---|---|---|
| \(-1\) | \(-f(n+2)=t^2+(k+8)t+3k+13\) | \(f(n+3)=k^2+kt+9k+3t+20\) |
| \(+1\) | \(-f(n+4)=t^2+(3k+18)t+2k^2+28k+82\) | \(f(n+6)=t^2+(5k+20)t+6k^2+50k+98\) |

Every row is strictly positive for all \(t,k\ge0\); the kernel independently reconstructs and checks the underlying identities without trusting this human-readable table. The canonical Mojo kernel constructs these expressions independently in `QX=Q[t,k]` and checks the equality and the coefficient signs, not just samples. The remaining signs `f(0)=2` (minus), `f(0)=-2` (plus), `f(1)<0` prove three disjoint real roots, with the positive Perron root respectively in `(n+2,n+3)` and `(n+4,n+6)`. The four nonzero integer evaluations at ±1,±2 show irreducibility by the rational-root theorem. Primitivity follows from positive `M^2` for these parameters.

**Strengthened boundary-chamber statement.** Let `beta` be the root above and `u=d/(beta-1)`. Minus: `d-(n+2)=t>=0`; plus: `d-(n+5)=k+t+10>0`. Since `beta< n+3` (minus) or `beta<n+6` (plus), `u>1` **for all** these `k,t>=0`, including the minus floor `n=k+3`. This improves the conservative statement in the parent note, which only asserted minus `u>1` for `n>=k+4`.

The second kernel models each actual symbolic **first/run/last** occurrence address, including `RUN` proper-prefix bounds `1<=j<=run` and `LAST` index `run+1`, for each parent letter. It checks the full bottom-minus-top Parikh recurrence `w'=Mw+prefix_bottom-prefix_top` in three coordinates. For the seed `(x,c,w=0)`, the run-1/1 paired letters are both `y`, but their residual is `(-1,1,0)`. Consequently the y/y intervals are separated by `L_x-L_c=d*h*(1+h)=u L_y>L_y`. The candidate **is not an interior overlap edge**, notwithstanding identical child letters. The first-child 0/0 selection is the genuine `(x,c,0)` loop, but it has other possible children and is not a strict or target-free component theorem. A second LAST/LAST case has residual `(-1,1,-eps)`.

### Evidence and replay

Canonical source: `kernel/psc/class_a_boundary_signs.mojo` (exact infinite-cone inequalities) and `kernel/psc/class_a_boundary_occurrences.mojo` (typed indexed word-prefix transport). Driver `kernel/class_a_boundary_kernels.mojo`. Native regressions `kernel/tests/test_class_a_boundary_kernels.mojo` verify two actual substitutions with existing `build_seed_overlap_tables_screened`, `selected_overlap_child`, and `interior_overlap`; independent Python `tests/test_class_a_boundary_chamber.py` compares exact rational endpoint inequalities on 32 sample parameters. Dedicated hosted CI: `.github/workflows/class-a-boundary-kernels.yml`.

From `kernel/`:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_kernels.mojo
pixi run --locked mojo run -I . class_a_boundary_kernels.mojo
```
From repository root:
```sh
python -m pytest -q tests/test_class_a_boundary_chamber.py
```
The proof is symbolic in `t,k`; finite Python and real-geometry specimens are regression controls, not its quantifier source.

### Negative controls

The verifier refuses determinant sign 0, a mutated coefficient of the rational endpoint identity, a mutated Parikh residual, nonexistent run ordinal 0, and run index beyond the final y. Native Perron-field geometry independently rejects both same-letter run-1/1 pairs as disjoint, while accepting the actual aligned (x,c,0) seed and its first-child loop. The earlier `n>=5d` u<=1/5 certificate and its box cannot be transplanted to this u>1 chamber; a same-letter quotient is also insufficient.

### Non-claims / remaining gaps

This is a **structural exclusion** of one syntactically available child, not a guarantee that any other child eventually hits offset zero. No uniform interior target-aware packets, no all-child strict carrier closure/descent, no C4 ordered hub-residual alignment, no universal BH, A1′, G1 or PSC. The existing finite BPA proxy in PR #346 remains a weaker diagonal-reachability calculation. A merge or passing CI is not final human validation.

**Next acceptance target:** derive all geometrically realizable indexed child types for an unbounded `k,t` chamber, then exhibit a symbolic well-founded descent or a uniform obstruction contradiction with strict interior/boundary guards. Reuse `class_a_gap_uniform` / existing perron field and target-packet kernels; do not infer word-level realization from `Q[t,k]` identities.


## A complete exact y/y run-pair classification for the aligned (x,c,0) seed

**Scope:** theorem about *all paired run children of this one parent state* for the boundary-ray families; not all children of the seed, not a claim that the recurrent first-child loop is closed, and not an occurrence-indexed hit.

Write \(i\) for a genuine top y-run index of \(\sigma(x)\), \(j\) for a genuine bottom y-run index of \(\sigma(c)\). Thus

\[
1\le i\le n+d,\qquad 1\le j\le n,\qquad m=j-i\in\mathbb Z.
\]

At source shift zero, the physical start of the top run child is \(L_x+(i-1)L_y\), while that of the bottom child is \(L_c+(j-1)L_y\). Their shift is

\[
L_c-L_x+(j-i)L_y=(m-u)L_y,\qquad u=\frac d{\beta-1}.
\]

Since both children have length \(L_y>0\), their interiors overlap **if and only if** \(\lvert m-u\rvert<1\). This is a literal geometric test after the symbolic occurrence indexes have passed the word-bounds check; quotient letter agreement alone is insufficient.

For \(\varepsilon=-1\), the already proved Perron interval \(\beta\in(n+2,n+3)\) and \(d=k+2t+5\) give
\[
1<u<\frac d{n+1}<2,\qquad 2(n+1)-d=k+3>0.
\]
Therefore the **only** possible integer index differences of strict y/y run overlaps are \(m\in\{1,2\}\).

For \(\varepsilon=+1\), the interval \(\beta\in(n+4,n+6)\) and \(3(n+3)-d=3k+t+2>0\) establish \(1<u<3\). To decide the exact integer chamber, put \(X=1+d/2>1\). The characteristic polynomial has its two other roots strictly inside \((-1,1)\); therefore
\[
\operatorname{sgn} f(X)=\operatorname{sgn}(X-\beta),\qquad
\operatorname{sgn}(u-2)=\operatorname{sgn}(X-\beta).
\]
Clearing the positive denominator,
\[
\begin{aligned}
F(t,k)=8f(1+d/2)
={}&-9k^3-12k^2t-93k^2-4kt^2\\
&-44kt-15k+12t^2+256t+1349.
\end{aligned}
\]
For \(k=0,1,2,3\), the four exact polynomials are
\[
\begin{array}{c|l}
k & F(t,k)\\\hline
0 & 12t^2+256t+1349\\
1 & 8t^2+200t+1232\\
2 & 4t^2+120t+875\\
3 & 16t+224
\end{array}
\]
and are positive for every \(t\ge0\). For \(k=4+q\), \(q\ge0\),
\[
-F(t,4+q)=9q^3+12q^2t+201q^2+4qt^2+
140qt+1191q+4t^2+112t+775>0.
\]
Every inequality is established by nonnegative integer coefficients and a positive constant; no floating point, sampled roots, or limiting argument is used. The kernel independently constructs \(F\) from the characteristic polynomial and verifies this finite partition of the infinite \((k,t)\) cone. Thus
\[
\boxed{
\begin{array}{c|c|c}
\varepsilon & \text{parameter chamber} & \text{exactly the allowed relative run differences }m=j-i\\\hline
-1 & k\ge0 & \{1,2\}\\
+1 & 0\le k\le3 & \{2,3\}\\
+1 & k\ge4 & \{1,2\}
\end{array}}
\]
The listed differences **pass the strict geometric intersection test when the actual run indices exist**; this does not claim a complete seed child enumeration or any successful continuation path.

Canonical Mojo: \`kernel/psc/class_a_boundary_run_pairs.mojo\`. The expanded \`kernel/tests/test_class_a_boundary_kernels.mojo\` validates actual selected child indices against the exact Perron overlap predicate for \((\varepsilon,n,d,k)=(-1,4,7,0),(+1,4,19,0),(+1,12,31,4)\); it also requires refusal on corrupt \(F\) and negative \(k\). Reproduction uses the same locked native commands above.

**New remaining target:** classify first/run, run/last, and first/last children and the adjacent self-run families before synthesizing a *full* child carrier and a descent. The table is a precise word-and-geometry filter for one source state, not a global nonproductive SCC argument.

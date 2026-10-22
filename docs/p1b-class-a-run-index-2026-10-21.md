# Issue #139: class-A run-index investigation (2026-10-21)

Status: scoped written proof and finite investigation; no universal boundary-hitting promotion.
Accepted class-D integration at main `d46ebe6` is a dependency, not a gate to
reopen. Independent human review remains pending and nonblocking for progress.

## Targeted literature stop/go (before implementation)

Proposed experiment: on class A, `(p,q,r)=(n+1,n,n+1)`, reconstruct the complete
canonical swap-seed graph exactly. Preserve ordered occurrence indices and
integral offsets, and test whether the growing run-indexed states admit a
parameter-independent hitting rank. Seek a uniform vertex-family argument or
an exact countermodel to a proposed finite quotient/rank reduction. A sampled
bound is not a uniform bound; failure of a proposed reduction is not a failure
of boundary hitting.

The existing September 21 and October 7 literature gates and the side-notes
ledger have been read. Three primary sources were re-inspected on October 21:

- Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine
  tilings*, [arXiv:1003.2898](https://arxiv.org/pdf/1003.2898), §3–4,
  Theorem 4.1: a finite overlap decision under the Meyer/tiling hypotheses.
  Neither a family-uniform depth nor seed-graph realization follows merely
  from this algorithm. Our object remains the repository swap-seed graph.
- Minervino–Thuswaldner, *The geometry of non-unit Pisot substitutions*,
  [arXiv:1402.2002](https://arxiv.org/pdf/1402.2002), representation space and
  Theorem 9.9: finite places are required, and the tiling conclusion assumes
  geometric property (F) as well as strong coincidence. No pointwise hit is
  imported from a multiple tiling or Archimedean contraction alone.
- Barge, *Pure discrete spectrum for a class of one-dimensional substitution
  tiling systems*, [arXiv:1403.7826](https://arxiv.org/pdf/1403.7826),
  Theorem 3.13: initial-letter injectivity is required. Class A has initial
  map `(x,c,x)`, hence is not injective; no power repairs this collision.
  The theorem cannot supply the missing family argument here.

Decision: **proceed with the narrowed vertex-family / hitting-rank target**.
Reuse the exact overlap engine, not the already unsuccessful constant-size
symbolic graph search. Retain capped/non-PIP refusals, strict endpoint
geometry, orientation and altered-occurrence controls. All computations are
exact integer/field computations; they do not approximate the adelic space.

## Exact residual families and seed configurations

Use the existing letters `(x,c,y)=(0,1,2)`, and offsets **bottom minus top**.
In A/C, `sigma(x)=x y^p x` and `sigma(c)=c y^q x`. Put `d=p-q` and
`s in {-1,+1}`. The determinant-two PIP domains have the following exact
integer descriptions (including nonnegativity):

| Class | Third image | Domain | Previously certified infinite lines |
| --- | --- | --- | --- |
| A | `x y^(q+s) c` | `q>=0`, `q+s>=0`, `1<=d<=2q+6s+5` | `p=2q+k`, `k=0,1,2,3`, both signs |
| C | `c y^(q-d+s) c` | `d>=1`, `q>=0`, `q>=d-s`, `q>=2d-3s-2` | `d=1,2,3`, both signs |

Derivation: the characteristic cubics are respectively

$$
f_A(t)=t^3-(r+3)t^2+(2+3r-p-q)t-2(r-q),
$$
$$
f_C(t)=t^3-(r+3)t^2+(2+3r-2q)t-2(p-2q+r).
$$

The determinant pins `r=q+s` in A and `r=q-d+s` in C. The repository's
necessary inequalities `f(1)<0`, `f(-1)<0` give the domains above.
They are sufficient here too: `f(2)=-2p<0` and `|det|=2` put the other
roots in the open unit disc by the existing cubic Jury argument. There is
no rational root: `f(1),f(-1),f(2)` are strictly negative; in A,
`f(-2)=2d-6q-12s-24<0`, and in C,
`f(-2)=10d-6q-12s-24<0` by the displayed bounds. Rational roots could only
be `±1,±2`. Primitivity follows from `x -> y -> c -> x` and the x self-loop.
These descriptions concern these two normal-form classes, not every PIP
substitution.

Remove the displayed certified lines from each domain to obtain the residual
**uniform family obligations**. Individual small members may already have
finite-domain certificates; that does not cover a residual infinite family.
Class D's accepted certificates apply to different endings and determinant
relations and do not cover these residuals.

All three canonical swap seeds `(xc,cx)`, `(xy,yx)`, `(cy,yc)` matter, including
their nonzero-offset descendant configurations. Theorem E settles aligned
coincidence here. The remaining statement is that every reachable nonzero
cyclic state has an offset-zero descendant. Changing the seed, erasing the
run index, or retaining a selected cycle without its productive exits does
not prove that statement.

We choose the least positive gap `d=1`, plus sign, in A:

$$
\sigma_n(x)=xy^{n+1}x,\qquad
\sigma_n(c)=cy^n x,\qquad
\sigma_n(y)=xy^{n+1}c.
$$

It is a one-parameter unresolved *uniform* case, even though small individual
members are known. The prefix convention and exact graph are unchanged.

## Uniform result on an explicit recurrent family

**Proposition (repository-proved, scoped written proof with coefficient-checked Mojo identities;
independent human review pending).** For every integer `n>=4`, define

$$
A_n=(c,y,n,-n,0).
$$

This is a genuine swap-seed-reachable recurrent overlap. If `L_n` is its
least offset-zero hitting depth, then

$$
\boxed{\quad n/10<L_n\le n+2.\quad}
$$

Thus a parameter-independent finite hitting-depth bound on this class is
false. This refutes the proposed fixed-`K` route in the historical progress
note §5.4, not boundary hitting. The upper bound is a reusable uniform
run-index descent, but only on the explicit family below, not on every state.

### 1. PIP and the Perron geometry

The incidence matrix and characteristic polynomial are

$$
M_n=\begin{pmatrix}2&1&1\\0&1&1\\n+1&n&n+1\end{pmatrix},
\qquad f_n(t)=t^3-(n+4)t^2+(n+4)t-2.
$$

The matrix is primitive (the directed cycle and self-loop above). For `n>=4`,

$$
f_n(0)=-2,\quad
n^3 f_n(1-2/n)=n^3-2n^2-4n-8>0,\quad f_n(1)=-1.
$$

The middle numerator at `n=4+h` is `h^3+10h^2+28h+8`, with positive
coefficients. Also

$$
f_n(n+2)=-n^2-2n-2<0,\qquad f_n(n+3)=n+1>0.
$$

There are therefore three distinct positive roots in the three disjoint
intervals `(0,1-2/n)`, `(1-2/n,1)`, `(n+2,n+3)`. The latter is the Perron
root `beta`. None of `±1,±2` is a root (`f_n(-1)=-2n-11`,
`f_n(-2)=-6n-34`, `f_n(2)=-2n-2`), proving irreducibility and Pisot.

Normalize the physical tile lengths by `ell_y=1`. Then

$$
\ell_x=\frac{n+1}{\beta-2},\quad
h=\ell_x-\ell_c=\frac1{\beta-1},\quad
\ell_c=\ell_x-h.
$$

Consequently `h>0`, `(n+1)h<1`, `ell_x>1`, and `ell_c>nh`.
These strict inequalities certify all the overlap geometry used next.

### 2. Seed reachability, recurrence and constructive exit

Write `A_k=(c,y,k,-k,0)`, `Y_k=(y,y,k,-k,0)` and
`B_k=(y,x,k,-k-1,1)`. Their physical shifts are respectively
`kh`, `kh`, and `kh-ell_c+1`. The inequalities above prove strict interiority
for `A_k (0<=k<=n)`, `Y_k (0<=k<=n+1)` and `B_k (0<=k<=n)`:
for example, B's two margins are `1+(k+1)h` and `ell_c-kh`.

Every edge below retains its ordered **zero-based** child indices. The
update is exactly `w'=M_n w+pi(bottom prefix)-pi(top prefix)`.

| Source | Child indices `(top,bottom)` | Target | Range |
| --- | --- | --- | --- |
| `(c,x,-1,1,0)` | `(0,1)` | `(c,y,0,1,-1)` | `n>=4` |
| `(c,y,0,1,-1)` | `(0,1)` | `(c,y,1,0,-1)` | `n>=4` |
| `(c,y,1,0,-1)` | `(1,1)` | `Y_2` | `n>=4` |
| `Y_k` | `(n+2,n+2-k)` | `A_k` | `2<=k<=n` |
| `A_k` | `(k+1,1)` | `Y_(k+1)` | `2<=k<n` |
| `A_k` | `(k,0)` | `B_k` | `1<=k<=n` |
| `B_k` | `(n+2,n+1-k)` | `A_k` | `0<=k<=n` |
| `B_k` | `(k+1,0)` | `B_(k-1)` | `1<=k<=n` |
| `B_0` | `(2,1)` | `(y,y,0,0,0)` | `n>=4` |

The initial state is exactly the overlapping second/second tile pair in
`(xc,cx)`; its margins are `ell_c,ell_x`. The next two bootstrap states
have margins `(ell_c,1)` and `(ell_x,1-h)`. Thus they are genuine, too.
Every listed index is a legal proper-prefix occurrence in the displayed
range (last y-image index is `n+2`, c-run indices are `1..n`, x/y runs
are `1..n+1`). No all-child closure assumption is used for these paths.

Four bootstrap steps give A_2; the ladder reaches A_n after `2n` steps.
The pair `A_n -> B_n -> A_n` is an actual two-cycle. Its productive exit is

$$
A_n\longrightarrow B_n\longrightarrow B_{n-1}\longrightarrow\cdots
\longrightarrow B_0\longrightarrow(y,y,0,0,0),
$$

of length `n+2`. Rank `k+1` on B_k is a uniform formula, not a uniform
constant. This also shows why exhibiting a zero-shift-free cycle is not a
counterexample to BH: the cycle has an exit to coincidence.

### 3. A lower bound for every possible address

Let `alpha` be the real contracting root in `(1-2/n,1)`. The polynomial row

$$
\lambda(t)=\big((n+1)(t-1),\ n(t-1)+1,\ (t-2)(t-1)\big)
$$

satisfies `lambda(t)M_n=t lambda(t)` at every root of f_n. Mojo checks the
first two identities exactly and that the third defect is `-f_n(t)`.
Moreover `lambda_x(t)-lambda_c(t)=t-2`.

At `t=alpha`, `-5/2<lambda_x<0`, `-1<lambda_c<1`, and
`0<lambda_y<3/n`. Every proper prefix is either empty or one x/c followed
by at most `n+1` y's. Its lambda-value is in `(-3,5)`, so any difference
of two proper-prefix values has absolute value **strictly less than 8**.
This bound covers every occurrence choice, not just the selected edges.

For any m-step path from A_n the contracting value obeys

$$
z_m=\alpha^m n(\alpha-2)+
\sum_{i=0}^{m-1}\alpha^{m-1-i}d_i,\qquad |d_i|<8.
$$

If it reaches offset zero, `z_m=0`, hence
`n alpha^m < 8m`. Bernoulli's inequality gives
`alpha^m >= (1-2/n)^m >= 1-2m/n`. Thus a hit with `10m<=n` would imply
`n-2m<8m`, a contradiction. This proves `L_n>n/10`.

For any proposed constant K, choose integer `n>=max(4,10K)`. The explicit
seed-reachable recurrent A_n cannot hit in K steps, yet it does hit by n+2.
This is a uniform obstruction theorem, not a necessary-condition sieve or an
extrapolation from the depth table. A single Archimedean conjugate suffices
to obstruct a finite exact equality; it is **not** used to assert adelic
coverage or force a hit. The constructive upper path supplies that separately.

## Comparison with the accepted class-D mechanisms

Both classes have determinant magnitude two, exact ordered affine updates,
strict Perron geometry, and the same finite-place obligations. Class D used
finite parameter chambers, covered carriers and rank descents; the accepted
minus carrier and plus chamber certificates remain untouched.

The crucial difference here is the explicit recurrent run-index family:
`alpha_n -> 1` and `L_n -> infinity`, with all members reachable from a
canonical seed. A fixed set of ranks with a parameter-independent maximum
cannot cover it. A finite list of vertex **families** with an integer rank
can: B_k supplies a concrete example. The remaining A task is to cover every
reachable configuration and connect it to such a family with proved descent.
The residual C domain above still needs its own coverage/recurrence proof;
no A conclusion is transferred merely because both have determinant two.

## Exact executions and replay

Canonical code: `kernel/psc/class_a_run_index.mojo`; driver:
`kernel/class_a_run_index.mojo`; controls:
`kernel/tests/test_class_a_run_index.mojo`.

| n | Complete seed vertices | Maximum first hit | Recurrent vertices | L(A_n) |
| --- | ---: | ---: | ---: | ---: |
| 1 | 181 | 4 | 178 | 3 |
| 4 | 275 | 5 | 272 | 5 |
| 8 | 435 | 8 | 432 | 8 |
| 12 | 595 | 11 | 592 | 10 |
| 16 | 755 | 13 | 752 | 13 |
| 18 | 835 | 15 | 832 | 14 |
| 24 | 1075 | 19 | 1072 | 18 |

The raw survey records **every integer n=1..24**. Every graph completes below
the 20,000-state cap and every vertex reaches offset zero. Coincidences are
terminal, so the recurrent counts exclude those terminal vertices. The
maximum is also attained by a recurrent state in every sampled graph.
These are finite observations; neither the observed vertex-count formula nor
a fitted exact depth formula is claimed for all n.

The n=18 export contains all 835 integral labels, exact first-hit depths, swap
seeds and 17,178 ordered edges. The independent Python Fraction-field oracle
rebuilds the graph using its nested occurrence scan and rational root
isolation, matches every label/depth/seed/edge, and replays every occurrence
index with strict geometry. This is stronger than comparing just counts.

From `kernel/`:

```bash
pixi run --locked mojo run -I . tests/test_class_a_run_index.mojo
pixi run --locked mojo build -I . class_a_run_index.mojo -o /tmp/class-a-run-index
/tmp/class-a-run-index 24
/tmp/class-a-run-index family 64
/tmp/class-a-run-index export 18 > /tmp/class-a-n18.log
```

From the repository root:

```bash
python oracles/python/class_a_run_index.py /tmp/class-a-n18.log
python -m pytest tests/test_class_a_run_index.py
sha256sum -c evidence/class-a-run-index-2026-10-21/SHA256SUMS
```

The local runs use `Mojo 1.1.0.dev2026090805 (34562fa1)`, the locked version,
with the previously provisioned minimal runtime. The observed compiler hash
matches the accepted assembly's compiler hash. This session does not claim a
new full-Pixi installation or new CI acceptance. A dedicated workflow replays
the new work; it neither invokes nor reopens the accepted class-D gate.

### Negative controls

- An exhausted graph cap refuses a verdict; zero/oversized n budgets refuse.
- The singular `A(p,q,r)=(2,1,1)` is rejected by the exact PIP screen.
- Changed child index, reversed offset, wrong target letter and a corrupted
  symbolic closing edge all refuse.
- Endpoint-only contact is excluded. A zero-offset unequal-letter state is
  distinguished from coincidence.
- The independent reader rejects missing/duplicate occurrences, illegal
  indices, wrong depths, missing seeds and missing completion records.
- The two-cycle is a positive control for recurrence with an actual productive
  exit; it is not misreported as a closed bad SCC.

### Non-claims and next reproducible obligation

The uniform bound above is for the displayed A_k/B_k/Y_k family and its
explicit seed/exit paths. The executable certifies coefficient identities;
the written proof supplies the all-parameter index, geometry and Bernoulli
inequalities. It is not Lean-formalized. Independent human review is pending.
No governed universal claim is promoted by this contribution.

The next obligation is a complete run-indexed cover of all descendants of
all three swap seeds for this A line, with every allowed child covered and
a productive descending choice. The present selected paths do not prove
that cover. Then address the remaining A domains and C's residual `d>=4`
region. General #139/#84/#138, universal aligned coincidence and general PSC
remain open. Accepted class-D integration is unchanged.

## Forward-cover continuation

The [rectangular cover countermodel](class-a-cover-obstruction-2026-10-21.md)
shows uniformly that strict geometry plus separate bounds on run index, y
offset and coordinate sum do not form a child-closed carrier. It provides
exact normalized coordinates and a real escaping edge; seed reachability is
not asserted. The arbitrary-n all-state cover and its descent remain open.

The arbitrary-n all-state cover and its descent on this line are supplied by
[class-a-carrier-closure-2026-10-22.md](class-a-carrier-closure-2026-10-22.md);
the other A regions and the C residual remain open.

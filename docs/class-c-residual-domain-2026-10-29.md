# Class C: exact PIP boundary and residual diagonal certificates (2026-10-29)

**Scope.** This note follows merged Theorem T_C (PR #384, merge
`40823631b1ed456509440263de9b100e596b314e`). It separates a
hand-proved, unconditional classification of the Pisot/irreducibility/primitive
(PIP) parameters from computer-assisted boundary hitting (BH).
The former does **not** depend on `psc.symbolic_cone`; the latter still does.
Nothing here proves pure discrete spectrum, G1 or the general PSC.

## 1. Exact PIP domain, no empirical lower endpoint

Set `p=n+d, q=n, r=n-d+eps`, where `eps in {-1,+1}`,
`d>=6`, and the three images have positive y-runs (`r>=1`).
The incidence matrix, in the convention of Theorem T_C, is

    M = [ [2, 1, 0], [0, 1, 2], [p, q, r] ].

Its characteristic polynomial is exactly

    chi(t) = t^3 - A*t^2 + B*t - 2*eps,
    A = n-d+eps+3,   B = n-3*d+3*eps+2.

**Theorem P_C (exact PIP domain).** Under these hypotheses, the substitution
is primitive, its characteristic polynomial is irreducible over Q and its
Perron root is Pisot **if and only if**

    plus:  n >= 2*d-5,
    minus: n >= 2*d+1.

These are *proved exact* lower endpoints, not profile extrapolations.
In particular **every member of the residual strips of T_C is PIP**.

**Proof.** The matrix has positive entries wherever permitted by the fixed
support and `M^2` is entrywise positive since `p,q,r>=1`. Its determinant
is `2*eps`. Direct integer substitution gives

    chi( 1) = -2*d,
    chi(-1) = 2*(2*d - 3*eps - n - 3),
    chi( 2) = -2*(d+n),
    chi(-2) = 2*(5*d - 6*eps - 3*n - 12).

Since `chi(2)<0` and `chi(t)` is monic, it has a positive root `beta>2`.
For the primitive nonnegative matrix this is the Perron root (or, equivalently,
its Perron root is at least this positive root, hence is itself >2).

*Necessity.* If the other two roots `a,b` lie strictly in the unit disc,
then `(1+a)(1+b)>0`: for two real roots both factors are positive;
for a nonreal conjugate pair it is a positive squared modulus.
Consequently
`chi(-1)=(-1-beta)(-1-a)(-1-b)<0`. This is equivalent to
`n>2*d-3*eps-3`, or `n>=2*d-3*eps-2` for integer n.

*Sufficiency.* Assume that strict integer bound. All four values of chi
displayed above are strictly negative: at `-1` by the bound, at
`1,2` directly, and at `-2` by substituting the minimal n:
`5d-6eps-3n-12 <= -d-3` (plus), `<=-d-9` (minus).
Every rational root of a monic integer cubic divides `2*eps`,
so none exists. Thus chi is irreducible. Factor over the ordered
algebraic extension at the chosen `beta>2`:

    chi(t) = (t-beta) * (t^2 + u*t + v),  v=2*eps/beta.

Then `|v|<1`. The two endpoint evaluations yield

    1+u+v = 2*d/(beta-1) > 0,
    1-u+v = -chi(-1)/(beta+1) > 0.

The elementary quadratic Schur/Jury criterion (`|v|<1` and both
`1±u+v>0`) puts both other roots strictly inside the unit disc.
Since the positive root >2 is then the unique root outside the unit disc,
it is beta, as required. This argument requires no cone-sign oracle,
sampling, limiting estimate or constant overlap labels. QED.

**Sharp negative controls.** The immediately preceding integers are
`n=2d-6` (plus) and `n=2d` (minus): `chi(-1)=0`, so reducibility
is witnessed by the exact root `-1`. Below them `chi(-1)>0`, excluding
the Pisot property. These are spectral, *not* BH counterexamples.

**A simpler sign partition for existing cone PIP checks.**
The sufficient dominant-coefficient (Rouché) margin is
`A-|B|-3`. For the residual strips it is strictly positive whenever
`n>=2d-2` (plus) or `n>=2d+2` (minus). The three plus boundary
lines `n=2d-5,-4,-3` and the one minus line `n=2d+1` need
the preceding exact endpoint/Jury argument. The split is not a
classification of overlap graphs. Crucially, `P_C` works even on
the latter four lines.

## 2. What was independently reproduced

An independent Python exact-arithmetic oracle lives in
`evidence/class-c-residual-domain-2026-10-29/exact_oracle.py`.
It builds every occurrence-pair child of a swap-seed graph (rather than
Mojo's sliding-window optimization), represents physical shifts in
`Z[beta]`, certifies every comparison by rational bisection of chi,
and converts each shift to the exact Parikh-offset coordinates.
No floating point, symbolic cone engine, external algebra package, or
sampling of signs is used. It refuses nonintegral offset reconstructions,
a graph over 20,000 states, and unsuccessful root isolation.
It tests *finite graphs*, not quantified BH.

Local independent finite results (complete graphs, all vertices hit
offset zero):

| eps | (d,n) | vertices | typed rows | significance |
|---:|---|---:|---:|---|
| +1 | (6,24) | 196 | 77 | T_C frozen tail |
| -1 | (6,28) | 214 | 81 | T_C frozen tail |
| +1 | (8,31) | 198 | 79 | T_C negative control, `n=4d-1` |
| -1 | (8,35) | 216 | 83 | opposite-sign negative control |
| +1 | (6,22), (7,26), (8,30) | 204 each | varies by typed rows | `n=4d-2` |
| -1 | (6,26), (7,30), (8,34) | 222 each | varies by typed rows | `n=4d+2` |
| +1 | (6,7) | 2432 | — | exact lower PIP boundary |
| -1 | (6,13) | 1283 | — | exact lower PIP boundary |

For the three-gap `-2` samples, the **complete normalized label sets**
(not merely vertex counts) agree within each sign; this is an experiment,
not a proof for all d. Both the 196/214 and 198/216 counts were reconstructed
independently, and the first typed rows agree with the T_C logs.
The exact certificate's quantified symbolic replay was **not** reproduced
on the local machine: Mojo is absent there. T_C's existing hosted result
and packet remain distinct evidence.

## 3. Independent audit of the symbolic cone trust boundary

Inspected at `kernel/psc/symbolic_cone.mojo` (main after #384):
- `Region.positive` shifts polynomials to a nonnegative orthant and accepts
  only a positive constant term and nonnegative coefficients after optional
  multiplication. This is a one-sided *sound* positivity witness, not a
  complete test; an undecided sign is not false.
- `Cone.sign_at_beta` requires matching strict endpoint signs; for a
  linear remainder this suffices; for a quadratic remainder, it additionally
  requires certified monotonicity or bending *away* from zero. The logic
  of those inequalities is sound if exact `param_poly` operations and
  bracket validation are correct.
- `certify_cone` tests primitive support, rational roots dividing
  determinant, strictly ordered positive-denominator brackets above
  `|det M|=2`, and Rouché or Jury guards. `P_C` now independently
  checks the PIP conclusion for *every* integer class-C parameter in scope.
- A run-position affine guess is sampled at three parameter values, but
  the returned fit is then required to satisfy strict/weak inequalities on
  the **entire** certified region. Consequently sample agreement alone
  is not used as a universal witness.
- The real remaining trusted surface is the exact implementation of
  `qx_shift/mul`, `tp_homog_at`, polynomial reduction, interval
  endpoint comparisons, run-index clipping, and seed closure; neither
  `P_C` nor the finite oracle proves those implementation details correct.
- `certify_piece` refuses a symbolic graph with nonconstant Parikh offsets
  **even when every symbolic vertex hits zero**. This is necessary for
  a uniform frozen-label theorem, but *not* for BH. The residual proof
  should keep BH reachability separate from the stronger frozen-label guard.
  A cone sign refusal is not evidence that BH fails.

## 4. Focused new BH candidate and next partition

The lines `n=4d-1` (plus) and `n=4d+3` (minus) are the first
below-onset diagonals. They have different, internally constant labels
(198/216) and existing T_C negative-control certificates for `d>=8`;
the companion Mojo replay
`kernel/class_c_residual_diagonals.mojo` attempts to extend each
to **every d>=6** by certifying that line and discharging `d=6,7`
with the exact capped kernel, with identical-label and BH checks.
This potential two-diagonal BH reduction is **conditional on native/hosted
successful replay**, not on the hand proof of `P_C`.

For the next cells, use `kernel/class_c_residual_probe.mojo` to run
`symbolic_cone_graph` on `c=-2,-3,...` diagonals, fixed-gap lines,
and shifted cones. Unlike `certify_piece`, this BH-only probe does not
require a constant symbolic label set. It still requires PIP, completed
closure, all-vertex zero reachability and an exact sample-graph comparison;
an undecided sign is a refusal, never a negative BH verdict.

Separate negative controls for any future cover must include different
label sets just above/below each crossing, independently reconstructed
boundary members and a bad-shift/refusal case. No constant-label claim
may cross the known `-1/0` boundary.

## 5. Replay, provenance and promotion

    python3 evidence/class-c-residual-domain-2026-10-29/exact_oracle.py --verify
    cd kernel
    pixi run --locked mojo run -I . class_c_pip_domain_check.mojo
    pixi run --locked mojo run -I . class_c_residual_diagonals.mojo 1
    pixi run --locked mojo run -I . class_c_residual_diagonals.mojo -1
    # BH-only exploratory candidate; output is NOT automatically a theorem:
    pixi run --locked mojo run -I . class_c_residual_probe.mojo 1 -2 8 0 diagonal

The complete audit/provenance depends on unchanged Theorem T_C at merged
PR #384 head `53dd9547cea65d3cdb1fa80c4e16f97b712aabd4` and the
exact source paths above. Local verification: Python `--verify` completed;
Mojo toolchain unavailable locally. CI is the native acceptance gate for
the new Mojo commands. Until CI passes, promotion of the new BH diagonal
claim is on HOLD. The hand-proved theorem P_C stands independently.

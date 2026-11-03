# Uniform Smith trichotomy for minus Class-A nonunit finite-place quotients

**Status:** new parameter-uniform **integral algebra** proof candidate, independent
machine-checked finite-level confirmation pending. **Not** a proof of the
Pisot Substitution Conjecture, BH (#139), A1′ (#138) or the Class-A
uniform-entry target (#452). Do not promote claim governance.

## Prior art and stopping rule

The repository already has the generic exact finite-cokernel kernel
`kernel/finite_linear_algebra/madic_ball.mojo` and its imported
`smith_normal_form.mojo`; the classic determinantal-divisor theorem is
explicitly attributed there to H. J. S. Smith (1861) and Newman,
*Integral Matrices* (1972). The generic M-adic documentation already
warns that quotient order `2^m` does **not** imply cyclicity; its
canonical example even has quotient `(Z/2)^2` at level two. The
specialized [#453](../kernel/psc/class_a_madic_digits.mojo) binary
transversal is a set of coset representatives, **not** an additive group
isomorphism. The new contribution below classifies precisely **when and
how** the abstract finite group differs across the entire Class-A
two-parameter family, using a standard 2-adic decomposition theorem.
Do not implement another Smith solver or claim novelty for Smith theory.

## Theorem: all Smith invariants for all k,t,m

Let k,t,m be arbitrary nonnegative integers and
`n=k+t+3`, `d=k+2t+5`, `A=n+d`. With alphabet
order `(x,c,y)` the minus Class-A incidence matrix is

```
M = [[2,1,1],
     [0,1,1],
     [A,n,n-1]],             det(M)=-2.
```

Let `G_m=Z^3/M^m Z^3` and list its three Smith invariant factors
`s_1 | s_2 | s_3`, retaining factors equal to one.

**Regime I: t even.** For every k,m,

```
(s_1,s_2,s_3)=(1,1,2^m).
```

Thus `G_m` **is cyclic**, although the chosen canonical binary digit
map of #453 is not claimed to be an additive homomorphism.

**Regime II: t odd and k even.** Write `m=3q+r`, `0<=r<3`:

```
r=0: (2^q, 2^q,     2^q)
r=1: (2^q, 2^q,     2^(q+1))
r=2: (2^q, 2^(q+1), 2^(q+1)).
```

In particular `G_3 ≅ (Z/2)^3`, rather than `Z/8`.
This is genuine three-way ramification at the finite prime 2.

**Regime III: t odd and k odd.** Write `m=2q+r`,
`0<=r<2`:

```
r=0: (1, 2^q, 2^q)
r=1: (1, 2^q, 2^(q+1)).
```

In particular `G_3 ≅ Z/2 × Z/4`, distinct from both
earlier regimes. For every case, the product of the three factors is
`|det M|^m=2^m`. Level zero is `(1,1,1)`.

These formulas require **no bound on m or the family parameters**.
The finite executable audit uses an explicit level cap separately.

## Proof

### A. Characteristic polynomial and a genuine local cyclic vector

A direct determinant expansion gives

```
f(X)=det(X I-M)=X^3-(n+2)X^2-(t+3)X+2.
```

Over `F_2` its form depends on the two parities:

```
t even:                  f ≡ X * g(X), g(0)=1 (mod 2);
t odd, k even:           f ≡ X^3 (mod 2);
t odd, k odd:            f ≡ X^2(X+1) (mod 2).
```

The matrix `M` is **cyclic as a 2-adic linear operator**.
An explicit integral vector `v` with odd Krylov determinant
`det[v,Mv,M²v]` is:

```
t odd:                       v=e_x;
t even, k even:              v=e_c;
t even, k odd:               v=e_c+e_y.
```

For the first two choices the exact determinants are
`-A²` and `2n-d=k+1` respectively, both odd in their
specified regimes. For the third, direct mod-two substitution into
the matrix above gives an odd determinant; `cyclic_krylov_mod2`
checks every named branch independently. The three Krylov
columns therefore constitute a basis over `Z_2`. The relation
`f(M)v=0` (Cayley–Hamilton) identifies

```
(Z_2)^3 ≅ Z_2[X]/(f),  with M acting as multiplication by X.
```

Since the determinant of `M^m` has no odd prime factor, its **integer**
Smith invariants are determined by this 2-adic module.

### B. Three separate local ring structures

For **t even**, the factor X occurs with multiplicity exactly one in
`f mod 2`. The remaining factor `g` has nonzero constant term.
Coprimeness gives a Hensel splitting of the local algebra into a
rank-one factor where X has 2-adic valuation one and a rank-two factor
where X is a unit. The constant term of f is exactly 2, so the
rank-one contribution to the quotient by `X^m` is `Z/2^m`;
the unit factor contributes nothing. This proves Regime I.

For **t odd, k even**, all lower coefficients of the monic cubic f
are even and its constant term is exactly 2. It is an
**Eisenstein polynomial at 2**. Its quotient ring is a rank-three
totally ramified `Z_2` extension, with X as uniformizer and
`X^3=2u` for some local unit u. Thus
`X^(3q+r)R=2^q X^r R`. The exact Smith factors of multiplication
by `X^r` for `r=0,1,2` are respectively
`(1,1,1)`, `(1,1,2)`, `(1,2,2)` (the last follows from
mod-two rank one and determinant four). Multiplying by
`2^q` scales all factors. This proves Regime II.

For **t odd, k odd**, `f mod 2=X²(X+1)` has two coprime
factors. Hensel splitting gives a rank-one algebra where X is a
unit and a rank-two factor whose monic polynomial reduces to X².
Because the rank-one factor has odd constant term and `f(0)=2`,
the quadratic factor has constant coefficient of **2-adic
valuation exactly one**; its linear coefficient is even. Hence
this quadratic is Eisenstein at 2. Its uniformizer X satisfies
`X²=2u` for a local unit u. At even power `2q`, multiplication
by X is equivalent to scalar multiplication by `2^q` on the
rank-two factor; at odd power `2q+1`, the factors are
`(2^q,2^(q+1))`. The rank-one unit factor contributes invariant
one. This proves Regime III. QED.

The use of local 2-adic/Hensel facts is a **classical imported
algebraic argument**; no claim of an independently Lean-checked
formalization of that argument is made.

## Exact kernel, independent oracle and negative controls

The new **canonical Mojo** module `kernel/psc/class_a_madic_smith.mojo`
implements the factor formula, explicit cyclic vectors, and calls the
**existing arbitrary-precision generic** `quotient_invariants` to
check complete Smith factors. It does not implement a second elimination
algorithm. The generic Smith calculation uses integer minors lifted into
exact rationals, and all comparisons are exact.

`kernel/tests/test_class_a_madic_smith.mojo` covers all sixteen
`(k,t)` with `0<=k,t<=3`, levels 0..5, explicit cyclic vector
determinants and all three regimes, plus refusal controls. The
separate `tests/test_class_a_madic_smith_oracle.py` calculates powers
by its own generic integer multiplication and computes gcds of
the nine 2x2 minors. It checks all 36 chambers
`0<=k,t<=5` through level eight, nontrivial split examples and
the genuine rank over `F_2`. This provides independent
**bounded** verification of the uniform written proof.

```sh
python -m pytest -q tests/test_class_a_madic_smith_oracle.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_madic_smith.mojo
```

Accepted negative control: `(k,t,m)=(0,1,3)` produces
`(2,2,2)`, not `(1,1,8)`, although both groups have order
eight and exactly eight binary digit words. At `(1,1,3)`,
the type is `(1,2,4)`, not either of those. The selected binary
coset representatives may be shared as a **set** while their addition
laws differ. A scalar `Z_2` group model would be unsound in the
noncyclic chambers.

## Precisely what remains open

No uniform existence of **actual legal substitution prefix paths**
is inferred from a quotient invariant. Nor does either a cyclic
quotient or its noncyclic alternative prove a boundary hit from
a seed-reachable strict-zipper overlap. The next #452 experiment
may stratify finite-place obstructions by the three parity regimes,
but must retain full oriented occurrence addresses and strict
Perron geometry. The correspondence between these arithmetic
quotients and the complete **realized** nonunit overlap system
also remains separately unproved.

Exact-head hosted CI, source-integrity tests and independent human
review remain distinct acceptance conditions. Keep the PR draft
and all global claim statuses unchanged until that evidence exists.

# C4 periodic ordered-lift experiment — 2026-11-04

**Status:** Executed independent exact Python exclusion of one specified six-state algebraic template, plus a native Mojo replay awaiting hosted execution. The conditional spectral argument below extends the existing three-state mean-area reduction; no governed claim or general C4/PSC status is promoted. This note is an experiment record, not an independent-review or Lean acceptance receipt.

Base: PR #486 at `6c8b0d267c410bdf2b246f3959824e2aef132ff0`, which is stacked on #484. Related target: issue #461.

## Why another matrix invariant is not enough

The all-positive template already admitted by the lattice tests is

```text
sigma=(01,121,012)
M = [[1,0,1],[1,2,1],[0,1,1]]
P = [M^2,M^2]
N = [[0,M],[M,0]].
```

It satisfies PN=MP, has period two, six states, rank three in each phase, phase-lattice indices (4,4), and transition indices (2,2). All Parikh coordinates are positive. This does not make its columns actual irreducible balanced-word pairs.

The new experiment exhausts every ordering of every child multiset prescribed by N. There are exactly `(2*3*6)^2=1296` possibilities. It excludes all of them using an order-sensitive equation and actual finite words, without assuming a selected ordering is the literal factorization.

## The word-order equation

For a word w, define a(w)=(N01-N10,N02-N20,N12-N21), counting scattered ordered two-letter subwords. Then

```text
a(uv)=a(u)+a(v)+p(u) wedge p(v),
a(sigma(w))=(wedge^2 M)a(w)+C_sigma p(w),
C_sigma[:,c]=a(sigma(c)).
```

For a balanced pair (u,v), the mean `J=(a(u)+a(v))/2` is integral: each coordinate of either area vector has parity p_i*p_j. Swapping the two tracks does not change J, so the argument covers normalized states and arbitrary child orientation signs.

For a proposed ordered child system tau, set `Omega[:,j]=sum_(r<s) p(tau(j)_r) wedge p(tau(j)_s)`. Any actual realization must satisfy

```text
(wedge^2 M)J - JN = Omega - C_sigma P.
```

This is the existing [three-state mean-area equation](c4-degree2-meanarea-integrality.md), now applied to a periodic equality-size candidate. Passing integrality does NOT prove word realizability.

## Why equality-size periodic candidates have a unique rational lift

For a supplied strict component with exactly 3h states, #484/#486 give invertible phase matrices P_k and return blocks B_k rationally similar to M^h. The block-cyclic determinant identity gives

```text
chi_N(t)=det(t^h I_3-B_k)=chi_(M^h)(t^h).
```

Let beta>1, alpha, gamma be the incidence eigenvalues, with |alpha|,|gamma|<1. If an eigenvalue lambda_i*lambda_j of wedge^2 M were also an eigenvalue of N, then `(lambda_i*lambda_j)^h=lambda_k^h`. If k is i or j, the remaining eigenvalue would have modulus one, impossible. If k is the remaining contracting conjugate, this would imply `|det M|=|lambda_k|^2<1`, impossible for a nonzero integer determinant. If k is beta, the product of the other two conjugates has modulus below one and cannot have modulus beta. Thus the spectra are disjoint.

Consequently `X -> (wedge^2 M)X-XN` is invertible over Q, and the ordered child words force one rational J. This proves uniqueness, not integrality or existence of a strict component. A useful exact determinant reduction is

```text
det(I_(3h) tensor A - N^T tensor I_3)
  = det(I_3 tensor A^h - (M^h)^T tensor I_3), A=wedge^2 M.
```

It follows by taking the product `prod_(mu in spec A) chi_N(mu)`. Independent integer replay checks this identity for h=1,2,3,4, with determinants -56, -596288, -628178432, -341820903424 for the displayed M.

The underlying disjoint-spectrum Sylvester criterion and scattered-subword calculus are established methods, not claimed as new here. See Nevanlinna, *Sylvester equations and polynomial separation of spectra* (2019), DOI 10.7153/oam-2019-13-62, and Mateescu–Salomaa–Yu, *Subword histories and Parikh matrices* (2004), DOI 10.1016/j.jcss.2003.04.001. The contribution here is the periodic equality-case specialization and the complete template exclusion.

## Exact exhaustive outcome

The 18-by-18 operator S has determinant **-596288**. The supplied integer matrix Q is independently verified on BOTH sides:

```text
S Q = Q S = 1694 I_18.
```

Therefore J is integral exactly when every coordinate of `Qb` is divisible by 1694. The Python oracle computes its inverse independently with Fractions; the native replay verifies the integer certificate before using it.

| Reduced common denominator of forced J | Number of ordered systems |
|---:|---:|
| 1 | 5 |
| 7 | 31 |
| 11 | 8 |
| 77 | 90 |
| 121 | 168 |
| 847 | 994 |
| **Total** | **1296** |

The **1291 nonintegral** cases cannot come from balanced words. In the remaining five, the first state has fixed mass (1,3,1), and its forced mean-area is one of

```text
(7,3,3), (3,1,1), (1,1,3), (-3,-1,1), (-3,-3,-1).
```

The first and fifth violate the elementary area magnitude bounds (3,1,3). The second forces both words to begin with 0, because the 01 and 02 areas are simultaneously maximal. The third forces both words to end with 2; the fourth forces both to end with 0. Each common endpoint contradicts noncoincident irreducibility: a common initial letter is an immediate balanced factor, and a common terminal letter gives a proper preceding balanced cut.

The executables also enumerate **all 20 words** of mass (1,3,1), examine all 400 ordered pairs per survivor, and find **zero** irreducible noncoincident pairs with the required mean-area. There is no cap-dependent inference here: 20 is the exact multinomial count.

Thus no choice of side words or normalized child orientations realizes this *particular* (sigma,P,N) packet as a strict irreducible balanced-pair system. The source substitution already has strong-coincidence witnesses in #479; this is not a new proof of general productivity. Its purpose is to make the algebraic-versus-literal gap mechanically testable.

## Reproduction and acceptance

```sh
python -m pytest -q tests/test_c4_periodic_order_lift_oracle.py
python tests/test_c4_periodic_order_lift_oracle.py
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_periodic_order_lift.mojo)
python tools/make_proof_bank.py --check
```

`evidence/c4-periodic-order-lift-2026-11-04/receipt.json` contains the exact matrix packet, inverse certificate, denominator census and five survivors. The receipt is data, not trusted proof: the Python oracle reconstructs it and the native verifier checks its inverse identity.

Local acceptance: six independent Python tests pass. The standard-library-only replay independently agrees with a separate SymPy exploratory calculation. Mojo/pixi are absent in this session, so native compilation and execution are **not claimed**. The full repository Proof Bank check and hosted exact-head workflows are still required. The focused workflow retains those checks. No changes to governed theorem statuses or claim dependencies are made.

Next useful step: apply the ordered-lift gate to additional *explicit* equality-size packets, retain every integral survivor, and then require literal complete child factorization. Do not infer that the finite template exclusion rules out every 3h-state component.

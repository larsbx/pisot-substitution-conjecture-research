# Literature gate: the fibre identification for strict-zipper periodic pairs — 2026-10-02

**Status:** stop/go literature gate for §5 of
`p1b-strict-zipper-periodic-pair-2026-10-02.md`. **Decision: proceed,
conditional on hypothesis (R)** (§6). Proposition F below, proved here, puts
the two tilings of Theorem B in one fibre of the maximal equicontinuous factor
whenever (R) holds. (R) is verified on the finite domains in §5 and is open in
general. Nothing here excludes a strict zipper or proves
PeriodicPairVertexCoincidence, AdelicPeriodicOffsetHitting, G1 or the Pisot
substitution conjecture.

## 1. Exact claim under review

For a primitive irreducible Pisot `sigma` on three letters, take interior
occurrences `sigma^r(i) = P i U` and `sigma^r(j) = Q j V` with
`w_0 = (M^r − I)^{−1}(pi(P) − pi(Q)) ∈ Z^3`. Let `T_A = T(i, P)` and
`T_B = T(j, Q) + <ell, w_0>`, the two `Phi^r`-fixed tilings with common centre
`c` (Theorem B). The claim is:

> (F) `g(T_A) = g(T_B)`, where `g: X_sigma → X_max` is the factor map onto
> the maximal equicontinuous factor of the translation action.

The note's §5 stated (F) as a reading resting on "the standard description of
`g` through Rauzy addresses". This gate replaces that reading with a proof
that uses only the eigenvalue criterion, and records the one hypothesis it
needs.

## 2. Sources inspected

| Source | Statement used | Read |
| --- | --- | --- |
| M. Barge, J. Kellendonk, *Proximality and pure point spectrum for tiling dynamical systems* (arXiv:1108.4065) | Thm 3.4 and Cor 3.5: for Meyer tilings, proximal means strongly proximal, and pairs in one fibre come in finitely many local configurations. Thm 5.1 (citing Solomyak): every eigenfunction of a substitution tiling space can be chosen continuous. Lemma 5.12: two tilings in one fibre that are not proximal share no tile. Thm 5.10 and Cor 5.11: the factor `X_max` is a solenoid of dimension equal to the degree, a torus in the unit case. | §§2.2, 3, 5 |
| M. Barge, *Factors of Pisot tiling spaces and the Coincidence Rank Conjecture* (arXiv:1301.7094) | Thm 4, collected from BK: (1) `g` is a.e. `cr`-to-one; (2) each fibre holds `cr` tilings sharing no tile under any `Phi^k`; (5) pure discrete spectrum iff `cr = 1`; (6) `g(T) = g(T')` iff `T` and `T'` are strongly regionally proximal. Proof of Thm 5: without pure discrete spectrum there are `Phi`-periodic `T` and `T'` with `g(T) = g(T')` and no common tile. | §§1–3 |
| M. Barge, J.-M. Gambaudo, *Geometric realization for substitution tilings* (arXiv:1111.6641) | §3: global shadowing, meaning lifts to an abelian cover of the Anderson–Putnam complex with deck group `GR(Phi)`, the generalized return vectors. Prop 24: global shadowing implies regional proximality. Prop 25 and Thm 4: they are equal when `D(Lambda) = D(GR)`. Thm 8: the realization is `g` in the `(m, d)`-Pisot-family case. **Unimodular only.** | §§2–4, 8 |
| M. Barge, *The Pisot conjecture for beta-substitutions* (arXiv:1505.04408) | Item (3) of §1, citing BKw, BBK, BK and Barge: `g(T) = g(T')` iff strong regional proximality, and pairwise strongly regionally proximal, pairwise tile-disjoint `T_1, …, T_r` exist iff `r <= cr`. Lemma 2: a configuration argument (after Barge–Diamond 2002) on `Psi`-fixed, pairwise tile-disjoint tilings in one fibre. | §§1–3 |
| J.-Y. Lee, B. Solomyak, *Pisot family self-affine tilings, discrete spectrum, and the Meyer property* (arXiv:1002.0039) | Proof of Prop 4.1, restating Solomyak (1997), Thm 3.13: `gamma` is an eigenvalue iff `e^{2 pi i <phi^n x, gamma>} → 1` for every return vector `x ∈ Ξ = {x : T + x ∈ T for some tile T}`. | §§2, 4 |

Not read directly, used only through the restatements above: Solomyak,
*Dynamics of self-similar tilings* (ETDS 17, 1997); Barge–Diamond, *Coincidence
for substitutions of Pisot type* (2002); Barge–Diamond, *Proximality in Pisot
tiling spaces* (2007); Barge–Kwapisz (2006); Barge–Bruin–Jones–Sadun. Pisot's
theorem on `||theta beta^n|| → 0` is classical (Cassels, *An introduction to
Diophantine approximation*, Ch. VIII).

## 3. What the literature gives and what it does not

- **No off-the-shelf statement covers (F).** Barge–Gambaudo's global
  shadowing is the right notion. It is stated for unimodular substitutions
  only, and its lifts live in the cover with deck group `GR(Phi)`. The overlap
  offset `w_0` lives in `Z⟨ell⟩ = Z^3`. When `GR(Phi)` is a proper
  finite-index subgroup, bounded lift discrepancy in `Z^3` does not give
  global shadowing.
- **Strong regional proximality** (Barge 2013 Thm 4(6); Barge 2015 (3)) needs,
  for each radius, two tilings containing the two patches that agree on a
  large ball somewhere. For a reachable overlap the patches descend from a
  swap seed `(ab)^Z` against `(ba)^Z`, which need not be legal, so this
  criterion cannot be checked directly.
- **The eigenvalue route works without unimodularity** (§4), at the price of
  hypothesis (R).

## 4. Proposition F (proved here)

*Hypothesis (R).* The **return module**
`Λ_ret = <pi(u) : a u a is legal, u ≠ empty>_Z` is all of `Z^3`.
Equivalently, the uncollared return vectors span `Z⟨ell⟩`.

*Proposition F.* Under (R), `g(T_A) = g(T_B)`.

*Proof.*

1. **The eigenvalue criterion on `Z^3`.** By (R), the return vectors `Ξ`
   generate `Z⟨ell⟩`. By Solomyak's criterion each eigenvalue `b` has
   `e^{2 pi i b beta^n x} → 1` for `x ∈ Ξ`, hence for the group they
   generate. So `||b beta^n <ell, z>|| → 0` for every `z ∈ Z^3`. Steps 3 and
   4 use this for all bounded prefix vectors, not only for `w_0`, which is
   why (R) is stated for the whole module.
2. **Exponential rate.** Fix `z` and put `theta = b <ell, z>`. By Pisot's
   theorem `theta ∈ Q(beta)`. Pick `D` with `D theta ∈ Z[beta]`. Then
   `Tr(D theta beta^n) ∈ Z`, so `||D theta beta^n|| <= C rho^n`, where
   `rho < 1` is the largest conjugate modulus. Hence
   `theta beta^n ≡ (m_n + eps_n)/D (mod 1)` with `m_n ∈ Z` and
   `|eps_n| <= C rho^n`. Since `||theta beta^n|| → 0`, eventually
   `m_n ≡ 0 (mod D)`, so `||theta beta^n|| <= C rho^n / D`.
3. **A continuous eigenfunction.**
   - For `T ∈ X_sigma`, let `y_n(T)` be the left endpoint of the level-`n`
     supertile containing `0`. The supertile is unique by recognizability:
     `sigma` is primitive and aperiodic, so `Phi` is a homeomorphism. If `0`
     lies on a supertile boundary, the two choices differ by
     `<ell, M^n e_a>`, which step 1 sends to zero, so the limit below is
     unchanged.
   - Consecutive differences are `y_n − y_{n+1} = <ell, M^n z_n>` with
     `z_n = pi(p_n)` the Parikh vector of a proper prefix, so `z_n` is
     bounded.
   - By step 2, `F_b(T) := lim_n e^{2 pi i b y_n(T)}` converges uniformly.
     It is continuous, and `F_b(T − t) = e^{−2 pi i b t} F_b(T)`, since
     `y_n(T − t) = y_n(T) − t` while `0` stays inside the same supertile.
   - So `F_b` is a continuous eigenfunction for `b`. By minimality it is the
     eigenfunction for `b`, up to a constant.
4. **Evaluating on the pair.** `T_A − c` and `T_B − c` are `Phi^r`-fixed
   about `0`. Their level-`rn` supertiles at `0` are the inflated tiles `i`
   and `j`, with left endpoints `−beta^{rn} c` and `beta^{rn}(<ell, w_0> − c)`.
   Hence
   `F_b(T_A − c) / F_b(T_B − c) = lim_n e^{−2 pi i b <ell, M^{rn} w_0>} = 1`
   by (R).
5. **Same fibre.** Every eigenfunction can be chosen continuous (BK Thm 5.1).
   For a minimal action, `X_max` is the dual of the group of continuous
   eigenvalues, and `g(T) = g(T')` iff every continuous eigenfunction agrees
   on `T` and `T'`. So `g(T_A − c) = g(T_B − c)`, and translating by `c`
   gives `g(T_A) = g(T_B)`.

`square`

Neither unimodularity nor reachability from a swap seed is used. Only the
integrality of `w_0` and (R) are.

## 5. Hypothesis (R): exploratory check, and its obstruction

**Exploratory check.** An uncommitted scratch oracle computed the index of
`Λ_ret` in `Z^3` from the gaps between consecutive equal letters in a long
`sigma^n(0)`, by integer row reduction. Index 1 is (R). Results:

- Tribonacci, the cube-image specimen and the determinant-two golden pump:
  index 1.
- 1,534 random primitive irreducible Pisot substitutions with images of
  length at most 3: all index 1.
- All primitive irreducible Pisot substitutions on three letters with total
  image length at most 8: the enumeration found exactly 24,486 specimens,
  matching the class of `lost-depth-indexed-formulation-2026-10-01.md` §6,
  and all have index 1.

This is evidence only. A Mojo port is required before (R) on any finite
domain is cited as a finite-domain theorem.

**Obstruction.** A character `chi: Z^3 → Q/Z` vanishes on `Λ_ret` iff there
is `h: A → Q/Z` with `chi(e_a) = h(c) − h(a)` for every legal two-letter word
`ac`. These are "height"-type cocycles. Then `chi ∘ M` has the same form,
with `h_M(a) = h(first letter of sigma(a))`. If such a `chi` exists, an
eigenvalue may detect `w_0` modulo `Λ_ret`, and the construction of step 3
needs modification. The ratio in step 4 is then a
root of unity, and (F) can fail by a torsion element of
`(M^r − I)^{−1} Z^3 / Z^3`. Whether `Λ_ret = Z^3` holds for every primitive
irreducible Pisot substitution was not settled by the sources read.

## 6. Consequences and decision

Under (R), Theorem B and Proposition F give the following chain:

1. A reachable strict zipper gives a `Phi^r`-periodic pair in one fibre with
   **no common vertex**, hence no common tile.
2. BK Lemma 5.12 (equivalently Barge 2015, item (3)) then gives `cr >= 2`,
   hence no pure discrete spectrum (Barge 2013 Thm 4(5)).

This is consistent with the known chain from pure discrete spectrum through
productivity to the absence of strict zippers, and adds nothing
unconditional. The table in §5 of the note now stands **under (R)**:

| Periodic pair in one fibre | Equivalent to |
| --- | --- |
| no common tile | `cr >= 2` (known) |
| no common vertex | a strict zipper (Theorem B with Proposition F) |

**Decision: proceed, conditional on (R).**

1. Record Proposition F in the note as proved under (R), with the sources
   above. Do not cite (F) without (R).
2. Promote no ledger node. PeriodicPairVertexCoincidence stays open.
3. **Stop list.** None of the following may be offered as closing #139:
   - `cr = 1`-type statements, since they are pure discrete spectrum itself;
   - density or counting, since a hypothetical `cr = 2` substitution with
     measure-disjoint subtiles has vertex-disjoint generic pairs;
   - Barge–Gambaudo global shadowing without a proof that `GR(Phi) = Z⟨ell⟩`.
4. **Candidate route, not verified.** Barge 2015, Lemma 2, runs the
   Barge–Diamond 2002 configuration argument on `Psi`-fixed, pairwise
   tile-disjoint tilings in one fibre: union vertex set, local
   configurations, a pumping step, and a contradiction with `cr`. Our pair
   is a two-element instance with the stronger property of vertex
   disjointness. Whether that argument, which in Barge 2015 depends on the
   monotone structure of beta-substitutions, can yield a common vertex in
   general needs a reading of Barge–Diamond 2002 in full. That reading is
   the next gate.

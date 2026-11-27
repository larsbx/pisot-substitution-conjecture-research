# GRH, effective Chebotarev and auxiliary primes: stop/go before any implementation

**Decision (2026-11-22): stop.** No open obligation of the programme is of a
form that a bound on the least prime with a prescribed splitting type could
discharge, so the Generalized Riemann Hypothesis (GRH) has no entry point.
No diagnostic, census, Lean development or oracle is written. The reopening
criterion is in the last section.

This note changes no claim status. It was written at `main@f5ba148`.

## 1. Proposed claim and scope

Let `σ` be a PIP substitution on `d` letters with incidence matrix `M`,
irreducible `χ_M`, Perron root `β`, `K = ℚ(β)`, Galois closure `L` and
`G = Gal(L/ℚ) ≤ S_d`. For a rational prime `ℓ ∤ det M · disc χ_M` the
factorization type of `χ_M mod ℓ` is the cycle type of the Frobenius class
of `ℓ` in `G`. Call such an `ℓ` an *auxiliary prime*, as opposed to a
*structural prime* `p | det M`.

The proposed route was:

> **(Q)** Some open obligation `O(σ)` follows, uniformly in `σ`, from the
> existence of an auxiliary prime `ℓ` of prescribed splitting type together
> with an explicit upper bound `ℓ ≤ B(σ)`. GRH would supply
> `B(σ) = O((log D_L)²)` where only a power of `D_L` is known
> unconditionally.

The question decided here is whether any open obligation has the shape (Q).
The standing target is ternary PIP with nonunits allowed, so `d = 3`,
`G ∈ {S₃, C₃}` and `[L:ℚ] ∈ {6, 3}`.

## 2. Primary sources checked

1. Thorner and Zaman, *An explicit bound for the least prime ideal in the
   Chebotarev density theorem*, Algebra Number Theory 11 (2017), 1135–1197,
   [arXiv:1604.01750](https://arxiv.org/abs/1604.01750). Read: introduction
   and Theorem 1.1. With `P(C, L/F)` the least norm of an unramified prime
   with Artin symbol `C`, Theorem 1.1 gives unconditionally
   `P(C, L/F) ≪ D_K^694 Q^521 + D_K^232 Q^367 [K:ℚ]^{290[K:ℚ]}` for `K` the
   fixed field of an abelian subgroup meeting `C`. The introduction records
   the Lagarias–Montgomery–Odlyzko bound (a fixed power of `D_L`), Zaman's
   explicit `P(C, L/F) ≪ D_L^40` as (1.5), and the GRH bound (1.4) below.
2. Bach and Sorenson, *Explicit bounds for primes in residue classes*,
   Math. Comp. 65 (1996), 1717–1735,
   [DOI](https://doi.org/10.1090/S0025-5718-96-00763-6). **Not read in the
   original** (the publisher page refused the fetch). The bound is taken from
   its quotation as equation (1.4) of source 1: under GRH,
   `P(C, L/F) ≤ (4 log D_L + 2.5 [L:ℚ] + 5)²`.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   Ann. Inst. Fourier 64 (2014), [arXiv:1402.2002](https://arxiv.org/pdf/1402.2002).
   Read: Section 3. The representation space is
   `K_σ = ∏_{𝔭 ∈ S_α ∖ {𝔭₁}} K_𝔭` with `S_α = {𝔭 : 𝔭 | ∞ or 𝔭 | (α)}`, and
   "in case the substitution σ is unit the representation space will consist
   only of Archimedean completions". No place outside `S_α` occurs. A text
   search of the paper finds no use of Chebotarev, L-functions or a Riemann
   hypothesis.
4. Baker, Barge and Kwapisz, *Geometric realization and coincidence for
   reducible non-unimodular Pisot tiling spaces with an application to
   β-shifts*, Ann. Inst. Fourier 56 (2006), 2213–2248,
   [published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf).
   Read: Section 3 and Definition 4.1 / Theorem 4.2. The realization target
   is `T_A = lim←(A : V/Σ → V/Σ)` for an intrinsic lattice `Σ`; `h_φ` is
   uniformly finite-to-one and almost everywhere `cr_φ`-to-one. The same
   text search finds no analytic number theory.
5. In-repository: `kernel/psc/overlap_madic_filter.mojo`,
   `kernel/psc/finite_cokernel_address.mojo`, `kernel/psc/degree2_sieve.mojo`,
   the open records of `tools/make_ledger.py`, and the M-adic entries of the
   [side-notes ledger](side-notes-ledger.md) (2026-10-04, 2026-10-05). The
   repository contained no mention of GRH, Chebotarev or Artin's conjecture
   before this note.

Siegel's 2003 non-unimodular construction is cited by source 3 as the origin
of `K_σ`; it was not read.

## 3. Derivation

**(D1) GRH changes a bound, never an existence statement.** Chebotarev's
theorem already gives, unconditionally, infinitely many auxiliary primes of
every cycle type occurring in `G`. Sources 1 and 2 concern only the size of
the least one. Therefore an implication
`(∃ℓ of type τ) ⟹ O(σ)` needs no hypothesis, and for a fixed `σ` the least
such `ℓ` is found by a terminating exact search (factor `χ_M mod ℓ` for
`ℓ = 2, 3, 5, …`). GRH is relevant only to an argument that *consumes the
inequality* `ℓ ≤ B(σ)` with `B` polylogarithmic in `D_L`. That is the
shape (Q), and it is the only one to look for.

**(D2) The maximal equicontinuous factor has no auxiliary-prime part.**

*Lemma.* Let `M ∈ M_d(ℤ)` with `det M ≠ 0` and
`Λ = ⋃_{n≥0} M^{-n} ℤ^d ⊂ ℚ^d`. Then `ℤ^d ⊆ Λ ⊆ ℤ[1/det M]^d`, and
`#(ℤ^d / M^n ℤ^d) = |det M|^n`.

*Proof.* `M⁻¹ = adj(M)/det M` with `adj(M)` integral, so
`M^{-n} ℤ^d ⊆ (det M)^{-n} ℤ^d`. The index is the absolute determinant of
`M^n`. ∎

`Λ` (with `Mᵀ` in place of `M`) is the Pontryagin dual of
`lim←(ℝ^d/ℤ^d, M)`. For another full-rank `M`-invariant lattice `Σ`, as in
source 4, the matrix of `M` on `Σ` is integral with the same determinant,
so the lemma applies unchanged. Consequently, for `ℓ ∤ det M`,
`Λ ⊗ ℤ_(ℓ) = ℤ_(ℓ)^d`: the solenoid's profinite fibre
`lim← ℤ^d/M^n ℤ^d` is supported on the structural primes only, and is
trivial when `σ` is unimodular. This agrees with `S_α` in source 3. Pure
discrete spectrum is almost-everywhere injectivity of `h_φ` onto this group
(source 4, Theorem 4.2 with `cr_φ = 1`), so the object PSC is about does not
see an auxiliary prime at all. The structural primes are determined by `σ`;
there is nothing to choose and hence no least-prime problem.

**(D3) Reduction modulo an auxiliary prime can refute, not produce.**
Reduction `ℤ^d → 𝔽_ℓ^d` is a homomorphism commuting with `M`, so it carries
solutions of an integral equation to solutions. For the boundary-hitting
equation `M^m w = p − q` it yields the necessary condition
`M^m w ≡ p − q (mod ℓ)`, where `m ↦ M^m w mod ℓ` is periodic with period
dividing the order of `β` in `(𝒪_K/ℓ)^×`. This is the one place a splitting
type could matter, since it controls that order. It is a sieve on `m`: it
can exclude hits and can never certify one. The lattice form of the
condition, `p − q ∈ M^m ℤ^d`, is vacuous at `ℓ` by the Lemma, which is the
statement in `overlap_madic_filter.mojo` that the filter "correctly becomes
trivial" in the unimodular case.

**(D4) The open obligations, one by one.** The thirteen records with status
`open` in `claim_governance.toml`, with statements from
`tools/make_ledger.py`:

| Open record | Logical form | Shape (Q)? |
| --- | --- | --- |
| `UniversalBoundaryHitting` | ∀ cyclic vertex ∃ occurrence-compatible offset-zero descendant | No. Existence of a hit; (D3) gives exclusions only |
| `UniversalAlignedCoincidence` | ∀ letter pair ∃ eventual prefix coincidence | No. Existence, same direction mismatch |
| `OverlapProductivity`, `AllSeedOverlapProductivity`, `FormalProductivity` | ∀ reachable overlap ∃ productive descendant | No. Existence |
| `AllSeedStrictZipperExclusion` | no reachable closed nonproductive strict-zipper set | No mechanism identified; see below |
| `ConcentrationAuxB`, `SpanRichProductivity` | no strict component with `K2 = 0` / `K2 ≠ 0` | No mechanism identified; see below |
| `G1b2RenewalFiniteness` | finitely many realizable irreducible balanced pairs in the discrepancy box | No. Its arithmetic refinement is the cokernel `ℤ³/M^k ℤ³` of order `|det M|^k`: structural primes only |
| `G1`, `SCCProducer`, `SpectralSCCProducer`, `PSC` | assemblies of the above | Inherit the answer |

The three nonexistence records are the only ones whose direction a sieve
could serve. The existing exclusions of that kind use congruences that are
forced by the structure: `degree2_sieve.mojo` works modulo 2 and 4 because
`N_C = A + B` and `S_C = A − B` differ by `2B`, and the cokernel filters
work at `p | det M`. An auxiliary `ℓ` has no such source of congruences: the
intertwiner relations of a strict component hold over `ℤ`, so their
reductions modulo `ℓ` hold too and exclude nothing by themselves. I found
no argument in the repository or in sources 3–4 in which a strict component
is constrained modulo a prime chosen by splitting type. This is an absence
of a mechanism, not a proof that none exists.

The Galois-theoretic steps already in the programme
(`GaloisWedgePropagation`, the `(2,2,0)` exclusion at `r(C) = 4`) argue with
conjugate roots over `ℚ`. In degree three the Galois group is decided by
whether `disc χ_M` is a square, an exact integer test, so no Frobenius
certificate is needed there either.

**Conclusion.** No open obligation has shape (Q). Every use of a finite
place in the programme and in the cited literature is at a structural
prime, which is given and not searched for.

## 4. Hypotheses that transfer and those that do not

- Transfer: sources 3 and 4 allow nonunits and so match the standing PIP
  regime. Source 4 also allows reducibility, which is not used.
- Do not transfer: sources 1 and 2 are statements about number fields with
  no dynamical content; nothing in them refers to a substitution.
- Size of the effect, were it ever needed: for the corpus the entries of `M`
  are bounded, so `D_L` is bounded and any required prime is found by
  exhaustive exact search. Asymptotic bounds matter only for a statement
  uniform over an unbounded family.

## 5. Negative controls

All three are checkable by hand; none is a new executable.

1. **Unimodular, vacuous sieve.** Tribonacci `0→01, 1→02, 2→0` has
   `χ_M = x³ − x² − x − 1`, `det M = 1`. By the Lemma `M^m ℤ³ = ℤ³` for all
   `m`, so every lattice-residue filter is empty at every prime.
2. **Nonunit, structural prime only.** `σ = (01, 121, 012)` is the
   `a = b = 1` member of the two-parameter family of the 2026-11-04 ledger
   entry, with Parikh columns `(1,1,0), (0,2,1), (1,1,1)` and
   `det M = 1·(2−1) + 1·(1−0) = 2`. The cokernel `ℤ³/M^m ℤ³` has order `2^m`;
   `M` is invertible modulo every odd `ℓ`, so the cokernel carries no odd
   information.
3. **The GRH bound is slack where a prime is wanted.** For Tribonacci,
   `disc χ_M = −44` is not a square, so `G = S₃` and `[L:ℚ] = 6`. Modulo 2,
   `χ_M ≡ (x+1)³` (ramified, `2 | 44`). Modulo 3, `χ_M` takes the values
   `2, 1, 1` at `0, 1, 2`, so it is irreducible and 3 is the least inert
   prime. The bound of source 2 is at least `(2.5·6 + 5)² = 400` for every
   sextic `L`. Exhaustive search wins by two orders of magnitude before the
   discriminant term is counted.

## 6. Decision and reopening criterion

**Stop.** Reopen only if an obligation is exhibited in which a bound
`ℓ ≤ B(σ)` on an auxiliary prime is consumed by the argument, with `B`
required to be smaller than a power of `D_L`. Two places where that could
conceivably arise, neither on the standing target:

- a `d`-uniform (all-alphabet) version of a Galois-span hypothesis, where
  certifying that `G` contains a given cycle type by exhibiting a Frobenius
  element replaces the discriminant test available at `d = 3`;
- a complexity statement about certificate size, which would be a statement
  about the algorithm and not about PSC.

## 7. Non-claims

- This note does not show that GRH and PSC are logically independent, and
  does not show that no arithmetic route to PSC exists.
- It does not assert that congruences modulo auxiliary primes are useless
  as diagnostics; (D3) says only that they are one-sided and that no open
  obligation is of the form they could settle.
- The Bach–Sorenson constant is quoted second-hand (source 2).
- A result obtained through (Q) would be GRH-conditional. Under the
  promotion rule of `AGENTS.md` ("a certificate check cannot decide: refuse
  to promote") it would carry GRH as an explicit hypothesis.

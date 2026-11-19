# Geometric realization on the legal hull: source decision

**Status:** Source decision for the realization obligation left open by the
[legal tiling hull instance](c4-tiling-hull-realization-2026-11-19.md) (its non-claim 1):
construct the geometric-realization map on the Lean hull, with the Pisot contraction,
recognizability and a solenoid target in the nonunit case. Starting revision:
`main@e79e3e3`. No governed claim changes.

## Exact target

On `PeriodicPartnerHull.Hull` for any `LengthSubst α` over a finite alphabet, construct

- the substitution matrix `M` (`M b a` = number of `b` in `σ a`), the torus `ℝᵈ/ℤᵈ` and the
  endomorphism `M` induces on it;
- the solenoid `{(zₙ) : M zₙ₊₁ = zₙ}` with the shift `Â(zₙ) = (M zₙ)`;
- a map `h : Hull → Solenoid` with `h ∘ inflate = Â ∘ h`, translation carried to a flow along
  `u`, and (R4) at `q₀ = 0`;

and replace the fields `realize`, `A`, `semiconj`, `q₀`, `q₀_fixed`, `r4` of
`PublishedInputs` by these constructions. Finite fibres stay an input.

## Sources

| Source | Input and boundary |
| --- | --- |
| Baker–Barge–Kwapisz, [Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Ann. Inst. Fourier 56 (2006), §§2–4 (re-read 2026-11-19 from the Numdam PDF) | §2, Prop. 2.3: the strand space is the inverse limit `(γₖ)` with `γₖ₊₁ = Φ(γₖ)`; injectivity of the projection "hinges on the fact that Φ induces a homeomorphism", "a consequence of Mossé's recognizability result". §3: the target is `T_A`, the inverse limit of `A` on `V/Σ` ("the obvious candidate is the inverse limit of the endomorphism induced by A on the torus V/Γ"); Definition 3.1, `p_k := min I − u_i` with `u_i` normalised by `τ = Au_i − u_{i'} = 0`; (3.10) `h∘Φ = A∘h` with `A` the shift on `T_A`; (3.12) the flow `(p_k + λ^k tω)`. Theorem 4.2: `h_φ` is uniformly finite-to-one and a.e. `cr_φ`-to-one. |
| Same, §3, after (3.4) | "If A is irreducible Pisot (i.e. W = {0}) then Σ = Γ". In the irreducible case the lattice is `ℤᵈ` and the offsets `u_i` vanish modulo `Σ`. This is the case realised here. |
| Mossé (1992), TCS 99; Solomyak (1998), DCG 20 | Recognizability (inflation injective on the hull of an aperiodic primitive substitution). Bibliographic citation only, **not re-opened**; it stays an input. |
| Barge–Diamond, [Cohomology in one-dimensional substitution tiling spaces](https://arxiv.org/pdf/math/0702669), §2 | Inflation is a homeomorphism of the hull for primitive aperiodic substitutions (surjectivity included). Not re-opened in this session; used for the surjective half of the bijectivity input. |

## Hypotheses that transfer, and those that do not

- **Transfer.** The definition is the BBK one specialised to `Γ = Σ = ℤᵈ` and to tilings of
  `ℝ` rather than strands in `V`: the strand vertex of the origin tile at level `n` is
  `−βⁿxₙ u` modulo `ℤᵈ` plus stable corrections, and the series
  `G(T) = −x₀u − Σₖ Mᵏ π(cₖ)` is the strand position. Semiconjugacy, equivariance and the
  shift's invertibility are algebraic consequences, to be proved.
- **Pisot contraction.** BBK use an adapted stable norm on `Eˢ`. Only the estimate
  `‖Mⁿ v‖ ≤ C ρⁿ ‖v‖` on `ker ℓ` (with `ρ < 1`) is used; it is stated as a field of a
  `PisotData` structure, together with the eigenvector `u`, `ℓ ⬝ u = 1`. For an irreducible
  Pisot matrix it is a consequence of the spectral hypothesis; the derivation from the
  characteristic polynomial is **not** attempted. Instances are checked for Fibonacci and
  Thue–Morse.
- **Recognizability.** Used as bijectivity of `inflateH` on this hull (injectivity: Mossé,
  Solomyak; surjectivity: Barge–Diamond §2). Imported.
- **Reducible case.** BBK's `V`, `W` splitting and the intrinsic lattice `Σ ≠ Γ` (their
  Example 3.2) do not transfer: when `ker ℓ` contains a non-contracted direction there is no
  `PisotData`, and this construction does not apply. A control records this.
- **Finite fibres (BBK Theorem 4.2).** The coincidence-rank argument is not attempted. The
  correspondence of the Lean map with `h_φ` is the written identification above; it is not
  machine-checked, so Theorem 4.2 remains an input stated directly for the constructed map.

## Controls

- Nonunit: Thue–Morse (`det M = 0`) satisfies the contraction with `ρ = 0`; its torus
  endomorphism is not injective, so a torus-valued semiconjugacy cannot target an invertible
  map. The solenoid shift is bijective in every case.
- Unit: Fibonacci (`det M = −1`) satisfies the contraction with `ρ = |ψ|`, and the solenoid's
  first coordinate is injective.
- Failure: `0 ↦ 011, 1 ↦ 100` has second eigenvalue `−1` on `ker ℓ`; no `PisotData` exists.

## Decision

**Proceed** with the torus map, the solenoid, semiconjugacy, flow equivariance and (R4) for
the constructed map, under `PisotData` and bijective inflation. **Do not** attempt the
finite-fibre theorem or the derivation of the contraction from the characteristic polynomial.

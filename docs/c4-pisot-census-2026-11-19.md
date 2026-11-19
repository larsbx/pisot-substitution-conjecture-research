# The census in Lean: 4,554 PIP3 members, each with the derived contraction

**Status:** Lean decides, for each of the `39³ = 59 319` substitutions on `{0, 1, 2}` with
images of length one to three, whether it underlies a PIP3 `LengthSubst (Fin 3)`. Exactly
`4 554` do, the census count, and each carries `PisotData` through the derivation of the
[contraction note](c4-pisot-contraction-2026-11-19.md). This closes that note's non-claim 1 for the
census class. Recognizability, BDS and finite fibres remain inputs. Independent human review is
pending. C4 and PSC remain open; no governed claim changes.

Starting revision: `main@c0231e0`.
[Source decision](c4-pisot-census-stop-go-2026-11-19.md).

## Work shown

### Assumptions and hypotheses

| Input | Formal role | Status |
| --- | --- | --- |
| `SpectralPisot.toPisotData`, `SpectralPisot.ofIrreducible` | the contraction from a factorization of `χ_M`; the factorization from PIP3 | proved in the previous round, used unchanged |
| `PIP3 S` | nonerasing; `∃ n, Mⁿ > 0`; `χ_M` the image of an irreducible `p ∈ ℚ[X]`; `1 < β`; `χ_M(β) = 0`; every other complex root of modulus `< 1` | definition (`PeriodicPartnerSpectralCertificate.PIP3`) |
| the specimen class | `σ : Fin 3 → List (Fin 3)`, every image of length `1..3` | hypothesis of `census` |

No Lean axiom is added. `decide +kernel` evaluates in the kernel; `native_decide` is not used.

### Derivation / reduction

Write `M` for the incidence matrix of `s`, `p = χ_M = X³ − T X² + U X − D`.

1. **The certificate** (`check`). Integer data only: images nonempty; `p(1) < 0`, `p(−1) < 0`;
   `D ≠ 0` and no integer root `r`, `|r| ≤ |D|`; `M⁵ > 0`; a bracket `lo/16 < β < hi/16` from
   integer bisection of `16³ p(x/16)`, re-checked at both ends, with `lo/16 ≥ max(1, |D|)`; and for
   each column `j` a positive lower bound of `c₁ⱼ β² + (c₂ⱼ − T c₁ⱼ) β + D` on the bracket
   (`c₁, c₂` the column sums of `M`, `M²`).
2. **The root** (`exists_root`, `beta`). Intermediate value theorem on the bracket; so `β > 1`
   and `β > |D|`.
3. **The cofactor** (`pR_factor`, `charpoly_factor`). For any root `β ≠ 0`,
   `χ_M = (X − β) Q` with `Q = X² + (β − T)X + D/β`.
4. **Jury** (`jury`, `norm_lt_one_of_quadratic`). `p(1) = (1 − β) Q(1)` and
   `p(−1) = (−1 − β) Q(−1)` give `Q(±1) > 0`; `|Q(0)| = |D|/β < 1`. A monic real quadratic with
   these three properties has its complex roots in the open unit disc: real roots
   `x, y = −a − x` satisfy `Q(1) = (1 − x)(1 − y)`, `Q(−1) = (1 + x)(1 + y)`, `Q(0) = xy`; a
   conjugate pair has `|μ|² = Q(0)`. `Q(β) ≠ 0` because `β > 1`.
5. **The eigenvector** (`ell`, `ell_vecMul`, `beta_mul_ell`, `ell_pos`). `ℓ = 𝟙ᵀ Q(M)` satisfies
   `ℓ M = β ℓ` by Cayley–Hamilton (`Q · X = χ_M + β Q`), and `β ℓⱼ = c₁ⱼ β² + (c₂ⱼ − T c₁ⱼ) β + D`,
   positive by step 1. This replaces Perron–Frobenius by a per-specimen check.
6. **Soundness** (`subst`, `spectral`, `pisotData`, `mem_PIP3`, `sound`). `check s = true` gives
   `S : LengthSubst (Fin 3)` with `S.σ = s.σ`, `PIP3 S` (with `n = 5`, `p = X³ − TX² + UX − D`
   over `ℚ`, irreducible by the rational root theorem) and `PisotData S`.
7. **Rejection** (`refute`, `refute_spec`). If `s` underlies any PIP3 `S`, whatever its `ℓ` and
   `β`: `p = pQ s` (injectivity of `ℚ → ℝ` on polynomials), `ofIrreducible` gives a cofactor
   with roots in the disc, which is `X² + (β − T)X + D/β` by cancellation, so Jury's conditions
   hold (`jury_of_norm_lt_one`, the converse of step 4). Hence `p(±1) < 0`; no integer root (an
   irreducible cubic has none); and for `|D| ≥ 2`, `|D| < β` and
   `p(|D|) = (|D| − β) Q(|D|) < 0` with `Q > 0` on `[1, ∞)`. So `refute s = false`.
8. **Enumeration** (`words`, `specimens`, `mem_specimens`). The 39 words in census order; every
   substitution with image lengths in `[1, 3]` is a specimen.
9. **Kernel evaluation** (`row_*`, `corpus_length`, `decided_*`, `decided_of_mem`). For each of
   the 39 first images, the kernel counts the accepted specimens of the row (the counts sum to
   `4 554`) and checks `refute s || check s` on every specimen of the row.
10. **The census** (`census`). For `σ` in the class: `(∃ S, S.σ = σ ∧ PIP3 S)` iff
    `(σ 0, σ 1, σ 2) ∈ corpus`, and every member of `corpus` carries `PisotData`.

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`PeriodicPartnerSpectralCertificate.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSpectralCertificate.lean) | `check`, `refute`, integer lemmas, the bracketed root, the cofactor at any root, Jury's test in both directions, `ℓ = 𝟙ᵀ Q(M)`, `subst`, `spectral`, `pisotData`, `mem_PIP3`, `sound`, `refute_spec`; controls `check_tribonacci`, `check_reducible`. |
| [`PeriodicPartnerSpectralCensus.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSpectralCensus.lean) | `words`, `specimens`, 39 row counts, 39 row decisions, `corpus_length`, `corpus_sound`, `mem_corpus_of_PIP3`, `census`, `tribonacci_mem_corpus`. |

```sh
(cd proof/PscVerif && lake build PscVerif.PeriodicPartnerSpectralCertificate PscVerif.PeriodicPartnerSpectralCensus)
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

Both modules are in the periodic-partner audit closure (`PeriodicPartnerAudit.lean`), which
checks every compiled declaration for the standard axioms only. Session receipts (Lean
`v4.34.0-rc2`, 4 cores, 16 GB):

- `lake build PscVerif.PeriodicPartnerSpectralCensus`: 533 s, peak resident memory 4.45 GB.
- `./tools/check_c4_periodic_partner.sh` after merging `main@0179693` (fresh closure, source
  snapshot `ba0654e7…1dbd` over 226 files): `PSC_PERIODIC_PARTNER_AUDIT_VERIFIED 20 1371 1005 533`,
  `PSC_PERIODIC_PARTNER_GATE_COMPLETE fresh-local-closure standard-axioms-only`.
- `#print axioms census`: `[propext, Classical.choice, Quot.sound]`; `corpus_length`:
  `[propext]`.

The Lean `corpus`, printed with `#eval` and letters shifted by one, equals `pip_corpus()` as a
list (same 4,554 members, same order); this is a session replay, not a committed test, and the
`census` theorem does not depend on it. Receipts come from incremental and isolated session builds; the hosted CI receipt is separate.

### Negative controls

- `check_reducible`: `0 ↦ 011, 1 ↦ 100, 2 ↦ 2` (`χ_M = (X − 1)(X − 3)(X + 1)`) is rejected.
- `doubled_not_pisot` (root `−1` on `ker ℓ`) still shows that the root condition cannot be dropped
  from the contraction.
- Bracket width `1` fails the positivity bound on 36 members (prototype); the committed width
  `1/16` has margin.
- A single kernel evaluation of all specimens exceeded 13 GB and was killed; the row split is a
  resource necessity, not a choice of presentation.

### Non-claims / remaining gaps

1. **Only the census class.** Three letters, images of length at most three. The certificate
   `check` is sound for every `Sub3`, but its completeness is established only by the kernel
   evaluation on the 59,319 specimens, not as a general theorem.
2. **Recognizability, BDS and finite fibres** remain inputs for every census member as for
   Tribonacci; `pisotData` does not by itself produce `publishedInputs`.
3. **The Mojo census is not refined into Lean.** Agreement with `kernel/psc/pisot.mojo` is the
   count `4 554` and the session list comparison above; Lean's `PIP3` and the census's Sturm
   screen are different definitions that select the same specimens.
4. Non-claims 2–3 of the [contraction note](c4-pisot-contraction-2026-11-19.md) and 1, 3–6 of
   the [realization note](c4-geometric-realization-2026-11-19.md) are unchanged.

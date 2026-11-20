# Geometric realization on the legal tiling hull

**Status:** Lean now constructs the geometric-realization map of the
[legal tiling hull](c4-tiling-hull-realization-2026-11-19.md) into the solenoid of the
substitution matrix. It proves the semiconjugacy with inflation, the bijectivity of the solenoid
shift (also when `|det M| ≠ 1`), translation equivariance, and (R4) at `q₀ = 0`. Of the
`PublishedInputs` fields, `realize`, `A`, `semiconj`, `q₀`, `q₀_fixed` and `r4` are now
constructed (`publishedInputs`). Recognizability, BDS periodicization and finite fibres remain
inputs, and the Pisot contraction is a hypothesis (`PisotData`). Independent human review is
pending. C4 and PSC remain open; no governed claim changes.

Starting revision: `main@e79e3e3`. The [topology follow-up](c4-geometric-realization-topology-2026-11-19.md)
proves compact Hausdorff topology, a shift homeomorphism and continuous target flow, and
checks on actual Thue–Morse tilings that depth zero loses information.
[Source decision](c4-geometric-realization-stop-go-2026-11-19.md).

## Work shown

### Assumptions and hypotheses

| Input | Formal role | Status |
| --- | --- | --- |
| `LengthSubst α`, `[Fintype α]` | Substitution with nonempty images and a positive length eigenvector `ℓ`: `ℓ M = β ℓ`. | as in the hull |
| `PisotData S` | `u` with `M u = β u` and `ℓ ⬝ u = 1`; `C ≥ 0`, `0 ≤ ρ < 1`; `‖Mⁿ v‖ ≤ C ρⁿ ‖v‖` whenever `ℓ ⬝ v = 0`. | hypothesis; checked for Fibonacci and Thue–Morse |
| `hR : Bijective inflateH` | Recognizability: every hull element has a unique desubstitution. | published input (Mossé, Solomyak; surjectivity Barge–Diamond) |
| `1 < β` | Only for translation equivariance. | hypothesis |
| BDS, finite fibres | Passed unchanged into `publishedInputs`. | published inputs |

Every input is a theorem argument or structure field. No Lean axiom is added.

### Derivation / reduction

Write `Tₙ` for the `n`-th desubstitution (`inflate Tₙ₊₁ = Tₙ`) and `xₙ` for the left
endpoint of the tile of `Tₙ` containing `0`.

1. **Level recursion** (`offset_eq`, `xs_succ`). The origin tile of `inflate U` is a tile of
   the placed image of `U`'s origin tile (`tileAt_inflate`), after a prefix `p` of that image
   (`place_prefix`). Hence `xₙ = β xₙ₊₁ + ℓ ⬝ cₙ` with `cₙ = ab(p) ∈ ℤᵈ`, drawn from the finite
   set of prefix counts, so `‖π cₙ‖ ≤ offsetBound` where `π v = v − (ℓ ⬝ v) u`.
2. **The series** (`summable`, `vec`). `ℓ ⬝ π v = 0`, so `‖Mᵏ π cₖ‖ ≤ C · offsetBound · ρᵏ`
   and `G(T) = −x₀ u − Σₖ Mᵏ π cₖ` converges absolutely.
3. **The key congruence** (`partial_sub_mem`). From `Mⁿ c − Mⁿ π c = βⁿ (ℓ ⬝ c) u` and the
   recursion, by induction,
   `−x₀u − Σ_{k<n} Mᵏ π cₖ ≡ −βⁿ xₙ u (mod ℤᵈ)`.
   The torus point `[G(T)]` is the limit of `[−βⁿ xₙ u]`, the BBK strand vertex.
4. **Inflation** (`vec_shift`, `torusRealize_inflate`). The desubstitutions of `inflate T` are
   `inflate T, T₀, T₁, …`, so its counts are `c'₀, c₀, c₁, …` with
   `x'₀ = β x₀ + ℓ ⬝ c'₀`. Passing to the limit in a finite identity between partial sums gives
   `G(inflate T) = M G(T) − c'₀`, so `[G(inflate T)] = M [G(T)]`.
5. **Translation** (`vec_sub_mem_of_eventually`, `torusRealize_translate`). The desubstitutions
   of `T − t` are `Tₙ − t/βⁿ` (`level_translate`, from injectivity of inflation). Once
   `|t/βⁿ| < min ℓ`, the tile of `Tₙ` at `t/βⁿ` is the origin tile or one of its neighbours
   (`tileAt_near`, using `tileAt_next` and `exists_prev`), so its start is `xₙ + ℓ ⬝ dₙ` with
   `dₙ ∈ {0, eₐ, −e_b}`. Then
   `βⁿ x'ₙ = βⁿ xₙ + βⁿ (ℓ ⬝ dₙ) − t`, and the partial-sum differences minus `t u` minus
   `Mⁿ π dₙ` lie in `ℤᵈ` from that index on. `Mⁿ π dₙ → 0` and `ℤᵈ` is closed
   (`isClosed_lattice`), so `G(T − t) − G(T) − t u ∈ ℤᵈ`.
6. **The solenoid** (`solenoid`, `shiftS_bijective`, `realize`, `realize_inflate`). The torus map
   only semiconjugates to the endomorphism `M` of `ℝᵈ/ℤᵈ`, which fails to be injective when
   `|det M| ≠ 1`. The realization is `T ↦ ([G(Tₙ)])ₙ`. Step 4 gives `M [G(Tₙ₊₁)] = [G(Tₙ)]`, so
   this is a solenoid point, and the shift `Â(zₙ) = (M zₙ)` has inverse `(zₙ) ↦ (zₙ₊₁)`.
   Inflation is carried to `Â` coordinatewise. Translation is carried to
   `flow t (zₙ) = (zₙ + [t β⁻ⁿ u])` (`realize_translate`). This matches BBK (3.10) and (3.12).
7. **(R4)** (`torusRealize_periodic_vertex`, `realize_r4`). If `inflateᵖ T = T` and a tile ends
   at `0`, then `x₀ = 0` (`tileAt_next`) and `T_{pk} = T`. By step 3 the partial sums at
   indices `pk` lie in `ℤᵈ`, so `[G(T)] = 0`. For level `n`, `Mᵖ` fixes `zₙ = [G(Tₙ)]` and
   `Mⁿ zₙ = z₀ = 0`; therefore `zₙ = M^{pn} zₙ = M^{pn−n} 0 = 0`.
8. **Bridge** (`publishedInputs`). Given BDS and finite fibres for `realize`, the old bundle
   is produced with `A = shiftS`, `q₀ = 0` and every other realization field proved. The hull
   consumers `hull_two_step_iff_zero_fibre` and `hull_branch_triple_dichotomy` therefore
   apply with the constructed map.

**Relation to BBK Definition 3.1.** BBK place `p_k := min I − u_i` in the inverse limit of `A`
on `V/Σ`. For irreducible Pisot `σ`, `V = ℝᵈ`, `Σ = Γ = ℤᵈ` (their §3), and the `u_i` vanish
modulo `Σ`. The tiling coordinate is the projection of the strand along `Eˢ`. The strand vertex
of the origin edge at level `n` is then `G(Tₙ)` modulo `ℤᵈ`, which is the map above. This
identification is a written argument. It is what lets BBK Theorem 4.2 be quoted for the
constructed map, and it is not machine-checked.

### Evidence and replay

| Module | Checked scope |
| --- | --- |
| [`PeriodicPartnerRealization.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerRealization.lean) | Lattice, matrix and torus map; `PisotData`; level sequences, series and congruences; tile neighbours; desubstitution; torus map; solenoid, `realize`, semiconjugacy, flow, (R4), `publishedInputs`. |
| [`PeriodicPartnerRealizationModels.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerRealizationModels.lean) | Thue–Morse and Fibonacci `PisotData`; Thue–Morse torus map not injective; Fibonacci torus map injective; the `doubled` control. |

```sh
(cd proof/PscVerif && lake build PscVerif.PeriodicPartnerRealization PscVerif.PeriodicPartnerRealizationModels)
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

The scoped gate compiles both modules with the rest of the periodic-partner closure from fresh
sources, and audits every compiled declaration for the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) only. Session receipt (Lean `v4.34.0-rc2`, source snapshot
`aad53f79…306c` over 222 files): `PSC_PERIODIC_PARTNER_AUDIT_VERIFIED 16 806 561 336`,
`PSC_PERIODIC_PARTNER_GATE_COMPLETE fresh-local-closure standard-axioms-only`. The hosted CI
receipt is separate.

### Negative controls

| Model | Point checked |
| --- | --- |
| Thue–Morse, `M = [[1,1],[1,1]]` | `PisotData` holds with `C = 1`, `ρ = 0`, `u = (½, ½)`. `torusMap` sends `(½, 0)` and `(0, ½)` to `(½, ½)`, so it is not injective (`thueMorse_torusMap_not_injective`). On the actual hull under bijective inflation, a period-two tiling and its translate by two have the same depth-zero class and different depth-one classes (`thueMorse_hull_depth_zero_loses_information`). |
| Fibonacci, `ℓ = (φ, 1)`, `M = [[1,1],[1,0]]` | `PisotData` with `C = 1`, `ρ = |ψ|`: `M` acts as `ψ` on `ker ℓ`. `torusMap` is injective, so the first solenoid coordinate is injective (`fibonacci_coord_zero_injective`). This is the unit case, in which the solenoid is the torus. |
| `0 ↦ 011`, `1 ↦ 100`, unit lengths, `β = 3` | `M (1,−1) = −(1,−1)` on `ker ℓ`, so `‖Mⁿ (1,−1)‖ = 1`. No `PisotData` exists (`doubled_not_pisot`). The contraction is a real restriction and not vacuous. |

Neither model discharges recognizability, BDS or finite fibres, and neither is a PIP3 member.
Thue–Morse is not irreducible Pisot. BBK §4 cite the Morse substitution as a case where realization is not a.e. one-to-one.

### Non-claims / remaining gaps

1. **Finite fibres are not proved.** BBK Theorem 4.2 is supplied as `hfin` for the
   constructed `realize`. The identification of `realize` with BBK's `h_φ` is written, not
   machine-checked.
2. **The Pisot contraction is not derived** from the characteristic polynomial. It is a
   `PisotData` field, checked here only for Fibonacci and Thue–Morse. No PIP3 member is
   instantiated.
   *Update:* the [contraction note](c4-pisot-contraction-2026-11-19.md) derives `PisotData`
   from `χ_M = (X − β) Q` with `Q(β) ≠ 0` and the roots of `Q` in the unit disc, and that from
   the PIP3 conditions; Tribonacci `01/02/0` is proved a PIP3 member and instantiated.
3. **Recognizability is imported** as bijectivity of `inflateH`. The models do not supply it.
4. **Hull continuity remains open.** The hull carries the exact-agreement ultrametric.
   The [topology follow-up](c4-geometric-realization-topology-2026-11-19.md) gives the solenoid
   the product-subspace topology and proves continuity of the shift and the target flow.
   Relating the realization to the ordinary tiling topology requires a separate proof.
   *Update:* the [ordinary-hull formalization](c4-ordinary-hull-topology-2026-11-19.md)
   gives the same legal tilings the usual small-translation/window topology and proves
   joint source translation continuity and forward inflation continuity. The unchanged
   realization on that presentation is continuous exactly when its exact-source map is
   continuous; neither side of this equivalence has been discharged.
   *Further update:* the [concrete continuity proof](c4-realization-continuity-2026-11-19.md)
   now discharges both sides under the existing Pisot, bijective-inflation and `beta > 1`
   hypotheses. Compact exact origin fibres and finite possible parent origins derive
   inverse continuity; uniform convergence of the actual stable series supplies the map
   continuity. Recognizability itself and the normalized BBK identification remain inputs
   or separate obligations.
5. The reducible case (`Σ ≠ Γ`, non-contracted `W`) is out of scope.
6. Gaps 2–6 of the [hull note](c4-tiling-hull-realization-2026-11-19.md#non-claims-and-remaining-gaps),
   witness selection under (NM_V) and the global rank-two contradiction are unchanged.

# Proposition B′ and Corollary B (i) in Lean — 2026-11-09

**Status:** Lean proof of the audit's corrected B′ and of Corollary B (i), local receipts only
(base `c15d0e33457f357e6b8d6aecd00f8148dd4f7c3d` plus the uncommitted working tree described
below; no hosted exact-head CI run yet). B′ is not a governed claim in `claim_governance.toml`,
and no claim status changes. Human mathematical review and novelty review stay deferred until
after PSC closure, as the [priority note](c4-bprime-machine-verification-priority-2026-11-07.md)
decided. Nothing here bears on the Pisot side: C4, A1′, BH and PSC remain open.

**Sources.** [General-structure note](c4-general-structure-2026-11-06.md) §3 (Proposition B′,
Corollary B and the written proof); the [independent audit](c4-bprime-independent-proof-audit-2026-11-07.md)
(corrected theorem, six-step proof, assumption inventory, acceptance matrix); the
[machine-verification priority note](c4-bprime-machine-verification-priority-2026-11-07.md)
(automation-first policy); `proof/bpa/BpaPrefixBridge.lean`; `tools/audit_bpa_bprime.py`;
`proof/quint/BpaCutBound.qnt`.

**Lean modules** (all in the root import closure of `proof/PscVerif/PscVerif.lean`):

| Module | Content | Named proofs in the bank |
| --- | --- | ---: |
| `PscVerif.BPrimeCore` | audit steps 2–6: cut bound, frequency-free averaging, growth, strict dominance, cyclicity, spectral exclusion, cubic boundary, the abstract core | 63 |
| `PscVerif.BPrimeBinding` | audit step 1: Sirvent–Solomyak (3.1) bound to the Lean reduction `Psc.Reduction.red`, termination to cut gaps | 103 |
| `PscVerif.BPrime` | composition: Proposition B′, its cubic Pisot reading, Corollary B (i), controls (a)–(e) | 56 |

## Work shown

### Assumptions and hypotheses

The theorem formalized is the audit's corrected statement, `Psc.BPrime.bprime`:

> Let `σ = subst s` be a substitution of a finite alphabet `α`, primitive (`∃ k ≥ 1, Mᵏ > 0`
> with `M = Psc.Incidence.inc s`), with `χ_M` irreducible over `ℚ`. Let `β` be named by a
> positive left eigenvector `ℓ M = β ℓ`. Let `u : ℕ → α` be a one-sided fixed point
> (`IsFixed s u`: the image of every prefix of `u` is a prefix of `u`) and `W ≠ []` a prefix of
> `u` (`PrefixOf u W`). If `I(W)` is finite, every complex root `z ≠ β` of `χ_M` has `‖z‖ ≤ 1`.

`I(W)` is `Psc.BPrimeBinding.IW s u W = ⋃ₙ Iₙ(W)`, where `Iₙ(W)` is the set of blocks of the
reduction `red` of the windows `(u[0,N), u[tₙ, tₙ+N))` over all zero returns `N`, with
`tₙ = |σⁿ(W)|`. Coincidence blocks `([c],[c])` are retained. The first track is always `u`
and the second its shift, as in Sirvent–Solomyak's `[u, S^{|W|}u]`. *Termination* means
that `I(W)` is finite, not termination with coincidence. The literal recursion (3.1)
(`ssLevel`: reduce `(u, S^{|W|}u)`, then reduce all substituted pairs) has the same union,
`IW_eq_iUnion_ssLevel`. So `bprime_ss` states B′ with termination read literally.

Variants: `bprime_perron` supplies `β` and `ℓ` from `Psc.PerronExistence.perron_inc`.
`bprime_isPisotOrSalem` (two or more letters) concludes `IsPisotOrSalem β`. `bprime_cubic`
and `bprime_cubic_isPisot` add `natDegree χ_M = 3` and conclude `‖z‖ < 1` and `IsPisot β`.

**Derived inside the proof, not assumed:**

- nonerasing (`Psc.PrimitiveExpansion.nonerasing_of_primitive`);
- recurrence, i.e. unbounded zero returns at every shift, from primitivity of `σ` itself
  with no power (`Psc.BPrimeBinding.unbounded_of_primitive`). This is the input the audit
  attributes to uniform recurrence.
- the prefix property `σⁿ(W) <+: u` for every `n` (`isPrefixOf_iterate`);
- `β > 1` on two or more letters, from primitivity alone (`Psc.BPrimeCore.one_lt_perron`);
- strict dominance `‖z‖ < β` for `z ≠ β` (`norm_lt_perron`);
- integrality of `β` and `minpoly ℚ β = χ_M` (`isIntegral_of_root`, `minpoly_eq_charpoly`).

**Hypotheses of the written proof that the Lean proof does not use:**

- letter frequencies `f` and Cesàro limits (audit step 3), replaced as described below;
- Galois-normalized eigenvectors and conjugate coefficients `c_λ` (the written proof in §3 of
  the general-structure note), replaced by the audit's cyclicity route;
- diagonalizability (the audit already drops it);
- integrality in the cubic boundary (`norm_ne_one_of_cubic` needs a monic irreducible rational
  cubic only).

Inside the core, cuts can be weakened to a bounded discrepancy along `tₙ`
(`bprime_core_of_discrepancy`). Irreducibility is not used by the orbit bound
`eigen_orbit_bound`. It enters only through `q · w ≠ 0` (step 4), the cubic boundary
(step 6) and the minimal-polynomial reading.

**Hypotheses a Lean control shows cannot be dropped from a step.** Each control refutes the
weakened *step*, not B′ itself (see Negative controls):

- irreducibility in the nonvanishing step 4 (`reducible_control`);
- recurrence, which primitivity supplies, in the passage from termination to cut gaps
  (`stairBoundedGaps`, `stair_not_primitive`);
- the degree hypothesis of the abstract cubic-boundary lemma `norm_ne_one_of_cubic`
  (`degree_three_needed`). `X² + 1` is monic and irreducible over `ℚ` with the root `i` on
  the unit circle. That is a statement about arbitrary monic irreducible rational
  polynomials. `X² + 1` is not the `χ_M` of any primitive substitution, so the control does
  not show that degree three is necessary for the strict disc in B′.

**Scope of the strict disc.** The strict disc `‖z‖ < 1` is formalized only for
`natDegree χ_M = 3` (`bprime_cubic`). In degree two, Lean has only the closed disc. There the
strict disc follows by hand: the conjugate `tr M − β` of `β` is real, and modulus one would
make it `±1 ∈ ℚ`, a rational root of the irreducible `χ_M`. This is not stated in Lean. In
degree `≥ 4`, Lean has only the closed disc. Nothing is known here or claimed about the
strict disc there, that is, whether some Salem substitution has a terminating prefix-seeded
`bpa-W`.

**Scope, not necessity: the fixed point.** B′ is stated for a one-sided fixed point `u` and a
prefix `W` of `u`. `plastic_not_isFixed` shows that the plastic substitution
`0 ↦ 1, 1 ↦ 2, 2 ↦ 01` has no one-sided fixed point. So B′ does not apply to it, which is why
the cubic positive control is Tribonacci. This is a remark about scope. It does not show that
the fixed-point hypothesis is necessary for B′'s conclusion.

**Standing PSC hypotheses.** The primitive irreducible Pisot (PIP) regime of the programme is a
different hypothesis set. B′ concludes "Pisot or Salem" from termination; it supplies no
productivity, coincidence or termination fact for any Pisot substitution.

### Derivation / reduction

The proof follows the audit's six steps. Step 3 is replaced and step 5 is re-routed.

**Step 1: binding (3.1)** (`PscVerif.BPrimeBinding`).

- Windows `win u t N = u[t, t+N)` and zero returns (`Equiv1` of the two windows).
- `blocks u t N = red (win u 0 N) (win u t N)`, which is independent of `N` along zero
  returns (`blocks_prefix`, `mem_levelSet_iff_ge`).
- With `φ(t) = |σ(u[0,t))|`, the fixed point gives `σ(u[t, t+N)) = u[φ t, φ t + …)`
  (`subst_win`). Hence `blocks u (φ t) (φ N)` is the concatenation of the red-children of
  `blocks u t N` (`blocks_phi`, via `Psc.Descendants.red_subst`).
- The index relation is `t_{n+1} = φ(tₙ)` (`tn_succ`).
- (3.1) holds as `I_{n+1}(W) = {T | ∃ U ∈ Iₙ(W), Child s U T}` (`I_succ_of_primitive`). The
  recursive and window definitions agree at every level (`ssLevel_eq_of_primitive`), and
  `I(W)` is the child closure of `I₀(W)` (`IW_eq_reachable_of_primitive`).
- If `I(W)` is finite with block lengths `≤ L`, unbounded zero returns give a common cut
  within `L` of every position, at every level, with one `L` (`boundedGaps_of_finite_primitive`;
  in the consumed form, `Psc.BPrime.cutGaps_of_finite`).

This is the second use of the fixed point in the audit's inventory (substituted reductions are
shifts of the same `u`). The first use is `P(tₙ) = Mⁿ w` below.

**Step 2: cut bound** (`PscVerif.BPrimeCore`). Let `P(k)` be the Parikh vector of `u[0,k)` in
`ℤ^α` and `D_t(k) = P(k) − (P(t+k) − P(t))`.

- The shift/factor identity `D_t(k) = P(t) − (P(k+t) − P(k))` is `shift_factor_identity` and
  `D_eq_factor`; it is the content of `proof/bpa/BpaPrefixBridge.lean`.
- Each coordinate of `D` moves by at most one per letter (`abs_D_sub_le`) and vanishes at
  every cut, so `CutGaps u t L` gives `|D_t(k)_a| ≤ L` (`cut_bound`).
- In block form, with aligned blocks of length `≤ L` and cuts `c 0 = 0 < c 1 < ⋯`, the bound is
  strict, `|D| < L`, because `D` vanishes at each block end (`cut_bound_of_blocks`,
  `exists_cut_of_blocks`). This is the off-by-one item of P0.2.
- With the prefix property, `P(tₙ) = Mⁿ w` for `w = p(W)` (`P_iterate`, via `parikh_iterate`).

**Step 3, replaced: frequency-free averaging along `t_m`.** Fix `t` and `K` and assume
`|D_t(·)| ≤ L` coordinatewise.

1. Sum the factor form over `k < K`: `Σ_{k<K} D_t(k) = K·P(t) − Σ_{k<K} (P(k+t) − P(k))`.
2. Exchange the window sums: `Σ_{k<K} (P(k+t) − P(k)) = Σ_{j<t} (P(K+j) − P(j))`. Both sides
   add up the letter indicators over the rectangle `k < K`, `j < t` (`window_sum_swap`; any
   abelian-group-valued `P`).
3. For `j < t`, `0 ≤ P(K+j) − P(K) ≤ j` and `0 ≤ P(j) ≤ j`, so
   `|P(K+j) − P(j) − P(K)| ≤ t`. Hence `|K·P(t) − t·P(K)| ≤ K L + t²` coordinatewise
   (`avg_bound`).
4. Now take `t = tₙ` and, instead of letting `K → ∞` through all integers, `K = t_m`, another
   substitution level. There `P(K) = M^m w` is known exactly:
   `|t_m Mⁿ w − tₙ M^m w| ≤ t_m L + tₙ²`.
5. Apply a complex left eigenvector `q M = z q`. Then `q · Mʲ w = zʲ q(w)`, so
   `‖t_m zⁿ q(w) − tₙ z^m q(w)‖ ≤ (t_m L + tₙ²) ‖q‖₁` (`eigen_window_bound`).
6. Divide by `t_m`:
   `‖z‖ⁿ |q(w)| ≤ L ‖q‖₁ + tₙ² ‖q‖₁ / t_m + tₙ |q(w)| ‖z‖^m / t_m`.
7. Two growth facts make the error terms vanish:
   - **growth:** `t_m ≥ c β^m` with `c = ℓ·w / Σℓ > 0`, since `ℓ·M^m w = β^m ℓ·w` and
     `M^m w ≥ 0` has coordinate sum `t_m` (`len_growth`);
   - **strict dominance:** `‖z‖ < β` (`norm_lt_perron`).
   With `β > 1`, the errors are `O(β^{−m})` and `O((‖z‖/β)^m)`. Letting `m → ∞` at fixed `n`
   gives `‖z‖ⁿ |q(w)| ≤ L ‖q‖₁` for every `n` (`orbit_limit_bound`, `eigen_orbit_bound`).

**What changes against audit step 3.** The audit sends `K → ∞` through all integers and needs
the frequency vector `f` (`P(K)/K → f`, `Mf = βf`) to reach `‖Mⁿw − tₙ f‖ ≤ L`. It then
kills the Perron direction by `q(f) = 0` for `z ≠ β`. The Lean route samples `K` only along
`t_m`. There `P(K)/K = M^m w / t_m` is exact. The Perron contamination is the term
`tₙ z^m q(w) / t_m`, and it is killed by `‖z‖ < β` together with `t_m ≍ β^m`. So no
frequencies, Cesàro limits, unique ergodicity or uniform convergence in `n` are constructed.
The price is strict dominance, which needs **primitivity**: an irreducible but imprimitive
nonnegative matrix has eigenvalues `β·ω` of modulus `β`.

**Strict dominance.** `‖z‖ ≤ β` is `Psc.PerronExistence.norm_le_of_pos_left_eigen`. In the
equality case, the Wielandt extremal theorem (`Psc.CocycleSpectrum.primitive_extremal` with
`S = N = M`) gives `z = ±β` and `M = ±DMD` for a diagonal sign matrix `D`. The sign `−1`
would give `(Mʲ)ᵢᵢ = −(Mʲ)ᵢᵢ` for odd `j`. That is impossible, because `Mᵏ` and `Mᵏ⁺¹` both
have positive diagonals and one exponent is odd. If `β ≤ 1`, which happens only on one
letter, the conclusion is `‖z‖ ≤ β` directly (`bprime_core_of_discrepancy`).

**Step 4: cyclicity on any alphabet** (`krylov_span_eq_top`, P1.4). Let `w ∈ ℚ^α`, `w ≠ 0`,
and let `U = span_ℚ {Mⁿ w}`.

- `U` is `M`-invariant and nonzero.
- `χ(M|_U)` divides `χ_M` (`Psc.SectorBridge.charpoly_restrict_dvd`).
- `χ(M|_U)` is monic of degree `dim U ≥ 1`, so irreducibility forces it to equal `χ_M`, and
  then `U = ℚ^α`.

This generalizes the `3 × 3` lemma `Psc.Cyclicity.invariant_eq_bot_or_top`. It follows that
every nonzero left eigenvector `q` over a field `K ⊇ ℚ` has `q · w ≠ 0`
(`dotProduct_ne_zero_of_left_eigen`). No Galois normalization of eigenvectors appears.

**Step 5: spectral exclusion.** If `‖zⁿ c‖ ≤ C` for all `n` and `c ≠ 0`, then `‖z‖ ≤ 1`
(`norm_le_one_of_bounded`). With `c = q · w`, the composition is `bprime_core_of_discrepancy`,
or `bprime_core` with cut input.

**Step 6: cubic boundary** (`norm_ne_one_of_cubic`). Let `f` be a monic irreducible rational
cubic and `z` a root with `‖z‖ = 1`.

- A real root of modulus one is `±1`, which is rational and so impossible.
- A non-real root `z` has `z z̄ = 1`, so the third root is `−f(0) ∈ ℚ`, again impossible.

Hence `bprime_core_cubic` and `bprime_cubic` give `‖z‖ < 1`. `bprime_cubic_isPisot` reads
this as `IsPisot β`, through `minpoly_eq_charpoly` and `isIntegral_of_root`.

**Composition.** `bprime` is `cutGaps_of_finite` + `isPrefixOf_iterate` + `bprime_core`.
Corollary B (i) is the contrapositive in three forms:

- `corB_infinite`: any alphabet, some root `z ≠ β` with `‖z‖ > 1`;
- `corB_infinite_of_not_isPisotOrSalem`;
- `corB_infinite_cubic`: three letters, irreducible non-Pisot `χ_M`.

Under these hypotheses, `I(W)` is infinite for **every** one-sided fixed point and **every**
nonempty prefix `W`. The literal-(3.1) forms are `corB_infinite_ss` and `corB_infinite_cubic_ss`.

### Evidence and replay

**Receipts (local, this session).** All are taken on base
`c15d0e33457f357e6b8d6aecd00f8148dd4f7c3d` with the uncommitted working tree, toolchain
`leanprover/lean4:v4.34.0-rc2`. File digests (SHA-256):

- `BPrimeCore.lean` `c3cfe60a…51f3`
- `BPrimeBinding.lean` `f9c9723b…8048`
- `BPrime.lean` `77ec2e5e…9138`
- `proof/bpa/BpaPrefixBridge.lean` `30a657a8…d692`

| Check | Result |
| --- | --- |
| `lake build PscVerif` | success, 8,961 jobs, 0 warnings |
| `ProofBankAudit.lean` | `PSC_AUDIT_COMPLETE 3950 3037`. Every declaration's axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; 424 audit lines come from the three B′ modules. |
| `make_proof_bank.py --check --audit-log` | all 1,823 named proofs reached |
| `tests/test_proof_bank.py` | pass (the library has no `private` declarations) |
| `BpaPrefixBridge.lean` standalone | compiles; `shift_factor_identity` depends on `[propext]` only |
| `tools/audit_bpa_bprime.py` | pass; Krylov determinant 1; 12-generation swap-seed regression `[1, 2, 4, …, 16]` |
| `sorry`/`admit`/`axiom`/`native_decide`/`private`/`set_option` in the three modules | none |

**No hosted CI receipt exists for an exact head.** Under the priority note's
automation-first policy, a missing job is no acceptance. Lean credit attaches to the exact
commit whose hosted `lake build` and axiom audit pass, and only to the declarations it
replays.

**Replay, incremental** (from the repository root, after `./tools/setup_lean.sh` where
needed). `AUDIT_LOG` is an absolute path, so it still resolves after the `cd` back to the
root:

```sh
AUDIT_LOG=$(mktemp)
cd proof/PscVerif
timeout 7000 lake build PscVerif
timeout 3000 lake env lean ProofBankAudit.lean > "$AUDIT_LOG" 2>&1   # last line: PSC_AUDIT_COMPLETE 3950 3037
lake env lean ../../proof/bpa/BpaPrefixBridge.lean                   # shift_factor_identity: [propext]
cd ../..
python3 tools/make_proof_bank.py --check --audit-log "$AUDIT_LOG"
python3 -m pytest -q tests/test_proof_bank.py
python3 tools/audit_bpa_bprime.py
```

The incremental replay reuses the local `.lake` build artifacts. **The clean-room replay is
`./tools/check_lean.sh`.** It is the step "Build the complete proof bank and replay its axiom
audit" of `.github/workflows/ci.yml`. It copies only the Lean sources and Lake configuration
of `proof/PscVerif` into an empty temporary workspace, so no local `.olean`, `.hash` or
`.trace` file is credited, and Mathlib's cache comes fresh from the pinned upstream. It then
rebuilds `PscVerif`, runs `ProofBankAudit.lean` and checks the proof bank against that log
(`make_proof_bank.py --check --audit-log`). This script is what hosted CI should run on the
exact head. It was not run in this session, so none of the receipts above is a clean-room
receipt.

**Acceptance matrix of the audit, item by item.**

| Item | Lean declarations | Disposition |
| --- | --- | --- |
| P0.1 shift/count identity | `PscVerif.BpaPrefixBridge.shift_factor_identity` (standalone); `Psc.BPrimeCore.shift_factor_identity`, `D_eq_factor`; `Psc.BPrimeBinding.zeroReturn_iff_factor` | formalized |
| P0.2 bounded-block cancellation, with the off-by-one at block ends | `Psc.BPrimeCore.abs_D_sub_le`, `D_add`, `cut_bound`, `block_bound`, `exists_cut_of_blocks`, `cut_bound_of_blocks` (strict `< L`), `cutGaps_of_blocks` | formalized, unbounded multi-letter statement |
| P0.3 bind (3.1): orientation, coincidences, `I_{n+1}` versus `tₙ` | `Psc.BPrimeBinding.I_succ_of_primitive`, `ssLevel_eq_of_primitive`, `IW_eq_iUnion_ssLevel`, `IW_eq_reachable_of_primitive`, `tn_succ`, `blocks_phi`, `boundedGaps_of_finite_primitive`; `Psc.BPrime.cutGaps_of_finite` | formalized against the Lean `Psc.Reduction.red` and `Psc.Descendants.Child`. A refinement proof for the Mojo `kernel/psc/bpa.mojo` is **open**. |
| P1.4 algebraic cyclicity | `Psc.BPrimeCore.krylov_span_eq_top`, `dotProduct_ne_zero_of_left_eigen` | formalized, any alphabet size |
| P1.5 averaging and growth | `Psc.BPrimeCore.window_sum_swap`, `avg_bound`, `eigen_window_bound`, `len_growth`, `one_lt_perron`, `norm_lt_perron`, `orbit_limit_bound`, `eigen_orbit_bound`, `norm_le_one_of_bounded` | formalized in the **frequency-free** form. The frequency/Cesàro statement itself is not formalized and is not needed. |
| P1.6 sources and novelty | none | **open**, deferred until after PSC closure (priority note) |
| P2.7 Quint/TLA+ finite bounds | `proof/quint/BpaCutBound.qnt` unchanged (one coordinate, `L = 3`) | **open**. The adversarial mistakes (missing child, wrong orientation, shifted offset) are not modelled. The unbounded statement the model would calibrate is P0.2, now in Lean. |
| (composition) corrected theorem and Corollary B (i) | `Psc.BPrime.bprime`, `bprime_ss`, `bprime_isPisotOrSalem`, `bprime_cubic_isPisot`, `corB_infinite`, `corB_infinite_cubic`, `corB_infinite_ss`, `corB_infinite_cubic_ss` | formalized |
| (step 6) cubic boundary | `Psc.BPrimeCore.norm_ne_one_of_cubic` | formalized |

### Negative controls

Each control is a Lean theorem in the modules above.

- **(a) The audit specimen** `0 ↦ 01, 1 ↦ 2, 2 ↦ 00`, with `χ_M = X³ − X² − 2`.
  - `zeta_control` discharges every hypothesis of Corollary B (i): `M⁴ > 0` by
    `decide +kernel`, irreducibility by the rational-root lemma `irreducible_cubic`, a Perron
    root that is not Pisot, and a non-Perron root of modulus `> 1` (`zeta_root_outside`).
  - `zetaU_IW_infinite`: the `bpa-0` of the fixed point `σ^ω(0)` does not terminate. The same
    follows through each other form: `zetaU_IW_infinite_of_root`,
    `zetaU_IW_infinite_of_not_isPisotOrSalem`, and `zetaU_ssLevel_infinite` (the literal
    recursion).
  - At the level of the core, `zeta_unbounded_discrepancy` and `zeta_no_uniform_cuts`: for
    every word with the prefix property and every `W ≠ []`, no uniform discrepancy bound and
    no uniform cut gap exist.
  - The least primitivity exponent is 4 (`zeta_primitive`: `M⁴ > 0`, `M³` not), where the
    audit and the script report 5, which is true but not minimal.
- **(b) Irreducibility is necessary in step 4.** `irreducibility_needed` and
  `reducible_control`: `0 ↦ 0001, 1 ↦ 0111` realizes the positive matrix
  `M = [[3,1],[1,3]]`, with `χ_M = (X − 2)(X − 4)` reducible over `ℚ`. The left eigenvector
  `(1, −1)` of the non-Perron root `2 > 1` kills `p(01)`. This refutes dropping irreducibility from the nonvanishing step, not B′ itself: `01` is
  not a prefix of a fixed point.
- **The cubic-boundary lemma needs its degree hypothesis.** `degree_three_needed`: `X² + 1`
  is monic and irreducible over `ℚ`, with the root `i` on the unit circle. This controls the
  abstract lemma `norm_ne_one_of_cubic` among arbitrary monic irreducible rational
  polynomials, not B′. `X² + 1` is not the `χ_M` of a primitive substitution, and in degree
  two the strict disc holds by hand (see "Scope of the strict disc").
- **Recurrence and primitivity cannot be dropped from "termination gives cut gaps."**
  `stairBoundedGaps` and `stair_not_primitive` use the non-primitive `0 ↦ 01, 1 ↦ 1` with
  fixed point `0 1^∞` and `W = 0`. Every hypothesis of `boundedGaps_of_finite` except
  recurrence (`Unbounded`) holds, and `I(0)` is empty, hence finite. Yet `BoundedGaps` fails at
  every level for every `L`.
- **Positive controls (non-vacuity).**
  - `one_letter_control` (`0 ↦ 00`): every hypothesis holds; the conclusion is empty there.
  - `Psc.BPrimeBinding.per_control` (`0 ↦ 01, 1 ↦ 01`): the fixed point, the prefix seed,
    primitivity and a finite `I(0)` are proved in Lean. Its `χ_M = X² − 2X = X(X − 2)` is
    reducible over `ℚ`. That is computed by hand and is not a conjunct of the Lean statement.
  - **(e) Fibonacci** `0 ↦ 01, 1 ↦ 0` with `W = 0`: `fib_control` meets every hypothesis of
    `bprime` with irreducible `χ_M = X² − X − 1`, and `I(0)` is finite
    (`Psc.BPrimeBinding.fib_terminates`). `fib_bprime` then puts `1 − β` in the closed disc.
  - **(c) Tribonacci**: `trib_control` meets every hypothesis of `bprime_cubic_isPisot`
    except the finiteness of `I(0)`, which is not checked. Its conclusion `IsPisot β` is
    proved directly (`trib_isPisot`).
- **Python and Quint controls.**
  - `tools/audit_bpa_bprime.py` is a 12-generation regression of the child closure of the
    swap seed `(01, 10)`. It is not a nontermination proof. For the specimen's fixed point
    `σ^ω(0) = 012000101012…`, `(01, 10)` is a block of `I₀(0)`: it occurs at positions
    `[5,7)` and `[7,9)` of the reduction of `(u, S¹u)`. By hand, `u[0,k)` and `u[1,k+1)` have
    equal Parikh vectors at `k = 5, 7, 9` and unequal ones at `k = 6, 8`. This is not stated
    in Lean. Since `I(W)` is child-closed (`Psc.BPrimeBinding.IW_childClosed`), the script's
    closure is a sub-closure of `I(0)`, and its generation `g` lies in `I_g(0)`
    (`child_mem_I_succ`). So its growth `[1, 2, 4, …, 16]` is a bounded non-proof regression
    both for Corollary B (i) at `W = 0` and for (iii). For (i) on the specimen,
    the proof is the Lean theorem `zetaU_IW_infinite`. The script is also an independent
    arithmetic check: incidence, characteristic coefficients, rational-root test, Krylov
    determinant 1.
  - `BpaCutBound.qnt` is a bounded one-coordinate model. It proves nothing unbounded.

### Non-claims / remaining gaps

- **Nothing on the Pisot side.** B′ concludes that a terminating prefix-seeded `bpa-W` forces
  Pisot or Salem. It supplies no termination, productivity or coincidence statement for any
  Pisot substitution. General C4, A1′ (#138), BH (#139), seedwise overlap productivity, G1 and
  PSC remain open, and no claim status changes.
- **Spectral half of Sirvent–Solomyak Remark 2.** Pure discrete spectrum is not addressed.
  Only the non-termination half is formalized, and only in B′'s scope: primitive `σ`, `χ_M`
  irreducible over `ℚ`, some root `z ≠ β` with `‖z‖ > 1`, a one-sided fixed point and a
  nonempty prefix seed. On two or more letters the root condition says that `β` is neither
  Pisot nor Salem. On three letters it says that `β` is not Pisot.
- **The strict disc outside degree three.** The strict disc is formalized only for
  `natDegree χ_M = 3`. In degree two, only the closed disc is in Lean. The strict disc follows
  there by hand (the conjugate is real and irrational) but is not stated. In degree `≥ 4`,
  only the closed disc `‖z‖ ≤ 1` is formalized. Nothing is known here or claimed about
  whether a Salem substitution can have a terminating prefix-seeded `bpa-W`.
  `degree_three_needed` concerns the abstract lemma `norm_ne_one_of_cubic` and marks no
  boundary of B′.
- **Prior-art status unchanged.** The Lean proof is evidence of correctness at its stated
  scope, not of novelty or priority. The audit's source table stands. Human mathematical review
  and comprehensive novelty review are deferred until after PSC closure, per the priority note;
  B′ keeps its written-argument classification, human review pending.
- **Not formalized:**
  - Corollary B (ii) and (iii), which rest on R3 and R2;
  - the remark that `I(W)` contains a noncoincident pair;
  - periodic points that are not fixed points (passing to a fixing power);
  - `bpa` seeds other than prefixes of a fixed point;
  - existence of a fixed point for a general primitive `σ` (only seeds `u₀ <+: σ(u₀)`,
    `exists_isFixed_of_seed`);
  - a refinement proof binding `kernel/psc/bpa.mojo` to the Lean `red`.
- **Finite `I(W)` on three letters.** No irreducible three-letter specimen has a
  machine-checked finite `I(W)`; Tribonacci's termination is not checked. The only irreducible
  specimen with a checked finite `I(W)` is Fibonacci, on two letters, for `W = 0` only.
- **The written §3 proof is not what was formalized.** The general-structure note's argument
  through Galois-conjugate coefficients `c_λ` and the linear independence of
  `e_λ − (𝟙·e_λ) f` is not checked. The Lean route is the audit's cyclicity argument with
  frequency-free averaging and strict dominance.
- **Receipts are local.** There is no hosted exact-head CI run, and nothing is staged or
  committed by this integration. The status prose of the general-structure note §7 ("no
  executable claim is made") and the audit's acceptance matrix are left as historical text.
  Dated status lines are appended to the general-structure note and the priority note.
- **Proof bank.** `claim_governance.toml` has no claim for B′ or Corollary B, so no
  `lean_support` binding is added to `proof/proof-bank.toml`. `BPATerminationInterface`
  governs the literature interface "PDS ⇔ termination with coincidence" for Pisot
  substitutions, which is a different statement. The 222 declarations appear in the proof
  bank's named-proof inventory only.

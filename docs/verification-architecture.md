# Verification architecture

Three layers, each doing what it is actually good at. Nothing is claimed by more
than one of them, and every layer states its own scope.

| Layer | Tool | Question it answers | Where |
|---|---|---|---|
| Computational kernel | Mojo | *Is the finite arithmetic right?* Exact integer and rational computation over the seed data, `W₃`, `Θ`, `Φ₃`, the PIP corpus, and `B_σ`. | `mojo/` |
| State machine | TLA+ / TLC | *Does the automaton behave as claimed, and what depends on what?* `B_σ` as a transition system; the proof-dependency ledger. | `tla/` |
| Deductive core | Lean 4 + Mathlib | *Do the theorems follow?* Machine-checked proofs of the finite algebra, with an axiom audit. | `PscVerif/` |

Run everything with `scripts/verify_all.sh`.

## Why this split

The Spectral module of `PROOF_CERTIFICATE.md` is finite algebra over `ℤ` and `ℚ`.
That part is fully mechanisable and is mechanised twice: computed exactly in Mojo
and proved in Lean. The open part of the program is not algebra at all — hypothesis
G1 (finiteness of `B_σ`) and the SCC Producer conjecture are statements about a
transition system, which is what TLA+ is for. And the failure mode this project
actually experienced — a certificate carrying an "unconditional" claim for four
months while resting on a withdrawn theorem — is a *dependency* error, which is
why the ledger itself is machine-checked.

## Layer 1 — Mojo kernel (`mojo/`)

Exact arithmetic only; no floating point anywhere in the kernel.

```
psc/rational    exact Q arithmetic
psc/qlinalg     RREF, rank, nullspace, span membership over Q
psc/mat3        3x3 integer matrices, adjugate, characteristic polynomial
psc/tensor3     V^(x)3 lex coordinates, the shuffle functional, M^(x)3, Theta
psc/words       scattered-subword counts N_i, N_ij, N_ijk and K_1, K_2, K_3
psc/w3          the shuffle-kernel sector, derived as ker S
psc/seeds       the six length-7 K_2-zero seed words
psc/pisot       exact PIP decision procedure
psc/bpa         balanced-pair automaton, Tarjan SCCs, productivity
psc/certificate the section 13 checklist as ten derived checks
```

**Derived, not transcribed.** The seed matrices `A_k`, their characteristic
polynomials, traces, eigenvectors and `dim W₃` are all recomputed from the seed
*words* and the definitions. The certificate's printed tables (§3 basis, §6
matrices) are kept only as independent cross-check targets, and the checks
compare the two.

**The PIP decision procedure** (`psc/pisot`) decides the standing regime exactly:
primitivity by Wielandt's bound, irreducibility of the characteristic cubic by
rational-root enumeration, and the Pisot condition by Sturm sequences over `ℚ`
(three-real-root case) together with the exact identity `β·|β₂|² = det M`
(complex-pair case). It was cross-validated against a floating-point root finder
on all `3⁹ = 19683` matrices with entries in `0..2`: exact agreement, 2442 PIP
matrices.

`mojo/verify.mojo` runs ten checks, all passing:

| Check | Content |
|---|---|
| C1 | `dim W₃ = 8`, derived as `ker S` |
| C2 | the certificate's printed basis `b₁…b₈` spans `ker S` |
| C3 | the six seeds are balanced of length 7 with `K₁ = K₂ = 0` |
| C4 | `K₃(s_k) ∈ W₃` |
| C5 | `Θ(K₃(s_k))` equals the tabulated `A_k` |
| C6 | `A_k` nonzero, traceless, rank 3, `tr(A_k²) = 6`, `A_k(1,1,1)ᵀ = λ_k(1,1,1)ᵀ` |
| C7 | the `Θ`-intertwining identity on the PIP corpus (2442 × 6 instances) |
| C8 | `W₃` is `M^{⊗3}`-invariant on the PIP corpus |
| C9 | **Target 1**: `(Φ₃ − det M)² K₃(s_k) ≠ 0` on 14652 instances |
| C10 | no PIP incidence matrix has all row sums equal |

`mojo/census.mojo` runs the exhaustive alphabet-3 census (images of length ≤ 3)
and reproduces the documented figures: **4554 PIP specimens, `B_σ` construction
terminating 4554/4554 with 0 caps, largest `|B_σ| = 1502`, and 4554/4554
productive**, in about a minute.

That census is *elimination over a finite corpus*, not a proof. G1 and SCC
Producer remain open.

## Layer 2 — TLA+ (`tla/`)

`BPA.tla` specifies the construction of `B_σ` as a breadth-first state machine
over balanced pairs. Invariants: `TypeOK`, `AllBalanced` (the `K₁ = 0` statement),
`NormalIdempotent`, `CuttingPreservesLength`, `NoOverflow`, `TerminatesInBound`
and `Productive`.

Termination is stated as the bounded-rounds safety property `TerminatesInBound`
rather than as `<>(frontier = {})`. `Step` is a deterministic function of the
state and is enabled exactly while the frontier is non-empty, so the spec has a
single behaviour; a safety bound on the number of rounds is therefore equally
precise, and it keeps the check inside TLC's model-checking mode.

`Productive` is the SCC Producer conjecture restricted to the reachable part of
`B_σ` for one `σ`. **`MCNonProductive` is a negative control** — a primitive but
non-Pisot substitution where `Productive` is violated — so the passing runs are
not vacuous.

`ProofArchitecture.tla` makes the dependency ledger executable: a result becomes
establishable only when every prerequisite is, and a withdrawn result never does.
`Ledger.tla` encodes the v15/v34 ledger. Machine-checked outcomes:

| Assumed | Result |
|---|---|
| nothing | `PDS` unreachable, `LoadBearingSCC` unreachable, nothing depends on the withdrawn v5 Thm 5.1 |
| nothing | the §14 Spectral Black Box **is** reachable — it needs no hypothesis |
| `G1` | `LoadBearingSCC` reachable, `PDS` still not |
| `G1`, `SCCProducer` | `PDS` reachable |

That last pair is the boxed conditional of `PSC_PROOF_v15`, checked mechanically
rather than asserted in prose.

`tla/check.sh` runs all nine models and asserts each expected outcome, including
the three that must fail.

## Layer 3 — Lean 4 (`PscVerif/`)

Proved, with `#print axioms` reporting only `propext`, `Classical.choice` and
`Quot.sound` — no `sorry`:

- `N_mul_N`, `N_mul_N₂` — the degree-2 and degree-3 shuffle identities on words.
- `BalancedPair.K₃_shuffle_zero` — §3's "certified fact 3".
- `seed_K₂_zero`, `seed_length`, `seed_K₃_mem_W₃` — §4's seed list.
- `theta_seed` — §6's table, derived from the seed words.
- `trace_A`, `trace_sq_A`, `det_A_ne_zero`, `A_ne_zero` — §6 properties 1, 2, 3, 7.
- `Aq_mulVec_ones`, `Aq_eigenspace` — §6 property 6, both halves.
- `no_commuting_of_no_eigenvalue` — the centralizer contradiction, over any field.
- `target1` — **PIP-Locus Target 1** in contradiction form.
- `no_equal_row_sums` — §7's concrete corollary.
- `trace_sq_cyclicPlus/Minus`, `Aq_not_conj_cyclicPlus/Minus` — §9's trace
  obstruction and the Dominant Cubic Capture step.

Not formalised, and said so in `PscVerif/Spectral.lean`: the `Θ`-intertwining
polynomial identity in `ℤ[m_ij]` (verified exactly by the Mojo kernel instead),
semisimplicity of `Φ₃`, the Galois-transitivity arguments of §8–§9, the passage
from a nonzero dominant projection to a spectral-radius bound, G1, SCC Producer,
and everything in §12.

## Discrepancies found

Three, from mechanising the certificate. None changes a conclusion.

### D1 — the shuffle map in §3 is written transposed

§3 defines the shuffle map by its action on basis vectors,

> `S(e_a ⊗ e_b ⊗ e_c) = e_{abc} + e_{bac} + e_{bca}`.

Read literally, the printed basis `b₁…b₈` does **not** lie in `ker S`, and neither
does any `K₃(s_k)`. Read coordinatewise — `(Sx)_{abc} = x_{abc} + x_{bac} + x_{bca}`,
the transpose — the printed basis spans `ker S` exactly, and all six seeds lie in
it. The coordinate form is the one the rest of the certificate uses, and it is
what the kernel and the Lean development implement.

### D2 — §3's "certified fact 3" needs correction terms

The identity behind `K₂(s) = 0 ⟹ K₃(s) ∈ W₃` is not the naive shuffle product
`a ⧢ bc = abc + bac + bca`. When letters coincide a position can be shared between
the two factors:

> `N_a · N_{bc} = N_{abc} + N_{bac} + N_{bca} + ⟦a = b⟧·N_{ac} + ⟦a = c⟧·N_{ba}`

(proved in `PscVerif/Shuffle.lean` as `N_mul_N₂`; the naive form fails on diagonal
indices). The corrections are degree-2 counts, so they cancel exactly when
`K₂ = 0` — the certificate's conclusion is correct, its stated reason is
incomplete.

### D3 — `V34_CLOSURE.md`'s status table contradicts its own patched header

The header of `certificates_patched/V34_CLOSURE.md` correctly says the
Load-Bearing SCC Theorem is *conditional on finite `B_σ` (G1)*, and step 1 of the
proof spine marks v5 Thm 5.1 withdrawn. But the status table further down still
reads

> `| Finite B_σ for PIP σ on alphabet 3 | Proved (PSC_PROOF_v5 Thm 5.1) |`
> `| **Load-Bearing SCC Theorem** | **Unconditional** |`

and the file list still cites `PSC_PROOF_v5.pdf — Theorem 5.1 (Finiteness of B_σ)`.
This is the exact claim the September remediation was meant to remove. The archived
file is left unedited; `tla/Ledger.tla` encodes the corrected dependency, and
`MCArchitectureOpen` checks mechanically that `LoadBearingSCC` is *not* reachable
without assuming G1.

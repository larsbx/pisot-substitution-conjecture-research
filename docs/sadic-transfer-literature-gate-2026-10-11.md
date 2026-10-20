# Stop/go: imports from the S-adic programme — 2026-10-11

Targeted literature check (AGENTS.md review gate) before registering ledger
nodes taken from `larsbx/s-adic-pisot-conjecture-research` (`main@c379703`).
No new diagnostic and no universal invariant is proposed; the note decides
which of that programme's results are PSC claims and with what status.

## 1. The proposed claims

1. **(T) Flow-to-symbolic transfer.** For a PIP substitution, pure discrete
   spectrum of the Perron-length suspension tiling flow implies pure discrete
   spectrum of the substitutive `Z`-action `(X_sigma, S)`.
2. **(Ω-sym)** Theorem Ω's per-specimen certificate, today stated for the
   tiling `R`-action only (`BoxAutomatonPDSCertificate`, "no flow-to-subshift
   theorem"), gives symbolic pure discrete spectrum too. In particular the
   finite-domain theorem on 145,806 specimens holds for both actions.
3. **(Barge-sym)** A PIP substitution with a power, or a maximal
   common-prefix/suffix rotation of a power, in Barge's class or its mirror
   (`psc/barge_class.mojo`) has symbolic pure discrete spectrum. On the
   standing corpus this is the 1,248 specimens of side-notes ledger §3.
4. **(B″)** The S-adic programme's Corollary B″: in every dimension, every
   primitive composite of an admissible unordered Brun word whose
   characteristic polynomial is irreducible and Pisot has symbolic pure
   discrete spectrum.

## 2. Prior art

| Source | What it gives | Transfers? |
| --- | --- | --- |
| V. F. Sirvent, B. Solomyak, *Pure discrete spectrum for one-dimensional substitution systems of Pisot type*, Canad. Math. Bull. 45 (2002) 697–710, [doi:10.4153/CMB-2002-062-3](https://doi.org/10.4153/CMB-2002-062-3): p. 699 definition, §4, Corollary 5.2 | "Pisot type" = Perron–Frobenius eigenvalue Pisot **and** characteristic polynomial irreducible; prototiles have left-PF-eigenvector lengths; Cor. 5.2: PDS of the `R`-action `(X_T, Γ_x)` implies PDS of the `Z`-action. No unimodularity | **yes**: "Pisot type" is exactly PIP. Read from the primary text in the S-adic gate (`docs/literature-gate-2026-10-09.md` §9 there, entries SS02-def, SS02-§4, SS02-5.2, all *verified*); not re-read here |
| M. Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, DCDS-A 36 (2016) 1159–1173, [arXiv:1403.7826](https://arxiv.org/abs/1403.7826), Theorem 3.13, Remark 3.14, §2, §4.2 | flow PDS for primitive, Pisot-inflation substitutions injective on initial letters and (eventually) constant on final letters; prototiles `[0, ω_i]`, `ω` the positive left eigenvector; §4.2 lists Arnoux–Rauzy, the 3-letter Brun substitutions of BBJS and Jacobi–Perron | **yes**, already used here (`p1b-strict-zipper-literature-gate-2026-09-21.md`, side-notes ledger §3); hypotheses re-verified in the S-adic gate §8 |
| Clark–Sadun, ETDS 23 (2003); Barge–Kwapisz, Amer. J. Math. 128 (2006) | `Z`/`R` equivalence for irreducible (unit) Pisot | not load-bearing; SS02 suffices and needs no unimodularity |
| S-adic programme, `docs/sadic-g6-brun-higher-census.md` §§1, 2, 5 | Theorem B (Brun composites: final-letter map the identity, initial-letter map constant when every letter occurs), Lemma Rev (reversal), Corollaries B′, B″ | **yes** as a cross-programme family theorem (§3) |

## 3. Hypotheses that transfer, and those that do not

- **Pisot type = PIP.** The standing regime is primitive, irreducible
  characteristic polynomial, Pisot. That is SS02's definition verbatim. The
  tile lengths match: the box certificate's "Perron-length suspension" uses
  the positive left eigenvector, which is SS02 §4's and Barge §2's.
- **Powers, rotations, reversal.** `sigma^n` and a conjugate `sigma'`
  (`sigma(a) p = p sigma'(a)`) generate the same subshift as `sigma`, so a
  symbolic statement for them is one for `sigma`. `sigma^n` is again PIP: the
  Galois conjugates of a Pisot `beta` have modulus `< 1`, so `beta^n` has the
  same degree and `chi_{M^n}` stays irreducible. Reversal maps `X_sigma` to
  its mirror image, conjugating `S` to `S^{-1}`; the eigenvalues are
  conjugated, so pure discreteness is preserved (S-adic Lemma Rev for the
  flow; the same argument for `Z`).
- **Irreducibility is essential to (T).** For reducible β-substitutions
  Ei–Ito give flows with PDS whose subshifts lack it (Barge 2016 Remark 4.2;
  ABBLS survey §4). Every node registered here therefore keeps "irreducible"
  in its statement.
- **B″ is a family theorem, not progress on #84.** It quantifies over every
  member of the Brun family in every dimension, but the family is
  structurally special (mirror Barge class) and says nothing about a
  substitution outside it.
- **Novelty.** Nothing is claimed as new. On three letters Barge §4.2
  already covers the ordered BBJS Brun substitutions; the unordered
  `d`-letter admissibility argument is the S-adic programme's Theorem B. (T)
  is a citation; (Ω-sym) and (Barge-sym) are one-line compositions.

## 4. Negative controls

- **No Barge witness on Theorem K's open family** (side-notes ledger §3,
  2026-10-07): powers and rotations do not help there. An archived probe of
  2026-10-11 extends this to Durand's return-word derivation: of the 130
  primitive Pisot members with `|det M| = 2` and `|w_1|, |w_2| <= 4`, no
  derived substitution at any letter, or its square, is in Barge's class or
  its mirror. Exploratory, float screen for Pisot, not a registered claim
  (side-notes ledger §2). Driver, budget and per-member output:
  `archive/2026-10-11/return-word-barge-probe/`.
- **The direction is PSC → S-adic.** The S-adic metric theorems (BST23
  Theorem 3.1, S-adic Theorems S, C, C′) are almost-everywhere statements;
  constant directive sequences form a null set, and BST23 consumes a PDS
  periodic point as input. None of them is imported.

## 5. Decision

**Proceed, narrowed** to four ledger nodes plus one cross-programme import:

| Node | Kind | Rests on |
| --- | --- | --- |
| `SirventSolomyakTransfer` | imported | SS02 Cor. 5.2 |
| `BargeClassFlowPDS` | imported | Barge 2016 Thm 3.13, Rem. 3.14 |
| `BoxAutomatonSymbolicPDSCertificate` | repository-proved | `BoxAutomatonPDSCertificate`, `SirventSolomyakTransfer` |
| `BargeClassSymbolicPDS` | repository-proved | `BargeClassFlowPDS`, `SirventSolomyakTransfer`, §3 |
| `BrunCompositeSymbolicPDS` | imported (cross-programme) | S-adic Corollary B″ (Theorem B, Lemma Rev, Barge 16, SS02) |

No open premise moves. PSC remains open.

## 6. Addendum: porting the S-adic Lemma S — stop

*Proposed.* Replace G1b-1's spectral constant `D_sigma` by the S-adic
programme's Lemma S bound (`‖Δ(j)‖_∞ <= C` for every swap pair, `C` the
balance constant of `L_sigma`; `docs/t1-uniform-overlap-finiteness.md` there)
and measure how much the PSC certificates shrink.

*Finding.* No certificate consumes `D_sigma`:

- Theorem Ω's box automaton is the inflation closure of the start set
  `|w_m| <= R_m`, whose radii come from Pisot contraction on **formal**
  overlaps (Lemma Ω1, `psc.vertex_coincidence.box_radii`). Lemma S bounds
  only **realized** swap walks `sigma^N(ab)`, `sigma^N(ba)`, so it cannot
  bound the box.
- The seed-patch overlap graph is built by exact breadth-first closure from
  the seeds. Its size is a property of `sigma`, not of an a priori cap, and
  `kernel/swap_discrepancy_census.mojo` already evaluates the reachable
  supremum exactly ("no computation verifies its constant `D_sigma`").
- For a single substitution, an exact `C` is itself obtained from Pisot
  contraction of the fixed point's discrepancy, which is G1b-1's mechanism.
  Lemma S earns its keep in the S-adic setting only because there is no
  single matrix to contract.

*Decision.* **Stop.** The measured shrinkage is zero by construction. The one
residual value is robustness: Lemma S composed with a balance theorem for
primitive irreducible Pisot languages (Adamczewski, TCS 307 (2003), cited,
not gated) would give a second proof of G1b-1 without unimodularity. That is
not pursued, since G1b-1 is already proved (PR #69).

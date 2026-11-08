# R1 positive repair: all-state Tribonacci productivity

Baseline: `f5b6625d0d6bd33ee8f3f07289cdc23e0911dc11`. This accompanies the [productive-parent countercontrol](psc-r1-productivity-scope-2026-11-07.md) and the dated correction in the ledger-linked [boundary-localization note](psc-r1-boundary-localization-2026-11-07.md).

## Work shown

### Assumptions and hypotheses

Let a substitution send every letter to a word beginning with one common letter c. For any two nonempty words u=a u' and v=b v', their substituted words both begin with c. The preceding prefixes are EMPTY on both sides, so their first one-letter block is a genuine balanced diagonal, not merely a matching symbol at a nonzero residual.

### Derivation / reduction

The common-initial-letter premise is independent of root productivity. It supplies productivity for EVERY nonempty balanced-pair state. For the literal Tribonacci substitution `0->01,1->02,2->0`, the premise is checked for all three letters with c=0. Thus every nonempty balanced pair is productive after one inflation. Consequently this particular substitution has no nonempty strictly child-closed nonproductive balanced-pair class. This is a source-specific statement, not general PSC.

`R1CommonInitial.common_initial_letter_forces_diagonal` proves the word-level lifting for arbitrary alphabets and word lengths. Its three concrete companion theorems bind the literal images and refute first-step diagonal avoidance. The four declarations are explicitly axiom-audited. This is an elementary formalized sufficient condition, with no novelty claim. The repository's ordered-word completion and derived-factorization contracts remain the prior scope references; proceed only as a correction to the overstrong root-to-descendant inference.

### Evidence and replay

`proof/psc_routes/R1CommonInitial.lean` contains four proof declarations. `proof/quint/PscR1CommonInitial.qnt` independently checks all three images, all nine ordered first-letter pairs, and that the binary negative control does NOT satisfy the common-initial-letter premise. The shared exact-head workflow `psc-r1-productivity-scope.yml` requires 15 negative-control plus 4 positive-repair Lean receipts, and six plus three explicitly named Quint test successes.

Local exact finite-word arithmetic and static theorem/audit/YAML checks were executed. A Lean compiler and Quint runtime were not available in the working container; latest-head hosted acceptance must be inspected before awarding either formal-layer credit. No new canonical research algorithm or census is introduced.

### Negative controls

The binary legal pair control `001/100` under `0->01,1->10` has both diagonal descendants and a strict closed descendant class. Its two images begin with DIFFERENT letters, so it does not satisfy the sufficient premise used here. Do not generalize the Tribonacci argument to non-left-proper PIP substitutions. Nor does a common vertex or later equal-index symbol substitute for this first, equal-prefix diagonal.

### Non-claims / remaining gaps

The earlier inference was invalid in general, but the Tribonacci conclusion has a stronger valid replacement: every actual nonempty balanced-pair state under this literal substitution has a first-step diagonal. An ancestry-germ cycle is not itself automatically a balanced-pair state. The nine recorded finite ancestry loops therefore remain useful recurrence controls, not evidence of strict nonproductivity. For general PIP systems, complete occurrence support and a path from INSIDE the purported strict component still have to be supplied; root productivity is not a substitute.

No PSC/C4/BH/A1′/G1 status change or merge is authorized. Human validation remains post-closure, and all new exact-head formal receipts remain pending until actually observed.

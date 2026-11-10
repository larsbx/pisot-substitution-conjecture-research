# B′ machine-verification gate and PSC-first priority (2026-11-07)

**Decision:** independent human mathematical review and comprehensive novelty review are **deferred until after PSC closure**. This is not a waiver of machine-checkable correctness, and it does not promote the claim in the ledger. Treat B′ as a useful written non-Pisot theorem with a bounded list of **automatable** obligations. The critical path remains the existing Pisot-side C4 / seedwise overlap productivity / A1′ / BH gates, not further bibliographic work on B′.

**Source:** PR #504 at `e9cfafebb0b0c7448757fee6ef53f77d8042e95a`; independent audit PR #505, `docs/c4-bprime-independent-proof-audit-2026-11-07.md`. Source classifications are unchanged.

## Work shown

### Assumptions and hypotheses

For B′: a finite alphabet; a primitive, nonerasing substitution with irreducible degree-`d` characteristic polynomial; a one-sided fixed point; a **nonempty prefix** `W`; and finite Sirvent–Solomyak prefix-seeded `I(W)`, including all descendants and coincidence blocks. The balance bound is only at `t_n = |ζⁿ(W)|`. Its transfer to a full partition of `(u,S^{t_n}u)` must be verified independently of the numerical control.

For PSC: the standing primitive irreducible **Pisot** hypotheses are different. B′'s contrapositive for non-Pisot substitutions cannot by itself close any positive-Pisot overlap-productivity obligation.

### Derivation / reduction

The B′ proof decomposes into machine-verifiable lemmas:

1. Formalize the actual Sirvent–Solomyak recurrence for prefix seeds, with the initial index and every successor relation. Terminating `I(W)` yields a full aligned decomposition into uniformly bounded blocks, including coincidences.
2. Formalize the block-cut argument in `Fin d → ℤ` with an explicit maximum block length `L`. At all positions, the discrepancy between the two tracks is bounded by `L` in each coordinate.
3. Derive the shift/factor identity `P(k)−(P(t+k)−P(t)) = P(t)−(P(k+t)−P(k))`, then `‖Mⁿ w − (P(k+t_n)−P(k))‖∞ ≤ L`.
4. From primitive unique frequencies, take Cesàro averages for **fixed** `t_n`; obtain `‖Mⁿw−t_n f‖∞≤L` without assuming full-word bounded balance.
5. Prove the rational cyclic-vector lemma for irreducible `χ_M`: any nonzero `w∈ℚ^d` spans via `w,Mw,…,M^{d−1}w`. A nonzero left eigenfunctional `q` therefore satisfies `q(w)≠0`.
6. Apply the eigenfunctional to bound `|λ|ⁿ |q(w)|`, forcing `|λ|≤1`, and exclude unit-circle roots in an irreducible cubic.

**Lean** owns typed algebra, bounds and spectral implications. **Quint** is a bounded adversarial model of cut transitions and exact-seed obligations; it is not a substitute for universal word or spectral arguments. Deterministic Python provides independent exact-integer and short-word regression controls.

### Evidence and replay

At PR #505 exact head `67aa081b6012cc3e5f6be250e4a80ea7113d1037`:

- GitHub Actions run `42370477931`: `symbolic-audit` **passed**; `quint-cut-control` **passed**; `lean-bridge` **failed** before compiling the theorem, due to a module documentation comment preceding `import Mathlib`. That is a parsing failure, **not** a mathematical counterexample.
- Show-your-work run `42370477820` **failed** because the original PR body omitted mandatory evidence headings. This did not validate theorem status.
- This follow-up corrects the Lean file's import ordering and supplies a policy-compliant PR body. Exact-head hosted compilation must be rerun and assessed before giving even this small bridge Lean credit.

Reproduce portable controls:

```bash
python3 tools/audit_bpa_bprime.py
cd proof/PscVerif
lake env lean ../../proof/bpa/BpaPrefixBridge.lean
npx --yes @informalsystems/quint@0.33.1 typecheck ../../proof/quint/BpaCutBound.qnt
```

Use the pinned provisioning script before the Lean command when appropriate. The project CI is the actual exact-head evidence source; these commands alone do not establish a clean-room full Lean audit.

### Negative controls

A reducible positive matrix with an expanding non-Perron eigendirection and a seed orthogonal to that direction refutes nonvanishing without irreducibility; see the independent B′ audit. Finite swap-pair expansion is a regression, not a proof of nontermination. A Quint bounded single-coordinate model cannot prove unbounded multi-letter BPA closure or Pisot-side coincidence. Neither numerical experiments nor an accepted Lean cancellation identity imply C4, A1′, BH, seedwise overlap productivity or PSC.

### Non-claims / remaining gaps

- This follow-up does **not** prove B′ or Corollary B end to end in Lean and does **not** change their current written-argument classification.
- Formalized full aligned reduction, factor frequency averaging, cyclicity, and spectral exclusion are still pending.
- General C4, A1′ (#138), BH (#139), and PSC remain **open**, irrespective of B′'s eventual disposition.
- **Human review and comprehensive historical novelty determination are post-PSC archival tasks**, not merge gates or near-term research assignments.

## Automation-first acceptance policy

Do not confuse "no immediate human review" with an instruction to merge failing proof CI. Automatically compile each claimed formal lemma at an exact commit; treat missing jobs, skipped checks, failures and unverifiable receipts as no acceptance. A successful CI build of the present file proves **only** the shift/factor algebra identity. Autonomously pursue the next unformalized lemma and prioritize PSC's existing open universal gates over non-Pisot auxiliary results.

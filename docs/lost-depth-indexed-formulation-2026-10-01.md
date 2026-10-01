# Lost depth-indexed formulation: provenance record — 2026-10-01

**Status:** missing-source provenance record. Nothing below is a repository
result. Every item attributed to the lost files is unverified, is not cited by
any status surface, and must not enter `claim_governance.toml`, the ledgers or
the manuscript until it is reconstructed from scratch with its own proof or
replayable finite certificate. This note does not change the status of any
rung of `docs/proof-ladder.md`.

## 1. What was lost

Notes from earlier working conversations describe a parallel formulation of
the proof programme whose source files no longer exist anywhere reachable:

| Lost file | Recorded role |
| --- | --- |
| `PROOF_LADDER.md` (118 lines) | depth-indexed ladder, distinct from `docs/proof-ladder.md` |
| `PAPER_SUBMISSION.md` | submission plan |
| `LEVEL3_SUBMISSION.tex` | Level-3 manuscript draft |
| `SWEEP_RESULTS.md` | results of a 24,486-specimen sweep |
| `TRANSPORTABLE_METHOD.md` | method write-up |

Searched on 2026-10-01, with no hit for any file name or for the strings
`S-child`, `joint full support`, `9.26j`, `24486` / `24,486`,
`TRANSPORTABLE_METHOD`, `psc_suite`:

- every commit, every branch and every unreachable object (`git fsck
  --lost-found`) of this repository and of `larsbx/finite-math-kernels`;
- `larsbx/tiling-theory-research`, a single-commit stub;
- GitHub code search across the `larsbx` account;
- Google Drive full-text and title search.

## 2. The two formulations differ in what "level" indexes

In this repository a level names a **proof route**: Level 2 is finite BPA
(G1, reduced to the open G1b-2), and Level 3 is the SCC Producer, posed under
G1. The lost formulation used levels as **depth-indexed criteria** over a
larger class of substitutions. Statements do not transfer between the two
automatically. In particular, Level 3 here presupposes Level 2, so no
"higher level implies lower level" transfer exists on this ladder.

## 3. Recorded items and their disposition

| Recorded item (as the notes state it) | Disposition |
| --- | --- |
| Level 3 "computationally closed for all 24,486 substitutions with \|σ\| ≤ 8 via a 2-step criterion" | **Unverified; wording rejected.** The 2-step criterion's definition is lost. Under hypothesis-firewall item 8 of `docs/proof-ladder.md`, a finite sweep is finite-domain evidence and cannot close a level. The domain is recovered (§4). |
| "Joint full-support lemma", false by Tribonacci; remaining gap stated as joint-support growth | **Counterexample reproduced** (§5). The lemma plays no role on this repository's routes: the bad-SCC normal form already has `rank_Q(V_S) = \|A\|`. |
| "S-child" statement: child support = supp σ(x) ∪ supp σ(y) | **Elementary, to be re-derived where used:** σ(xy) = σ(x)σ(y), so supp σ(xy) = supp σ(x) ∪ supp σ(y). Which graph's "child" was meant is lost. |
| Level 2 "closed for ℤ-independent substitutions with max \|σ\| ≤ 4" (Thm 9.28, chain 9.26a–j) | **Unverified and suspect.** It adds ℤ-independence as a hypothesis, which firewall item 2 forbids, and it conflicts with G1b-2 remaining open. It may descend from the retracted inference "UD ⇒ bounded padding ⇒ finite BPA" (see `docs/completion-ledger-2026-09-11.md`); this is a conjecture about provenance, not a finding. If it is ever reconstructed, it can only be a restricted-class result inside G1b-2. |
| 4,554-PIP `psc_suite` run | Matches this repository's standing corpus (`mojo/psc/corpus.mojo`). |

## 4. Recovered sweep domain

The count 24,486 is exactly the number of primitive irreducible Pisot
substitutions on three letters with **total** image length
Σ_a |σ(a)| ≤ 8. "|σ| ≤ 8" in the notes therefore meant total length, not
maximum image length. Cumulative counts by maximum image length:

| max_a \|σ(a)\| ≤ | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- |
| count (Σ_a \|σ(a)\| ≤ 8) | 72 | 4,554 | 14,670 | 22,080 | 24,486 |

The standing 4,554 corpus is exactly the max-image ≤ 3 slice: total length 9
adds no member, because images of lengths (3,3,3) are constant-length, so
β = 3 and the incidence polynomial is reducible.

**Evidence class:** oracle-only. The table was computed with the existing
Python screen `src/psc_research/pip_screen.py` (`mat`, `charpoly`, `primitive`,
`irreducible`, `pisot`) by enumerating every image triple with
Σ_a |σ(a)| ≤ 8. It has no canonical Mojo counterpart yet; until it does, it is
a recovery aid and not a repository census.

## 5. Primitivity and joint-support exponents on the standing corpus

Also oracle-only, computed in the same session over the 4,554 corpus:

| k | 1 | 2 | 3 | 4 | 5 |
| --- | --- | --- | --- | --- | --- |
| specimens with primitivity exponent γ(M) = k | 0 | 2,880 | 1,596 | 66 | 12 |
| specimens whose pairwise joint support first fills at k | 1,152 | 2,958 | 444 | 0 | 0 |

Wielandt's bound `γ ≤ (d−1)² + 1 = 5` is attained by 12 specimens, and
`max_a |σ^γ(a)| ≤ 42` across the corpus. Tribonacci (σ: 1→12, 2→13, 3→1) has
supp σ(2) ∪ supp σ(3) = {1,3}, γ = 3, and first joint saturation at k = 3.

Passing to σ^k preserves Ω_σ, pure discrete spectrum and "∃n" coincidence
conditions, but it does not remove the obstruction on this repository's
routes: a bad closed SCC for σ, sampled every k steps, is still a bad closed
recurrent structure for σ^k.

## 6. Follow-up tasks

1. Extend `mojo/psc/corpus.mojo` with a total-length bound so the 24,486 class
   becomes a canonical corpus, with the 4,554 corpus as a regression slice.
2. Run the existing swap-overlap census over that class. The result is
   finite-domain evidence on the larger class; it does not reconstruct the
   lost 2-step criterion and does not close any level.
3. Optionally, a bounded BPA build on the 14,670 max-image ≤ 4 slice, as
   evidence about the recorded Level-2 item only.

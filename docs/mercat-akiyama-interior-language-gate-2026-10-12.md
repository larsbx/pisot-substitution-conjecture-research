# Mercat–Akiyama interior-language criterion: PSC transfer gate (2026-10-12)

**Status:** targeted literature stop/go; no new theorem or computational certificate. General PSC, OP_seed (#84), aligned #138 and strict-zipper #139 remain **open**. Primary source: P. Mercat and S. Akiyama, *Yet another characterization of the Pisot substitution conjecture*, arXiv:1810.03500v1 (2018), https://arxiv.org/html/1810.03500v1. Read §§3, 5–7 directly. This note is not a claim-ledger promotion.

## Exact imported statements and boundary

- **Theorem 3.3:** for an **irreducible Pisot unit** substitution `s` and a periodic point `u`, its symbolic subshift has pure discrete spectrum iff **there exists a letter** `a` with nonempty interior of `D_{u,a}` in the authors' specially defined topology on the discrete line. Do not replace "exists a" with a claim about a specified letter without using the additional primitivity argument (Lemma 3.4).
- **Theorem 5.12:** given a regular language `L` over an alphabet in `Z^A` and an **irreducible Pisot unimodular matrix** `M`, the language representing the interior of the projected numeration set is regular and effectively computable. **Corollary 5.14**, rather than Theorem 5.12 alone, identifies nonemptiness of an appropriate interior language with symbolic PDS for an irreducible Pisot **unit substitution**, with a suitable fixed point.
- **Theorem 5.21:** the representation-equality language for finite alphabets and an integral matrix with **no eigenvalue of modulus one** is regular. This is a more general zero-automaton ingredient; it does **not** remove the unit/unimodular assumption from the interior-PDS characterization or its effective construction.
- **Conjectures 5.15, 5.17, 5.18:** conjectures, **not** theorems. Do not import their all-letter or natural-alphabet claims as established.
- The paper's topology/interior is not the usual interior of a prefix point set in ordinary Euclidean space; its topology is constructed from a projection along the expanding eigenline and the discrete-line address set.

## Known-positive families and exact algebra controls

Use alphabet order `(a,b,c)` and columns recording letter counts. The families are:

1. `A_k: a -> a^k b c, b -> c, c -> a` (paper §6.1, `k >= 0` where the Pisot-unit hypotheses apply):
   `M_A = [[k,0,1],[1,0,0],[1,1,0]]`, `det=+1`, `chi_A(x)=x^3-k x^2-x-1`.
2. `B_{k,l}: a -> a^l b a^(k-l), b -> c, c -> a` (§6.2, `k>=1, 0<=l<=k`):
   `M_B = [[k,0,1],[1,0,0],[0,1,0]]`, `det=+1`, `chi_B(x)=x^3-k x^2-1`.
   **The incidence matrix is independent of l**. Thus varying l is an order-sensitive positive control for occurrence-labelled overlap/Parikh machinery, not a distinguishable matrix-spectrum test.

The article also supplies a positive S-adic family (§7) with `a->aab` and `a->aba`, both having `b->c,c->a`: arbitrary infinite directive words over these two maps are covered by its S-adic argument. The S-adic repository owns cross-programme adoption; no periodic-point inference should be substituted for the everywhere-directive theorem.

**Negative controls:** `|det M|>1` examples must be marked **out of scope** of Theorems 3.3/5.12/Cor. 5.14; a zero automaton satisfying Theorem 5.21 is insufficient to claim non-unit PDS. Also a bounded/unfinished language search is `inconclusive`, not an empty-language proof. Productive exact overlaps are not automatically a certified interior-language witness absent an explicit translation theorem.

## Comparison to current PSC proof architecture

- **Existing:** `docs/pds-certificate-from-the-box-automaton-2026-10-07.md` (Theorem Omega) establishes an exact finite box criterion for **formal overlap productivity** and a per-specimen PDS sufficiency route using published overlap coincidence and Meyer imports, with human review pending under PR #235.
- **Open:** `OP_seed` / #84, split into aligned #138 and strict-zipper #139. Our strict-zipper target is `exists m: M^m w in P_m(i)-P_m(j)`; the source's zero/interior languages concern projected prefix addresses. Similar digit recurrences alone do not identify their states or acceptance conditions.
- **Different scope:** Mercat–Akiyama's unit case is established prior art, while the canonical PSC repository deliberately includes non-units. An extension to non-units would require full representation-space treatment (Archimedean **and finite places**, per `docs/p1b-strict-zipper-literature-gate-2026-09-21.md`) or an explicit proof omitted factors do not matter.
- **Novelty firewall:** do not claim finite automata deciding unit-Pisot PDS, the two infinite families, or the S-adic positive example as new.

## Decision — redirect, proceed narrowly

1. **Literature transfer only now:** register the imported statements and their exact scope in this note; do **not** change generated claim ledgers for an unimplemented comparator.
2. **Fixture contract next:** a Mojo-first independent *unit-only* comparator on small `A_k` and `B_{k,l}` examples, reusing vendored `finite_automata` and `psc` prefix/overlap code, not a new graph engine. Check the exact incidence polynomials/determinants, order sensitivity for fixed `k`, completed-language nonemptiness and separately the existing Theorem Omega verdict. Require deterministic witness language or complete emptiness certificate, with cap/error `inconclusive`. Include a non-unit rejection fixture and a bounded-search negative control. This is a separate PR: no executable comparison or cross-validation is claimed here.
3. **#139 bridge obligation:** give an occurrence-preserving map from each recurrent strict-zipper path to the correct prefix-address/zero-language state, and prove *both* relevant directions of the acceptance relationship in the **unit** case first. Candidate claim `bad closed SCC => empty appropriate interior language` remains **conjectural**; it cannot be inferred just from PDS equivalence or by assuming PDS.
4. **Non-unit extension is a separate open theorem:** construct/justify an adelic interior/coverage analogue before applying to `|det M|>1`. No formal-language computation over a Euclidean projection alone is a universal #139 proof.

**Exit gate:** an explicit state-to-state relation with checked hypotheses and a fully replayable unit calibration, or a counterexample that refutes the proposed correspondence. Until then: documentation/prior-art only; no status promotion, no generalized PSC claim.

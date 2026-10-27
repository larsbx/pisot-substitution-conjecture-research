# Audit and salvage: PSC v5 / residual-graph discussion (2026-10-23)

**Status:** documentation-only adversarial audit; **no theorem promotion**.  
**Source of authority:** `docs/claim-status-and-source-map-2026-09-13.md`, `docs/manuscript-p0-corrections-2026-09-11.md`, `README.md`, and issues #84, #44 and #151. The conversation's proposed v5.x files are not a substitute for the current accepted theorem/source ledger. The historical v4 branch is retired for this discussion.

## Summary decision

**Salvage:** unique decodability (UD) is a genuine general theorem, but the repository already derives it from full incidence rank by the classical *defect theorem*, for `sigma` and all powers. Keep that short proof and the finite-census SP runs as regressions. The finite overlap/loop-gain evidence and the Plastic-A worked-example observations are useful for scoped algorithmic research.

**Reject:** the thread's new SP/integral-residual proof of UD, its conclusion `UD => finite BPA`, and the claim that it closes the general PSC. There are precise mathematical counterexamples and an already-recorded withdrawal of the older v5 predecessor-contraction estimate.

## A. Valid theorem to retain: UD via full incidence rank

Let `|A|=d` and `C={sigma(a):a in A}`. If `det M_sigma != 0`, no two images coincide. Suppose `C` is not a code. The defect theorem produces at most `d-1` nonempty words `t_1,...,t_r` such that all `d` image words factor over the `t_j`. Their Parikh vectors give a factorization

```text
M_sigma = P * N,       P in Z^(d x r), N in Z^(r x d), r <= d-1.
```

Consequently `rank(M_sigma) <= r < d`, contrary to `det M_sigma != 0`. Hence `C` is uniquely decipherable; likewise all powers because `det M_(sigma^n)=(det M_sigma)^n != 0`.

This is already in the **live** manuscript/source map (UD and powers, manuscript Theorem 2.8). Do **not** reintroduce UD as an open conjecture or an additional standing hypothesis. Literature: classical defect theorem, e.g. Karhumäki et al., *Many aspects of defect theorems*, TCS 324 (2004), 35–54.

## B. Exact PIP counterexample to the thread's central residual-edge lemma

On alphabet `{0,1,2}`, set

```text
sigma(0) = 12
sigma(1) = 01
sigma(2) = 120
M_sigma = [ [0,1,1],
            [1,1,1],
            [1,0,1] ]
det(M_sigma) = -1
chi_M(x) = x^3 - 2*x^2 - x + 1.
```

The characteristic polynomial is irreducible over Q. Its roots (diagnostic approximations only) are `2.2469796037`, `0.5549581321`, and `-0.8019377358`, so the PF root is Pisot. `M_sigma^3 = [[3,3,5],[5,4,7],[3,2,4]] > 0`: sigma is primitive. Thus this is an actual **primitive irreducible Pisot** example, not an out-of-scope synthetic morphism.

There is an **initial reachable SP residual** `u=0` because
```text
sigma(2) = sigma(0) · 0          (120 = 12 · 0).
```
There is then a **same-orientation equal-length, non-identity edge** `u=0 -> v=2`:
```text
u · sigma(0) = sigma(1) · v      (0 · 12 = 01 · 2 = 012)
|u|=|v|=1,   u != v,            source letters 0 != 1.
```
The integral defect decoration holds exactly:
```text
M^-1 Parikh(0) = (-1, 0, 1)
M^-1 Parikh(2) = ( 0,-1, 1)
Delta_v - Delta_u = e_0 - e_1.
```

Therefore the proposed lemma “every equal-length preserved-orientation SP edge is an identity / same-letter edge” is **false even within the PIP class**, including reachable integral residual states. The proof error is the inference that `u sigma(a)=sigma(b) v` and `|u|=|v|` make `sigma(a)` and `sigma(b)` conjugate: they do not.

Retain this as an exact negative-control fixture. It **does not** refute UD (which is true by the defect theorem). Do not use the purported `G_m` proof of UD.

## C. Other invalid reductions in the thread

1. **Empty-to-empty SP return need not contain a nonempty-state cycle.** A path `epsilon -> u -> epsilon` has no cycle in the subgraph on nonempty residuals. The route from non-UD to an *internal* recurrent SCC requires an additional theorem and is not supplied by ordinary SP.
2. **A minimum-length vertex on a cycle does not give an equal-length subcycle.** The directed cycle with lengths `1 -> 2 -> 1` is a complete counterexample to that graph argument. Choosing a minimum merely bounds the other vertices below; it does not force equal lengths.
3. **Contraction to a centered-embedding graph is not justified.** Even if `G_m` is acyclic by strict growth of `|sigma(a)|`, successive SP flips do not automatically compose as a closed walk of source letters in one `G_m`. No such closure map was proved.
4. **UD is not recognizability of bi-infinite shifted cutting.** As a pure code-theoretic illustration, `{01,12,20}` is an equal-length UD code with nonsingular Parikh matrix (determinant 2), yet the bi-infinite periodic word `(012)^infty` admits distinct codeword boundary phases. One needs an additional language/recognizability argument; finite-word UD alone does not fix shifted infinite cut positions.
5. **Rauzy-bigram legality is not legal iteration.** A walk using allowed adjacent pairs need not be a legal word of a substitution subshift, still less imply all powers `W^n` are legal. In a minimal aperiodic subshift, if `W^n` were legal for all `n` for a fixed nonempty `W`, compactness would give the periodic point `W^infty`, contradicting aperiodicity. A claimed “cycle => legal `W^n` for every `n`” must prove its realization/concatenability rather than infer it from finite Rauzy compatibility.
6. **Level-3 witness preservation as drafted has a boundary gap.** `diameter(supertile) > |delta|` does not guarantee that `x` and `x+delta` lie in the same supertile (take `x` within `|delta|` of an edge). The claimed collapse/injectivity of the finite witness also requires a precise realization/ancestry theorem. Do not cite these short conversational sketches as a checked general Level-3 proof.
7. **The one-bit Plastic witness argument was logically redundant.** Assuming an injective witness already preserved by every recurrent displacement gives the contradiction directly; appending an active-support bit cannot be the load-bearing reason.

## D. Existing repository rejection of the older finiteness shortcut

The live source ledger explicitly withdrew `PSC_PROOF_v5` Theorem 5.1's predecessor bound `beta L(s') <= L(s)+D`: the estimate fails on verified examples (worst recorded ratio 8.0, unbounded excess). See `archive/2026-09-08/notes_2026_06/V5_THM51_RETRACTION_VERIFICATION_2026_06_13.md`, `docs/archive-tarball-audit-2026-09-13.md`, and `docs/manuscript-p0-corrections-2026-09-11.md` §12. The valid live chain is

```text
det(M) != 0 -> UD [PROVED via defect theorem]
Pisot setup -> bounded discrepancy G1b-1 [PROVED]
G1b-1 + realizable renewal/discreteness G1b-2 [OPEN] -> finite BPA G1 [OPEN].
```

The shortest current PDS route **does not require** G1: one swap-seed overlap productivity `OP_seed` is the open premise in issue #84 / manuscript Theorem 5.38. Never substitute a finite automaton experiment or predecessor contraction for this universal obligation.

## E. Useful scoped empirical/structural work

Conversation reports (not independently replayed here): SP/UD 2,622/2,622; zero off-diagonal *legal-phase* recurrent SCCs in 3,436+ tested specimens; 2,286 ternary specimens with transient zero-defect ambiguity (maximum persistence 2); 18 unreachable residual size-two SCCs; Plastic-A FM-active sector and exact span law. These are excellent **test inputs, negative controls, and certificate compression heuristics**, but require raw specimen IDs, exact builders, complete reachability definition, cap semantics, and reproducible receipts before project acceptance. In particular, unrestricted vs legal phase graphs and reachable vs unreachable residual SCCs must be distinct fields.

Useful Plastic-A outputs remain the exact canonical-chain span `beta^(k+3)` (verify normalizations/strict thresholds), FM/diagonal active-carrier maps, and potential witness/certificate compression. None supplies G1, `OP_seed`, or Level-3 witness preservation.

## F. Next actions (no new general-proof claim)

**P0 — proof hygiene:** keep the defect-theorem UD proof as the single canonical UD supplier; link this regression and explicitly quarantine the failed residual-acyclicity, equal-length, and predecessor-contraction shortcuts. Do not reopen a “prove UD” task.

**P1 — #84 (primary PSC route):** work on the single-seed productive-overlap gate using the live exact occurrence-labelled overlap graph and closed nonproductive SCC normal form. Preserve order, offset, realization, and non-unimodular hypotheses. Do not require seed `ab` to be substitution-language legal.

**P2 — #44 (parallel G1):** prove G1b-2 realizable renewal finiteness, not “bounded discrepancy => bounded balanced-pair length”. Use the exact labelled-return encodings; preserve non-Archimedean components when non-unimodular.

**P3 — #151 (Tier 2):** salvage the Plastic-A active-sector and periodic-loop observations as *diagnostics for the existing loop-gain Growth Bridge*, with exact fixtures and no PSC-completion promotion.

**Regression request:** add a Mojo-first exact negative control for the substitution above to a non-vendored PSC kernel/test location. Assert PIP/invertibility, initial residual reachability, equal-length same-orientation nonidentity transition, UD (by independent SP oracle), and the absence of any inference from this transition to a non-UD return. Also test a `1 -> 2 -> 1` residual-length cycle as a negative control for “minimum implies equal length.” Use Python/SymPy only as independent verification, not sole canonical executor.

**Status:** the present audit adds a falsifying fixture and eliminates duplicate/incorrect proof obligations. It does **not** prove or disprove PSC, G1b-2, or `OP_seed`. Independent referee-level validation remains separate from compile success and passing finite tests.

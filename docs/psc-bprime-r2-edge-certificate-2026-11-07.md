# R2C — finite-state oriented coboundary certification (2026-11-07)

**Parent:** R2 PR #508 exact accepted Lean/Quint head `3f87bdbba7489070e6951e55b478fca678e140a2`; this draft's target base is the independent R2 research branch, not `main`. **Classification:** scoped proof-interface and adversarial control only; C4, A1′, BH, PDS and PSC stay open.

## Work shown

### Assumptions and hypotheses

A **supplied finite occurrence-indexed directed graph** is represented by vertices `Fin n` and edges with a literal source, target, rational score, and separately verified source occurrence address. A candidate state potential `H : Fin n → ℚ` is a certificate when every supplied edge score `w(e)` satisfies `H(target(e)) − H(source(e)) = w(e)`. The Lean checker proves this exact condition for the *supplied list*, not completeness of the graph relative to a substitution.

The parent R2 branch already proves that B′ ordinary averages cannot be transported to an arbitrary deck-even oriented score: `(+1,-1)` has signed average 0 while both deck-adjusted contributions are positive. The correct bridge must supply a source-linear score plus an exact finite-state coboundary.

### Derivation / reduction

Define a typed `WeightedEdge` with finite source and target, rational signed weight; define a decidable Boolean potential verifier using `decide` on the complete supplied edge list; prove `true ⇒ ∀ supplied e, weight(e)=H(dst)-H(src)` in Lean without a `sorry`. A two-edge cycle `0→1` of weight 1 and `1→0` of weight 0 has nonzero total weight and therefore **no** rational potential; this is a kernel-level counterexample to a false blanket existence theorem. It is *not* an actual strict-PIP occurrence graph.

The parent Lean `coboundary_telescoping` theorem already proves potential differences telescope on paths; the new work supplies a finite-certificate **input boundary**, rather than reproducing the same theorem.

### Evidence and replay

- Lean: `proof/psc_routes/R2EdgeCertificate.lean`; typecheck against the repository-pinned Lean/Mathlib under `proof/PscVerif`; all new theorems audited for only the three allowed Lean axioms.
- Quint: `proof/quint/PscR2EdgeCertificate.qnt`; deterministic positive-cycle test explicitly verifies that the loop closes with accrued score 1; this model is finite and not a source-refined proof.
- Hosted CI: `.github/workflows/psc-bprime-r2-edge.yml`, exact-head checkout, nonzero named-test checks and exact Lean axiom receipt count.

### Negative controls

A signed orientation switch may reverse a linear displacement. Normalized, unordered states cannot be substituted for actual oriented edges. A zero ordinary sum does not imply zero orientation-indexed sum. A positive weighted closed directed loop makes an exact potential impossible. Conversely, a potential certificate over an **incomplete** observed edge set does not establish a potential over every occurrence or arbitrary substitution depth.

### Non-claims / remaining gaps

**Required next reproducible obligation:** extract the actual all-edge ordered descendant graph from canonical Mojo occurrence source, retaining multiplicity, source letter, both offsets, raw orientation and target labels. Independently reconstruct every edge weight. Then construct or reject a rational potential certificate, with a complete-edge-set digest and independently checked no-omission proof. Graph extraction and global-coverage proof are NOT implemented here.

No novelty claim for the elementary potential/cycle-sum criterion. No human mathematical review prior to PSC closure. The targeted automated research-design literature check is below.

### Targeted literature stop/go

- Sirvent–Solomyak (2002), *Pure Discrete Spectrum for One-dimensional Substitution Systems of Pisot Type*, DOI 10.4153/CMB-2002-062-3, §§3–5: distinguishes prefix-seeded BPA return gaps and overlap half-coincidences; does not supply our ordered strict graph or a corresponding signed potential.
- Martensen (2004), *A Generalized Balanced Pair Algorithm*, arXiv math/0309194, uses ordered reductions and coarser generalized balance; its termination conclusions do not imply every proposed oriented graph has a potential.
- The repository's `docs/c4-orientation-monodromy.md` already models `ℤ/2` deck signs and the ordered double cover; `docs/c4-ordered-hub-literature-gate-2026-10-06.md` compares exact occurrence versus normalized-state semantics.
- Parent R2's literature stop/go and adverse deck-average counterexample are inherited by exact revision, not reasserted as novelty.

**Decision: PROCEED NARROWED** with a machine-checked rational edge-certificate interface. Do not infer that the certificate exists in any strict PIP component; deliberately search for positive cycle-sum obstructions before proposing a universal R2 closure.

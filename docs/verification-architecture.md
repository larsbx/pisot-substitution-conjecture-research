# Verification architecture

The repository uses several complementary verification layers. No layer is allowed to claim more than it actually checks.

## 0. Canonical executable language

**Mojo is the canonical executable implementation layer.** New algorithms, exact finite-state machinery, census drivers, and performance-sensitive theorem-support code should be implemented in `mojo/` first. Python is retained as an independent reference/oracle and prototyping layer, not as the default implementation surface.

This is also an optimization policy: hot kernels should be redesigned around Mojo's strengths rather than mechanically translated from Python. In the standing alphabet-3 regime, prefer fixed-dimension exact arithmetic, streaming prefix accumulators, precomputed substitution-local tables, compact integer-index graph representations, iterative traversals, and storage reuse. Diagnostic string serialization and Python-style dynamic object graphs should stay out of inner loops where an exact compact representation is available.

The detailed agent/review rules are in `AGENTS.md`.

| Layer | Tool | Question it answers | Scope |
|---|---|---|---|
| **Canonical exact implementation** | Mojo | Is the executable finite arithmetic/automaton computation correct? | exact PIP decision, BPA construction, structural C4 machinery, C3/C4/defect censuses, finite algebra, optimized corpus instrumentation |
| Secondary structural oracle | Python | Does an independently written reference reproduce structural identities/counter-calibrations? | reference SCC/endpoint/orientation/defect/factorization/lattice models during Mojo migration |
| State/dependency model | TLA+ / TLC | Does the finite automaton/model behave as claimed, and which proof conclusions are reachable from which assumptions? | BPA model checks and proof-dependency ledger |
| Deductive finite algebra | Lean 4 + Mathlib | Do the formalized finite-algebra theorems follow? | seed/spectral algebra and axiom audit |

Run the available layers with `scripts/verify_all.sh`. A missing toolchain must be reported as skipped, never converted into a vacuous pass.

## 1. What is proved versus computed

The exact 4,554-substitution corpus is a **finite calibration**, not a proof of G1, C1, C4, or PSC. Mojo verifies that the chosen finite parameter space was screened exactly and that the reported BPA/census statistics are reproducible.

Executable identities in Mojo or Python are still regression/certificate computations, not proof-assistant theorems merely because they are exact. The architectural preference for Mojo changes the source-of-truth implementation, not the epistemic status of computation.

Lean currently formalizes the older finite spectral core, not the full C4 stack. TLA+ checks dependency reachability and selected finite-state models; it does not prove the mathematical C4 lemmas merely by naming them in a ledger.

## 2. Mojo kernel and optimization policy

The Mojo kernel uses exact integer/rational operations for:

- incidence and characteristic-polynomial arithmetic;
- primitive / irreducible / Pisot screening;
- balanced-pair factorization and SCC construction;
- seed `K2/K3/W3` certificate computations;
- endpoint/C3/C4 finite censuses;
- the exact first-defect census;
- new C4 structural machinery as it is migrated from the Python oracle layer.

For new work, the preferred optimization order is:

1. exploit known fixed dimensions before introducing generic containers;
2. replace combinatorial enumeration with exact streaming recurrences when possible;
3. precompute data depending only on a substitution/specimen;
4. intern states once and use integer indices in graph algorithms;
5. reuse scratch storage and avoid temporary strings/lists in hot loops;
6. keep SCC/reachability algorithms iterative;
7. fuse repeated exact passes only when doing so preserves auditability;
8. fail closed on impossible invariants;
9. never trade exact arithmetic for floating heuristics on proof-relevant predicates;
10. accompany material hot-kernel changes with deterministic correctness regressions and complexity/benchmark notes where practical.

The `N2/N3` word counters are a canonical example: in a three-letter alphabet they should use one-pass prefix accumulators rather than `O(n^2)` / `O(n^3)` tuple enumeration.

The established finite alphabet-3 corpus has 4,554 PIP substitutions with image lengths `<=3`. All BPA constructions terminate below the configured cap in this corpus; every observed sink is productive. This is finite evidence only.

Issue #2 tracks the remaining infrastructure step: make this exact screen the canonical documented corpus-export interface with deterministic machine-readable JSONL.

## 3. Python reference/oracle layer

`src/psc_research/` and `tests/` contain exact reference implementations for much of the live C4 reduction stack, including:

- sink-SCC and boundary-lineage tooling;
- seven endpoint-map types and synchronization quotients;
- Parikh/child-incidence intertwiners;
- orientation cocycle, even/odd incidence, and spectral phase cases;
- signed `K2/K3` first-defect intertwiners;
- degree-4 and generalized-Witt multidegree sieves;
- mod-2 degree-2 size obstruction;
- synthetic G/F factorization negative control;
- ordered degree-2 mid-area identity;
- three-state mean-area and integral-image calibration;
- recent recognizability/prefix-ancestry prototypes while their Mojo ports are being completed.

These files remain valuable because an independently written oracle can catch mistakes in the canonical Mojo path. They should not become the default location for new theorem-support code. A Python-only new module is temporary unless an explicit blocker makes a Mojo implementation impractical.

The strong G/F synthetic artifact is important precisely because it prevents overclaiming: it satisfies the real PIP substitution, endpoint phases, incidence, Parikh and `K2` data, and actual irreducible state columns, yet fails the true zero-return child factorization.

## 4. TLA+ proof-dependency layer

`ProofArchitecture.tla` is a generic dependency state machine. A result can be discharged only when all prerequisites are already established; withdrawn results can never be discharged. `Ledger.tla` supplies the current mathematical dependency graph.

The dependency graph must encode **sufficiency**, not converse implications. In particular the current route is

```text
C4 => C3-local => C2 => SCCProducer,
G1 + SCCProducer => PDS.
```

G1 is used to extract a finite sink SCC from global nonproductivity. Structural statements conditional on an already-given finite closed SCC should not all be made to depend on G1 in the ledger.

The literature relation between PDS and standard BPA termination is tracked separately. Until the repository's normalized all-seed graph is explicitly bridged to the literature algorithm, the ledger must not silently add `PDS => G1`.

## 5. Lean layer

The Lean development proves the formalized finite spectral algebra and audits axioms. It does **not** currently formalize:

- G1 or SCC Producer;
- sink-SCC extraction;
- endpoint synchronization quotients;
- the general first-defect free-Lie statement;
- C4's prefix-difference/recognizability route;
- the ordered mid-area or mean-area lattice identities.

Those omissions should remain visible rather than being implied away by passing computational tests.

## 6. Source/interface discrepancies

Four discrepancies are now canonical.

### D1 — printed shuffle map is transposed

The archived certificate's displayed basis-action form of the shuffle map is transposed relative to the coordinate map used by the rest of the certificate. The coordinate convention is the one implemented in Mojo and Lean and is the one under which the printed basis and seed `K3` vectors lie in the intended kernel.

### D2 — the degree-3 shuffle argument needs lower-degree corrections

The naive degree-3 shuffle identity is false on diagonal indices because scattered-subword multiplication is the infiltration product, not pure shuffle. The correction terms have degree two and cancel when `K2=0`; the intended conclusion remains valid. Lean proves the corrected instance used by the seed calculation.

### D3 — archived v34 status table still contradicts the withdrawal

The archived `V34_CLOSURE.md` contains stale prose saying alphabet-3 finiteness was proved by the withdrawn v5 theorem and that the Load-Bearing SCC theorem was unconditional. The live ledger is authoritative instead; the archived file remains preserved as historical source.

### D4 — archived normalized SCC transfer omits orientation signs

The archived `PROOF_CERTIFICATE.md` degree-3 SCC interface uses

```text
L_C N_C = Phi_3 L_C.
```

For normalized balanced-pair states this is not correct in general: when a raw child appears reversed relative to its normalized representative, the odd scattered-subword defect changes sign. The exact normalized relation is

```text
Q_3 S = Phi_3 Q_3,
S=A-B,
```

and similarly `Q2 S=(Lambda^2 M)Q2` at degree two.

This correction does **not** invalidate the seed-level finite Spectral Black Box. It corrects the SCC-level transfer interface. The older v34 norm/path-counting argument that takes norms before using unsigned counts is a separate statement and is not changed merely by D4.

## 7. Current verification and implementation gap

The deepest current mathematical gap remains a uniform theorem about actual factorization and recognizability:

- the prefix-difference walk determines balanced child return times;
- finite closed SCC recurrence produces many bounded-gap returns under inflation;
- Pisot contraction constrains multi-level ancestry defects;
- recognizability constrains recurrent child cuts relative to supertile boundaries;
- the remaining object is the relative hierarchy-offset/address state.

The implementation gap is now explicit too: recent Python structural prototypes on this route must be migrated into canonical Mojo modules, beginning with multi-level prefix ancestry/legal towers and the relative hierarchy-offset state. New work on this path should be Mojo-first.

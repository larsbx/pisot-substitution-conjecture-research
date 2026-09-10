# Verification architecture

The repository uses several complementary verification layers. No layer is allowed to claim more than it actually checks.

| Layer | Tool | Question it answers | Scope |
|---|---|---|---|
| Exact computational kernel | Mojo | Is the finite arithmetic/corpus computation correct? | exact PIP decision, BPA construction, C3/C4/defect censuses, finite algebra |
| Structural regression layer | Python | Do exact structural identities and counter-calibrations behave as claimed? | SCC, endpoint, orientation, defect, ordered factorization, mean-area/lattice prototypes |
| State/dependency model | TLA+ / TLC | Does the finite automaton/model behave as claimed, and which proof conclusions are reachable from which assumptions? | BPA model checks and proof-dependency ledger |
| Deductive finite algebra | Lean 4 + Mathlib | Do the formalized finite-algebra theorems follow? | seed/spectral algebra and axiom audit |

Run the available layers with `scripts/verify_all.sh`. A missing toolchain must be reported as skipped, never converted into a vacuous pass.

## 1. What is proved versus computed

The exact 4,554-substitution corpus is a **finite calibration**, not a proof of G1, C1, C4, or PSC. Mojo verifies that the chosen finite parameter space was screened exactly and that the reported BPA/census statistics are reproducible.

The Python layer contains theorem-level integer identities where the proof is elementary and explicit—for example the endpoint quotient, Parikh/orientation intertwiners, ordered mid-area identity, and exact lattice certificates—but Python execution is still a regression check, not a formal proof assistant.

Lean currently formalizes the older finite spectral core, not the full C4 stack. TLA+ checks dependency reachability and selected finite-state models; it does not prove the mathematical C4 lemmas merely by naming them in a ledger.

## 2. Mojo kernel

The Mojo kernel uses exact integer/rational operations for:

- incidence and characteristic-polynomial arithmetic;
- primitive / irreducible / Pisot screening;
- balanced-pair factorization and SCC construction;
- seed `K2/K3/W3` certificate computations;
- endpoint/C3/C4 finite censuses;
- the exact first-defect census.

The established finite alphabet-3 corpus has 4,554 PIP substitutions with image lengths `<=3`. All BPA constructions terminate below the configured cap in this corpus; every observed sink is productive. This is finite evidence only.

Issue #2 tracks the remaining infrastructure step: make this exact screen the canonical documented corpus-export interface with deterministic machine-readable JSONL.

## 3. Python structural layer

`src/psc_research/` and `tests/` now carry exact regression implementations for the live C4 reduction stack, including:

- sink-SCC and boundary-lineage tooling;
- seven endpoint-map types and synchronization quotients;
- Parikh/child-incidence intertwiners;
- orientation cocycle, even/odd incidence, and spectral phase cases;
- signed `K2/K3` first-defect intertwiners;
- degree-4 and generalized-Witt multidegree sieves;
- mod-2 degree-2 size obstruction;
- synthetic G/F factorization negative control;
- ordered degree-2 mid-area identity;
- three-state mean-area and integral-image calibration.

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

## 7. Current verification gap

The machine/prose record is being updated to include the C4 stack, but the deepest current mathematical gap is not a missing test. It is a uniform theorem about actual factorization:

- the prefix-difference walk determines balanced child return times;
- finite closed SCC recurrence produces many bounded-gap returns under inflation;
- Pisot contraction should constrain those return vectors;
- recognizability should constrain recurrent child cuts relative to supertile boundaries.

That alignment/return-density step is the next proof target. No amount of additional fixed-size regression filtering is a substitute for it.

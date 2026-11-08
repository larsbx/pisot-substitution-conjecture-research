# R1F ordered ancestry replay

## Work shown

### Assumptions and hypotheses

Use literal Tribonacci images 01, 02, 0 and the ordered legal seed (01,10). Enumerate ancestry of every interior aligned equal-Parikh cut through the requested depth. Addresses use the unique source letter occurrence whose nonempty image contains the position immediately to the right of the cut.

### Derivation / reduction

At each step independently count the signed top-minus-bottom source prefixes and the signed proper prefixes inside the two source images. Their incidence transport is the next defect. Record a candidate loop only when both ordered right-hand letters and the entire nonzero defect agree at the two levels of a single path. For chronological digits, fold the forced sum by b ← M b + c and the matrix power by P ← MP, starting with 0 and I. The resulting equation is (I−P)x = b.

### Targeted literature stop/go

Sirvent–Solomyak (2002), §§3–5, distinguishes the BPA cut and overlap domains. Martensen (2004), §3, separates generalized balance from ordinary Parikh balance. The Dumont–Thomas prefix-suffix graph (§2.6 in *Geometry, dynamics, and arithmetic of S-adic shifts*) supplies the local digit perspective, whereas the paired occurrence and zero-return constraint comes from the literal tracks. Proceed on the fixed seed and preserve the separation between local admissibility, occurrence, and strict nonproductivity.

### Evidence and replay

| Depth | Interior equal-Parikh cuts | Nonzero repeated decorated segments |
| --- | ---: | ---: |
| 1 | 1 | 0 |
| 2 | 3 | 0 |
| 3 | 9 | 0 |
| 4 | 18 | 0 |
| 5 | 35 | 0 |
| 6 | 71 | 9 |

The cut at 51 in depth six gives the repeated segment at levels 0 through 3 with defects `(1,−1,0) → (0,1,−1) → (−1,0,1) → (1,−1,0)` and digits `(0,−e₀,+e₀)`. The ordered right-hand letters are `(1,0)` at both endpoints. The integer rows are `A=[[-3,-3,-2],[-2,-1,-1],[-1,-1,0]]` and `b=[0,-1,0]`. Lean derives the incidence from the source images and checks the exact transforms and inverse laws for `UAV=diag(1,1,2)` against the existing Smith iff. The actual segment passes divisibility. The independent Quint model checks the literal cut, source addresses, digit transport and matrix basis.

Run `cd kernel && pixi run --locked mojo run -I . tests/test_ordered_ancestry_cycles.mojo`. The exact-head workflow compiles both Lean modules, compares every serialized row with the independent Lean enumerator, and runs `npx --yes @informalsystems/quint@0.33.1 test --backend=typescript proof/quint/PscR1OrderedAncestry.qnt` from the repository root. The receipt includes both packet digests and the checked-out SHA. Lean uses kernel reduction and a scoped axiom audit.

The checked finite scan uses one seed, depths 1–6, word length at most 81 per track and at most 71 interior returns per depth. Both caps fit all examined words and cuts. Reducing either cap below the depth-six requirement yields explicit exhaustion. The public Mojo entry point also rejects depths outside 1–12 and raises on integer overflow.

### Negative controls

Wrong offsets and digit signs fail replay. The arithmetic cycle `e₀ → e₁ → e₂ → e₀` satisfies its integer equation but is absent from all nine repeated decorated segments in the finite scan. This finite absence leaves other seeds and larger depths open. The parent Smith `4x=2` guard remains separate from source validation.

### Non-claims / remaining gaps

A repeated decorated defect along a finite path is a realized ancestry segment. This control rules out a blanket exclusion of nonzero integral ancestry cycles on productive PIP data. Strict child closure or infinite repetition requires separate evidence. The branch supplies neither a strict PIP component nor a closure implication.

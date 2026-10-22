# Class A d=2: parity-stratified typed-carrier investigation (2026-10-22)

**Status: exact finite-domain evidence and an inferred parity-sensitive carrier proposal; no uniform theorem.** Independent human review pending. This note continues #139 after the class-A gap-one hitting theorem merged in PR #310 and the general two-sign algebra proposed in PR #311. Neither the successful gap-one carrier nor its descent is assumed to apply at d=2.

## Stop/go and target

Fix the next residual determinant-two Class-A line

```
sigma_n(x)=x y^(n+2) x
sigma_n(c)=c y^n x
sigma_n(y)=x y^(n+1) c,       n>=4.
```

The targeted literature/assumption gate remains the Akiyama–Lee, Minervino–Thuswaldner and Barge review in `docs/p1b-class-a-run-index-2026-10-21.md`, and the October 22 exact normal-form work. The d=1 89-row carrier has a **uniform non-overlap countermodel** on the d=2 line. An unchanged transplantation is mathematically false, so proceed by rebuilding typed seed-reachable states and recording actual ordered occurrences under the existing screened exact Perron overlap engine. Preserve all three swap pairs and the non-unit determinant hypothesis firewall. Do not claim that exact finite enumerations prove a uniform n theorem.

## Exact finite graph experiment

The canonical source `kernel/psc/class_a_d2_parity_carrier.mojo` builds the complete exact graph for a user-specified `4<=n<=32`, rejects an exhausted 20,000-state budget, inverts the existing Perron tile-length matrix to recover **integer** bottom-minus-top offset coordinates `w=(k,c,y)`, and lexicographically groups all graph vertices into maximal consecutive-k typed intervals. Each row is

`(top,bottom,s,y,k_lower,k_upper)`, `s=k+c+y`.

It also requires that **every complete graph vertex has an offset-zero descendant** at that exact n. Coincidences remain terminal. Each reported row is a genuine seed-reachable vertex set at the parameter where it was computed, not a formal superset and not a family theorem.

An independently implemented rational-field oracle in `oracles/python/class_a_d2_parity_carrier.py` builds its own complete overlap graph, solves the Q(beta)-coordinate matrix over `Fraction` for every vertex, and checks the entire ordered typed interval list, exact first-hit depth, and finite completion. This is separate from the Mojo graph implementation and does not replace its authority.

### Finite parameter observations

The independently evaluated exact rational-root enumeration motivating the candidate shows:

| n | vertices | maximal typed intervals | maximum first boundary-hit depth |
| ---: | ---: | ---: | ---: |
| 4 | 183 | 87 | 4 |
| 5 | 193 | 85 | 5 |
| 6 | 225 | 91 | 5 |
| 7 | 231 | 87 | 5 |
| 8 | 265 | 93 | 5 |
| 9 | 271 | 87 | 6 |
| 10 | 305 | 93 | 6 |
| 11 | 311 | 87 | 7 |
| 12 | 345 | 93 | 7 |
| 14 | 385 | 93 | 7 |
| 18 | 465 | 93 | 9 |
| 24 | 585 | 93 | 11 |

**These are finite observations; the new canonical locked CI must replay the specified parameters before the repository treats them as accepted evidence.** None is extrapolated to all n. The exact source rejects incomplete graph builds instead of inventing a no-counterexample verdict.

## A new parity-sensitive hypothesis

The d=2 exact graphs suggest that a single affine interval table indexed by n is **not the right symbolic coordinate system**. Introduce `m=floor(n/2)`, and infer separate typed tables.

- **Even n=2m, n>=8:** 93 maximal interval families across 82 typed slices, with proposed endpoints affine in m. A symbolic count of their lengths gives `40m+105=20n+105`.
- **Odd n=2m+1, n>=7:** 87 maximal interval families across 80 typed slices, with proposed endpoints affine in m. Their lengths sum to `40m+111=20n+91`.

The tables are *generated candidates* by comparing the full exact profiles at n=8 and 12 (even), and n=9 and 13 (odd), respectively. Endpoint differences must be exactly divisible by the two-unit m increment, and the ordered typed slice keys must agree. Otherwise inference refuses. No floating regression, arbitrary slope fit or silently interpolated missing group is allowed.

The current canonical verifier checks complete-graph **label equality** for further, independently constructed finite parameters, not merely the two source graphs. The accepted source-pair rule is part of the contract: an arbitrary pair or a cross-parity pair refuses. The exceptional n=4,5,6 profiles are handled as separate exact finite base cases: n=4/5 have different vertex counts, and n=6 has the expected even vertex count but merged/split interval endpoints, so it is not required to have the stable n>=8 profile shape.

A failed candidate on any subsequently checked n is a replayable countermodel to that parity hypothesis, not a failure of the underlying boundary-hitting conjecture.

## What is proved, and what is not

The finite evidence supports a **parity-indexed candidate for a uniform d=2 carrier**. To promote it, the next PR must prove for all integer m above the two respective floors that:

1. Every affine row remains nonempty, strictly real, pairwise disjoint within typed slices and contains every genuine canonical swap seed. Derive Perron signs from the **d=2** characteristic cubic, not the d=1 formula.
2. Every **actual ordered proper-prefix child** of every nonterminal candidate state belongs to the appropriate same-parity carrier. Include all FIRST/RUN/LAST index cases, edge margins, and the terminal-coincidence rule. A finite comparison cannot discharge this quantified condition.
3. A parameter-dependent nonnegative rank/potential strictly decreases on a realizable chosen child from every nonzero-offset state, or an independently justified closed-SCC eliminator supplies the corresponding hitting argument.

Only after all three can the selected d=2 line be promoted from finite evidence to a scoped all-n boundary-hitting theorem. The parity effect itself needs a source-checked explanation; a fitted cardinality formula is not a proof.

## Replay, negative controls and integration

Canonical files: `kernel/psc/class_a_d2_parity_carrier.mojo`, driver `kernel/class_a_d2_parity_carrier.mojo`, and `kernel/tests/test_class_a_d2_parity_carrier.mojo`. Independent oracle and tests: `oracles/python/class_a_d2_parity_carrier.py`, `tests/test_class_a_d2_parity_carrier.py`. The dedicated locked workflow retains graph exports and independent calibration receipts.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_parity_carrier.mojo
pixi run --locked mojo run -I . class_a_d2_parity_carrier.mojo
pixi run --locked mojo run -I . class_a_d2_parity_carrier.mojo export 8 > build/d2-n8.log
pixi run --locked mojo run -I . class_a_d2_parity_carrier.mojo export 9 > build/d2-n9.log
cd ..
python oracles/python/class_a_d2_parity_carrier.py kernel/build/d2-n8.log
python oracles/python/class_a_d2_parity_carrier.py kernel/build/d2-n9.log
python -m pytest -q tests/test_class_a_d2_parity_carrier.py
```

Refusal controls include unsupported/cross-parity source pairs, a tampered affine endpoint, finite parameter outside the stated budget, a capped or incomplete exact graph, invalid integer-coordinate reconstruction, a missing/duplicate typed interval, and a misleading summary status. The previous d=1 non-transfer counterexample remains intact.

**Nonclaims:** This work does not prove all-n d=2 boundary hitting, general class A/C, non-unit tiling realization, #139, #138, #84, G1 or PSC. It does not promote any claim-governance or proof-ledger status. Independent human review remains pending. Fresh CI on the exact PR head remains required for integration.

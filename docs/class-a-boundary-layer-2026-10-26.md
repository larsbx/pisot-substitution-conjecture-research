# PSC research continuation: an exact boundary-layer obstruction in the class-A strip

**Snapshot:** 2026-10-26, repository `larsbx/pisot-substitution-conjecture-research`, `main@4eb0427d440e4c2cfe28ce7de934061f1c9bf3ad` (2026-10-24 10:47 UTC). **Work status:** independent local algebraic derivation and Python exact-arithmetic experiment; no repository changes, PR, hosted CI, or independent human review. **Claim status:** no change to BH, A1′, C4, G1 or PSC.

**Existing work used:** `docs/class-a-gap-theorem-2026-10-23.md` (PR #335, arithmetic repair PR #340), `docs/class-a-gap-uniformity-stopgo-2026-10-23.md`, `docs/direct-attack-frontier-2026-10-23.md`, and issue #139. In particular, #335 already proves BH for all class-A members with `n>=5d`. This note isolates a new failure mode for simply transferring its uniform `(h,u)` box to `n<5d`.

## 1. Exact statement (new candidate lemma, not repository-governed)

For `epsilon in {-1, +1}`, consider the class-A substitution in alphabet `(x,c,y)`:

    sigma(x) = x y^(n+d) x
    sigma(c) = c y^n x
    sigma(y) = x y^(n+epsilon) c.

For every **fixed** nonnegative integer `k`, set

    d = 2*n + 6*epsilon + 5 - k,
    m = k+2.

For `epsilon=-1` take `n>=k+3`. For `epsilon=+1` take `n>=2(k+2)`. Then:

1. Every such substitution is primitive and has an irreducible cubic characteristic polynomial with one real Perron eigenvalue `beta>2`, and two real eigenvalues of absolute value strictly below `1`. Thus it is a valid primitive irreducible Pisot example, of determinant `2*epsilon`, inside the **open** `l=floor(n/d)=0` class-A strip.
2. One of its two non-Perron eigenvalues, call it `lambda_-`, lies in the **exact rational isolating interval**

       -1 < lambda_- < -1 + (k+2)/n.

3. In particular, for any rational `0 < eta < 1`, and any fixed `k`, selecting an allowed integer `n > (k+2)/eta` gives `|lambda_-| > 1-eta`. Therefore **no parameter-independent strict contraction margin** for both non-Perron eigenvalues can hold on the class-A strip, even on any one of these boundary-distance rays. This is a negative result about one style of proof, *not* a negative result about boundary hitting.
4. Write `h=1/(beta-1)`, `u=d*h`, using the **repository's** class-A eigenlength coordinate (not `1/beta`). For `epsilon=-1`, `beta in (n+2,n+3)` and hence

       (2n-1-k)/(n+2) < u < (2n-1-k)/(n+1).

   For `epsilon=+1`, `beta in (n+4,n+6)` and hence

       (2n+11-k)/(n+5) < u < (2n+11-k)/(n+3).

   For the minus sign and `n>=k+4`, `u>1`; for the plus sign, `u>1` throughout the stated domain. In both cases the earlier `l>=5` certification box `u<=1/5` is inapplicable without a new parameter chamber and new proof.

## 2. Proof using exact integer and rational signs

In the basis `(x,c,y)`, the incidence matrix and characteristic polynomial are

    M = [[2, 1, 1], [0, 1, 1], [n+d, n, n+epsilon]],
    det M = 2*epsilon,
    P(T) = T^3 - (n+3+epsilon) T^2
           + (n-d+2+3*epsilon) T - 2*epsilon.

The matrix `M^2` is strictly positive for the stated positive parameters, so the substitution is primitive. With the displayed `d`, write `z=(k+2)/n`. Direct expansion in `Z[n,k,epsilon][z]` gives

    P(-1) = -(k+1),
    P(-1+z) = 1 + (4-epsilon)*z - (6+epsilon)*z^2 + z^3.

For `epsilon=-1`, `0<z<1`, so `P(-1+z)=1+5z(1-z)+z^3>0`. For `epsilon=+1`, `0<z<=1/2`, so `P(-1+z)=1+3z-7z^2+z^3 >= 1-z/2+z^3>0`. These signs isolate `lambda_-` in `(-1,-1+z)`.

If `epsilon=-1`, the additional signs are

    P(0)=2>0,    P(1)=-d<0,
    P(n+2)=-n^2-2n+2+k(n+2)<0,
    P(n+3)=3n+11+k(n+3)>0.

The third inequality follows from `k<=n-3`. Therefore the other two roots lie in `(0,1)` and `(n+2,n+3)`. If `epsilon=+1`, the other signs are

    P(0)=-2<0,
    P(n+4)=-n^2-10n-26+k(n+4)<0,
    P(n+6)=n^2+12n+34+k(n+6)>0.

The middle inequality uses `k<=n/2-2`. Thus the other two roots lie in `(-1+z,0)` and `(n+4,n+6)`. In each case the three disjoint intervals exhaust all roots of the cubic. There is exactly one root outside the open unit disk, and it is positive.

For irreducibility over `Q`, a reducible monic cubic with constant coefficient `-2*epsilon` would have an integer root in `{+1,-1,+2,-2}`. Yet

    P(1)=-d,  P(-1)=-(k+1),
    P(2)=-2*(n+d),  P(-2)=-2*(n+k+7),

and all four values are nonzero. The polynomial is irreducible. Finally, the parameters meet `1<=d<=2n+6epsilon+5` and `n<d`, hence `l=0`. This does **not** use global unimodularity, independent tile-length hypotheses, predecessor contraction or any analytic limit evaluation.

## 3. Local bounded exact experiment (independent implementation)

A separate pure-standard-library Python BFS expands *literal substitution words* starting from all three ordered swap-seed pairs, greedily splits each inflated balanced pair at its actual first zero Parikh-return positions, and retains each ordered child ordinal, span and normalization orientation. It then computes the backwards-reachable states from literal one-letter diagonal children. The replay refuses any word/state/edge cap. It does **not** implement the occurrence-target packet structure or independently certify the repository's Mojo checker.

For `epsilon=-1, n=3, d=5, k=0`:

- `sigma(0)=0222222220`, `sigma(1)=12220`, `sigma(2)=0221`.
- Local graph: **261** normalized states, **12,546** actual ordered child factors, maximum state word length **22,592**, and **2** distinct one-letter diagonal states.
- All 261 states reach a diagonal, maximum shortest target distance **2**. Root distances to a *diagonal child*, **not necessarily an interior target**: `01|10=1`, `02|20=1`, `12|21=2`. Actual shortest-path witnesses include `01|10 -> 2|2` via child ordinal 1, span `[11,12)`; `02|20 -> 0|0` via child ordinal 0, span `[0,1)`; `12|21 -> 022112220|122200221 -> 2|2` via ordinals 0,1 and spans `[0,9)`, `[24,25)`. The **`02|20` witness starts at the outer boundary**, an explicit control showing why these simple graph distances cannot be promoted to target-aware interior BH. The executable receipt preserves all these witnesses.
- SHA-256 over deterministic ordered child `(parent ID, ordinal, child ID, start, end, orientation)` lines: `ac39017ae34f7ca7c8fb092080bf3292f435c8e3cdcc16244cd2ceafb037ba1b`.

This is a *single finite prototype calculation*, not a new infinite-family theorem or a target-aware C4 packet certificate. In particular, plain diagonal reachability is weaker than the localized strictly-interior offset-zero target of the target-aware packet checker. It has not been cross-replayed against the canonical Mojo output or hosted CI.

## 4. Implications and next proof checks

**Priority A — proof architecture for the still-open class-A strips.** Existing `l>=5` `(h,u)` Bernstein/hull signs cannot be copied to `l=0`; the boundary-distance coordinate `k=2n+6epsilon+5-d` exposes a genuine near-`-1` eigenvalue chamber. Test whether a `k`-indexed interval/hull certificate (rather than a uniform spectral gap or fixed hitting depth) supports actual ordered occurrence-descent on finite cells. Acceptance is symbolic all-child carrier closure and an occurrence-indexed descending witness on each certified chamber, not root isolation alone.

**Priority B — independent cross-replay.** Reproduce the `n=3,d=5,epsilon=-1` finite graph using the canonical Mojo BPA and compare normalized-state counts, ordered child edge multiplicities, target distances and a serialized sorted edge digest. A mismatch invalidates the local finite proxy pending reconciliation. This does not replace the target-aware packet tests from Issue #9.

**Priority C — fill `l=1..4` strips and class C.** Enumerate carrier labels for each `l=0,1,2,3,4` as affine chambers in `(d,r)` only after tying every label to actual word factorization and Perron geometry. Existing PR #335 already covers every `l>=5`; do not repeat it. Independently continue the class-C gaps `d>=6` and class-B top-layer infinite descent program.

**Priority D — retain the universal firewall.** Proving a strip family, a finite graph, or algebraic spectral inequalities never closes Issue #139/BH, #138/A1′, #84, the C4 ordered hub-residual word obligation, G1 for all PIP substitutions, or PSC. Issue #9 closure remains administrative/routing, not mathematical.

## 5. Reproduction, status and provenance

Run from any Python 3.10+ installation, with no third-party dependencies:

```sh
python psc_class_a_boundary_probe.py --bpa-example > receipt.json
```

The accompanying fixed receipt contains 24 exact algebraic sample certificates spanning `k=0,1,3,10` under both signs, plus the single finite graph. All rational signs are checked using `fractions.Fraction` and integer arithmetic; the tested characteristic polynomial and determinant are also checked against direct 3-by-3 matrix determinants. The **unbounded** claim follows from the displayed symbolic sign proof, not from those 24 instances.

- Local script SHA-256: `e2621b9466fd2c6e5f0f32f5f6e7ed3d6249857ef871ee6f8f9998a5b0e23f72`.
- Receipt SHA-256: `de2beb836c3d04a495d6faca650e8b1795d0dd7eaeb75f955e21f258b3180f12`.
- On 2026-10-26, [PR #345](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/345) was **open**, head `aaa6a86fc06bb7b7d1002f7746a29df4836c4bb7`, already working on status governance and the #331 regression. It was not modified here.
- Immutable current base: https://github.com/larsbx/pisot-substitution-conjecture-research/commit/4eb0427d440e4c2cfe28ce7de934061f1c9bf3ad
- Canonical scope tracker: https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139

**Completion ledger delta:** one **locally proved exact negative-control lemma** and one **locally replayed finite BPA example** added as proposed research evidence. No existing PSC proof obligation is discharged, and no CI/PR/ledger change is claimed.
## Integration addendum — 2026-10-26

The preceding “local/no-PR” line records the **pre-integration snapshot**, not the eventual pull request state. The canonical coefficient verifier lives at `kernel/psc/class_a_boundary_layer.mojo`; `kernel/tests/test_class_a_boundary_layer.mojo` refuses corrupt endpoint formulas and invalid signs. The independent Python finite-graph probe lives under `oracles/python/`, and its output under `evidence/class-a-boundary-layer-2026-10-26/`. This remains a **scoped negative-control theorem and finite diagnostic** only. The targeted literature baseline is already in `docs/class-a-gap-uniformity-stopgo-2026-10-23.md` (Barge's balanced pairs, Berthé et al.'s unimodular family constructions, Minervino–Thuswaldner's non-unit setting). None of those results supplies this non-unit `l=0` certificate or an occurrence-level hitting theorem. The existing stop/go decision is reused rather than repeated.

### Work shown

#### Assumptions and hypotheses
Admissible class-A determinant-two parameters, `k>=0` and `n>=k+3` (minus) or `n>=2(k+2)` (plus). No global independence or unimodularity assumption.

#### Derivation / reduction
The sign proof in §2 isolates the three distinct real roots and, by the rational-root criterion, proves irreducibility. The canonical Mojo module checks every displayed polynomial evaluation and the cleared rational endpoint identity coefficientwise in `Z[n,k]`. The sign bounds are mathematical inequalities in §2, not claimed to be decided by the Mojo checker.

#### Evidence and replay
Run `python oracles/python/class_a_boundary_probe.py --bpa-example` and `python -m pytest -q tests/test_class_a_boundary_layer.py`. In `kernel/`, run `pixi run --locked mojo run -I . tests/test_class_a_boundary_layer.mojo` and `pixi run --locked mojo run -I . class_a_boundary_layer.mojo`. A dedicated hosted workflow runs both. The finite BPA search raises on budget exhaustion.

#### Negative controls
Invalid sign and damaged polynomial coefficient refuse; a local seed witness is an outer-boundary diagonal rather than interior offset-zero success. The near-`-1` family refutes a uniform spectral contraction margin, not BH.

#### Non-claims / remaining gaps
No target-aware packet coverage, no global PIP theorem, no C4 ordered-word solution, no general G1 and no PSC. No independent human review has occurred.

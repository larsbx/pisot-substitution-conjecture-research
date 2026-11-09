# Solidifying the scratch census and the reductio-lemma controls: literature stop/go gate — 2026-11-07

**Status:** stop/go note (AGENTS.md "Targeted literature stop/go check") for
two proposed computations that would turn scratch figures of the
[Concentration attack](c4-concentration-attack-2026-11-06.md) §4 and the
[general-structure note](c4-general-structure-2026-11-06.md) §6 into
repository evidence. It moves no governed claim status, adds no ledger
claim, and writes no code. The figures quoted from scratch below are labelled
as scratch and are not evidence.

Notation follows the manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`
(`def:balanced`, `def:bpa`, `thm:defect-intertwiner`, `thm:deg23`,
`thm:sieve`, `prob:concentration`) and the general-structure note
(strict system, `r(C)`, R2, R3, R3′, Proposition B′, Corollary B, (H), (N0)).
`u ∼_k v` means `K_1 = … = K_k = 0`, where `K_r(u,v) = N_r(u) − N_r(v)` is
the difference of the scattered-subword counts of length `r`. A pair
`(u, v)` is *irreducible* if `|u| = |v| = n`, `p(u) = p(v)`, and
`p(u[0,j)) ≠ p(v[0,j))` for `0 < j < n`. A *reductio lemma* is a Lean
theorem whose hypotheses describe a hypothetical strict component (the
usage of `proof/PscVerif`, e.g. `Degree3Sector`, `Degree4Floor`).

## 0. Decisions

| Item | Decision |
| --- | --- |
| A-bin: binary census, `k = 1..3`, `n ≤ 20` | **Stop as a census; redirect to a code calibration.** The irreducible answer is a theorem (`k ≥ 2`: zero) plus a closed form (`k = 1`: `2·C_{n−1}`); §3.3. Keep the binary run only to calibrate the enumerator, against the closed form and against the published class counts `D_k(n)`. |
| A-ter, `k = 1` | **Redirect.** The minimal length is 2, which is trivial. Report the counts as a by-product of the `k = 2` pass: all irreducible pairs, counted by an exact lattice-walk recurrence, minus those with `K₂ = 0`. No separate census. |
| A-ter, `k = 2, 3`, `n ≤ 12` | **Proceed, narrowed.** The novelty is restricted to the irreducibility specialisation. Minimal lengths of the unrestricted relation are known (the `k`-deck numbers `S(k)`, §2). The census must settle four scratch items (§3.6). |
| B1: both-outside irreducible non-Pisot | **Stop.** R3 excludes every finite child-closed set with a noncoincident pair, so every run could only exhaust its budget. |
| B2: one-outside irreducible non-Pisot, seeded closures | **Stop.** Swap seeds have `K₂ ≠ 0`, so their closures are infinite (Corollary B(iii)). Prefix seeds never terminate (Proposition B′). |
| B2/B3: `K₂ ≡ 0` strict systems (one-outside and reducible `χ_M`) | **Proceed, narrowed and fused with A.** Port the scratch greatest-fixed-point window search to Mojo, consuming A's pair list. The domain is the primitive specimens outside PIP and outside both-outside, with non-synchronizing endpoints, in a stated window `L`. A find is a full control or a leave-one-out control for the reductio lemmas (§5). An empty window is a bounded observation, never a verdict. |
| B3: reducible `χ_M`, strict systems with `K₂ ≠ 0` | **Stop a new search; redirect to the pinned carriers.** The 28 class representatives pinned in `kernel/tests/test_c4_quotient_spectrum.mojo` already supply primitive, literal drop-irreducibility controls for the reductio lemmas whose hypotheses do not include `K₂ ≡ 0` (§5). Drop-irreducibility controls with `K₂ ≡ 0` can come only from the window search in the row above. That every pinned carrier has `K₂ ≠ 0` on its seed is a direct check for the port to pin; it is not established here. |

## 1. Repository prior art (what exists, and with what status)

- **Theorems, written or formal.**
  - Over two letters, no irreducible noncoincident pair is 2-binomially
    equivalent: `Psc.PrimitiveExpansion.binary_no_equiv2`, Lean, standard axioms
    only. So the premise of the reduction lemma is empty there:
    `binary_reduction_premise_empty`.
  - Irreducible noncoincident pairs have distinct first letters:
    `Psc.Binomial.heads_ne`.
  - R2, R3, R3′, Proposition B′ and Corollary B are written proofs in the
    general-structure note §3 (human review pending; no executable claim).
- **Pinned executables.**
  - The six length-7 `K₂ = 0` seeds (`kernel/psc/seeds.mojo`, from archived
    `PROOF_CERTIFICATE.md` §4, which asserts "exactly six" without a pinned
    enumeration).
  - The length-12 `K₁ = K₂ = K₃ = 0`, `K₄ ≠ 0` state of
    `tests/test_multidegree_sieve.py`, "found by exhaustive enumeration" (that
    enumeration is not in the repository).
  - The 28 strict-carrier class representatives, all with reducible `χ_M`
    (`kernel/tests/test_c4_quotient_spectrum.mojo`).
  - The two Concentration controls (`kernel/tests/test_c4_concentration_controls.mojo`).
- **Scratch only (Python or C, not repository evidence).**
  - Shortest irreducible `K₂ = 0` pairs have length 7, and shortest
    irreducible `∼₃` pairs have length 12 (attack note §4).
  - The window search: no strict system with `K₂ ≡ 0` has all states of length
    ≤ 13. This was checked on the 15,192 primitive substitutions with images
    ≤ 3 and non-synchronizing endpoints, and with states ≤ 11 on the 592,134
    such substitutions with images ≤ 4. It was a C program, `k2zero_strict.c`,
    in the 2026-11-06 session scratchpad.
  - The swap-seeded landscape over all 59,319 substitutions with images ≤ 3
    (general-structure note §6).
  - An earlier-session scratch enumeration (`concentration/deg4/`) found
    irreducible `∼₃` ternary pairs, unordered, as follows: 0 for `n ≤ 11`, 12
    for `n = 12`, 24 for `n = 13`, 6 for `n = 14`. All have `K₄ ≠ 0`. The drop
    from 24 to 6 has not been re-derived, and none of these figures is cited.

## 2. Sources read for this gate

| Source | What was read | Used for |
| --- | --- | --- |
| M. Rigo, P. Salimov, *Another generalization of abelian equivalence: binomial complexity of infinite words*, Theoret. Comput. Sci. 601 (2015) 47–57, doi:10.1016/j.tcs.2015.07.025 (long preprint `orbi.uliege.be/2268/149313`) | Definitions; Lemma 3 (binary `∼₂` classes: a class is fixed by `\|u\|_a` and the count of the subword `ab`); Theorems 4–6 (bounded `m`-binomial complexity of Thue–Morse) | terminology "k-binomial equivalence"; the binary `∼₂` criterion |
| M. Lejeune, J. Leroy, M. Rigo, *Computing the k-binomial complexity of the Thue–Morse word*, J. Combin. Theory Ser. A 176 (2020) 105284 (arXiv:1812.07330) | Lemma 30 (Ochsenschläger): `φ^k(0) ∼_k φ^k(1)` and `φ^k(0) ≁_{k+1} φ^k(1)`; Lemma 31 (transfer) | the Thue–Morse blocks, whose first defect degree is exactly `k+1` (positive control of the degree classifier) |
| D. D. Freydenberger, P. Gawrychowski, J. Karhumäki, F. Manea, W. Rytter, *Testing k-binomial equivalence*, in *Multidisciplinary Creativity* (2015) 239–248 (arXiv:1509.00622) | Theorem 1 (deterministic polynomial test, via automata); the randomised test (Lemmas 1–3, a polynomial identity test over `F_p`) | algorithmic prior art; why neither algorithm is used (§3.4) |
| J. Chrisnata, H. M. Kiah, S. Rao, A. Vardy, E. Yaakobi, H. Yao, *On the number of distinct k-decks: enumeration and bounds*, ISCIT 2019, 519–524 (`par.nsf.gov/servlets/purl/10191056`) | Table I: `D_k(n)`, the number of `k`-deck classes of binary words of length `n`, for `3 ≤ k ≤ 6` and `k ≤ n ≤ 30`; Theorem 7 (`S(6) = 30`); "the exact values of `S(k)` have been determined for `k ∈ {3,4,5}`" | the known minimal lengths; calibration targets |
| R. Golm, M. Nahvi, R. Gabrys, O. Milenkovic, *The gapped k-deck problem*, arXiv:2201.12671 (2022), §I | The definition of `S(k)`; same `k`-deck implies same `l`-deck for `l ≤ k`; reports Manvel et al.: `S(k) ≤ 2^k` (Thue–Morse) and the reduction of `k`-reconstructibility to binary strings | the alphabet-independence of `S(k)` (as reported; Manvel et al. 1991 not read) |
| B. F. Martensen, *A generalized balanced pair algorithm*, Topology Proc. 28 (2004) 163–178 (arXiv:math/0309194) | §§1, 3, 4. §3.2: Livshits' original algorithm uses letter equivalences, and in the constant-length case it always terminates (Dekking). §3.3: the Perron-length equivalence `∼_{L_λ}`. Theorem 3.10. Example 3.13: a rewriting of Morse–Thue on which no version terminates. §4: eigenvalues 0 and roots of unity as the obstruction channel | the balanced-pair algorithm off the irreducible Pisot cone |
| M. Rigo, M. Stipulanti, M. A. Whiteland, arXiv:2201.04603 (re-read from the 2026-11-06 scratch copy) | Theorem 2.3 (Whiteland, WORDS 2021, Thm 3.5): for `\|x\| = \|y\|`, `xy ∼_k yx` iff `x ∼_{k−1} y`; Theorem 3.5 and Corollary 3.6 (Parikh-collinear morphisms) | the commutation mechanism, which always produces reducible pairs; the rank-one subclass |

**Cited only, not read here.**
- Ree, *Lie elements and an algebra associated with shuffles*, Ann. of Math.
  68 (1958) 210–220.
- Reutenauer, *Free Lie Algebras*, LMS Monographs 7, Oxford 1993. Ree's
  criterion is its Theorem 3.1(iv) as cited by arXiv:1011.1528. Witt's
  formula and its multigraded form are also there; no theorem number is
  asserted.
- Magnus' theorem that the dimension subgroups of a free group are its lower
  central series.
- Sirvent–Solomyak 2002, Remark 2. It was read by the repository and is
  quoted in the general-structure note §1.
- Queffélec, LNM 1294, for the non-discrete spectrum of Thue–Morse.

## 3. Experiment A: irreducible `k`-binomially equivalent pairs

### 3.1 Exact claim proposed

For an alphabet `Σ` of size 2 and `n ≤ 20`, or size 3 and `n ≤ 12`, for
`k = 1, 2, 3` and each `n`, count the ordered irreducible pairs `(u, v)` over
`Σ` with:
- `u ≠ v`;
- `u ∼_k v`;
- first defect degree `k + 1` (`K_{k+1} ≠ 0`).

Report the least `n` with a nonzero count, the classes under
`G = S_Σ × ⟨reversal⟩ × ⟨swap⟩`, and, at `k = 3`, how many pairs have
`K₄ ≠ 0` and how many have `K₄ = 0`.

### 3.2 Prior art and terminology

- **The unrestricted question is the `k`-deck problem.** The `k`-deck of a
  word of length `n ≥ k` is the multiset of its length-`k` subsequences. Two
  words of equal length have the same `k`-deck iff they are `k`-binomially
  equivalent (same deck ⇒ same `l`-deck for `l ≤ k`, Golm et al. §I).
  - Let `S(k)` be the least length with two distinct words of equal
    `k`-deck. It was posed by Kalashnik (1973).
  - Manvel–Meyerowitz–Schwenk–Smith–Stockmeyer (Discrete Math. 94 (1991))
    showed `S(k) ≤ 2^k` with the Thue–Morse pairs, and that it suffices to
    treat binary words. So `S(k)` does not depend on the alphabet size `≥ 2`
    (as reported by Golm et al.).
  - From Table I of Chrisnata et al. (the first `n` with `D_k(n) < 2^n`):
    `D_3(7) = 126`, `D_4(12) = 4092`, `D_5(16) = 65534`, `D_6(30) = 2^30 − 4`.
    Hence `S(1), …, S(6) = 2, 4, 7, 12, 16, 30`. The first two are elementary:
    `(01, 10)` and `(0110, 1001)`.
  - The minimal lengths of distinct `k`-binomially equivalent words are
    therefore **known**. The census must not present them as new.
- **Irreducibility is the only new restriction.** No source read studies
  `k`-binomial equivalence of irreducible balanced pairs (Livshits,
  Sirvent–Solomyak terminology). Here is what is known in its direction:
  - Binary: emptiness for `k ≥ 2` (`binary_no_equiv2`, Lean). It is
    elementary given Rigo–Salimov Lemma 3.
  - The commutation theorem (Whiteland, RSW Theorem 2.3): `x ∼_{k−1} y`,
    `|x| = |y|` ⇒ `xy ∼_k yx`. It manufactures `∼_k` pairs that are always
    reducible, being cut at `|x|`. Ochsenschläger's blocks
    `(φ^k(0), φ^k(1)) = (φ^{k−1}(0)φ^{k−1}(1), φ^{k−1}(1)φ^{k−1}(0))` are its
    iterates, so they are reducible for `k ≥ 2`.
  - The scratch minima 7 (`∼₂`) and 12 (`∼₃`) for ternary irreducible pairs
    are not in any source read.
- **Other relations, not to be confused.**
  - Simon's congruence (presence of subwords, not multiplicity).
  - `k`-abelian equivalence (factors, Karhumäki–Saarela–Zamboni).
  - Parikh-matrix equality (Mateescu et al.; already recorded in the attack
    note §1).
- **Lie structure, citation only.**
  - Via the Magnus map `a ↦ 1 + a`, `μ(w) = Σ_x binom(w, x)·x`. So `u ∼_k v`
    iff `v⁻¹u` lies in the `(k+1)`-st dimension subgroup, which is
    `γ_{k+1}(F)` (Magnus): equality in the free nilpotent group of class `k`.
    Lejeune–Rigo–Rosenfeld (arXiv:2001.11732, Theorem 11) prove the class-2
    case for monoids.
  - The leading term of `μ(v⁻¹u) − 1` is `K_{k+1}(u, v)`, a Lie element. This
    is the classical source of `K_r ∈ Lie_r`, which the repository proves for
    `r = 3, 4` on three letters through Ree's criterion (`Psc.Lie3`,
    `Psc.LieWeights`, `Psc.Defect4Lie`).
  - The Witt dimensions `3, 8, 18` (ternary) and `1, 2, 3` (binary) of
    `Lie_2, Lie_3, Lie_4` bound the coordinates the census needs. Nothing
    here is new.

### 3.3 Derivation: the binary half is already decided

- **(a) `k ≥ 2`: zero at every length.** This is `binary_no_equiv2`. For an
  irreducible binary pair, `K₂(u,v)_{01} = Σ_j d_j` with
  `d_j = |u[0,j)|_0 − |v[0,j)|_0`. The walk `d` moves by at most 1 per step
  and never returns to 0 at a proper cut, so every `d_j`, `0 < j < n`, has
  the sign of `d_1 ≠ 0`, and the sum is nonzero. Hence no binary irreducible
  pair has first defect degree `≥ 3`.
- **(b) `k = 1`: exactly `2·C_{n−1}` ordered pairs of length `n ≥ 2`, all of
  first defect degree 2.**
  - Encode `(u_j, v_j)` as a step of `d`: `(0,1) ↦ +1`, `(1,0) ↦ −1`, and
    `(0,0), (1,1) ↦ 0`, two flat colours.
  - Irreducibility says `d` leaves 0 at step 1, returns at step `n`, and
    stays on one side in between.
  - Between the first and the last step there is a bicoloured Motzkin path
    of length `n − 2` on the shifted half-line. There are `C_{n−1}` such
    paths (the standard bicoloured-Motzkin/Catalan bijection), and the sign
    contributes the factor 2.
  - `u ≠ v` holds because the first letters differ. By (a), `K₂ ≠ 0`.
  - *Scratch check, not evidence:* direct enumeration agrees for
    `2 ≤ n ≤ 12` (2, 4, 10, 28, …, 117572), and finds no `K₂ = 0` pair among
    them.

So a binary census adds no mathematics. Its value is as a **calibration** of
the enumerator, on two independent targets:
- (i) the closed form above, and 0 for `k = 2, 3`;
- (ii) the published class counts `D_3(n)`, `D_4(n)` for `n ≤ 20`, by
  bucketing without the irreducibility filter.

The targets from Table I:

| `k` | `n = 7` | 8 | 12 | 13 | 16 | 20 |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 126 | 247 | 3337 | 6208 | 36649 | 306285 |
| 4 | 128 | 256 | 4092 | 8176 | 65075 | 1028448 |

(*Scratch check, not evidence:* a Python replay agrees with Table I for
`D_3`, `D_4` at every `n ≤ 13`.) A disagreement would be a defect of the
census code, or a misreading of the table, and must fail the run. It is not
a mathematical finding.

### 3.4 Hypotheses that transfer and those that do not

**Transfer.**
- `S(k)` is alphabet-independent. So on any alphabet, two distinct words of
  equal length `n` have a nonzero defect of degree at most:
  - 2 for `n ≤ 3`;
  - 3 for `n ≤ 6`;
  - 4 for `n ≤ 11`;
  - 5 for `n ≤ 15`;
  - 6 for `n ≤ 29`.
- In particular, every distinct pair in the ternary window `n ≤ 12` has
  first defect degree at most 5, and the census class `DEGREE_FIVE_PLUS` of
  `psc/defect_degree.mojo` can only be degree exactly 5 there.
- This is an import: it rests on Chrisnata et al.'s computer enumeration and
  on Manvel et al.'s binary reduction, which was read only as reported. The
  census therefore must not relabel `DEGREE_FIVE_PLUS` as 5 on its strength.
  It may report the import as consistent or inconsistent with its own counts.

**Do not transfer.**
- The minimal lengths `S(k)` say nothing about *irreducible* pairs. Over
  binary the irreducible minima are infinite for `k ≥ 2`. The scratch
  ternary minima (7, 12) happen to equal `S(3), S(4)`. No mechanism for this
  is known, and it is recorded only as an observation for the census to
  report.
- Both FGKMR tests are for single pairs. Their randomised test may not enter
  a census (AGENTS.md: randomness never enters a census or certificate). The
  deterministic one is far costlier than direct streaming of `N_1, …, N_4`,
  which is `O(n·3^r)` per word with the existing prefix accumulators.

### 3.5 Negative and positive controls the census must carry

- **Positive control of the degree classifier:** the Thue–Morse blocks
  `(φ^k(0), φ^k(1))`, `k = 1..4`, have first defect degree exactly `k+1`
  (Ochsenschläger, LLR Lemma 30).
- **Negative control of the irreducibility filter:** the same blocks for
  `k ≥ 2`, the commutation pairs `(xy, yx)`, and the binary `S(k)` witnesses
  must all be rejected as reducible.
  - `(0110, 1001)` is cut at 2.
  - `(0110001, 1000110)` is cut at 2. This is a scratch-found `S(3)`
    witness; its 1s sit at positions `{1,2,6}` versus `{0,4,5}`.
- **Pinned states the census must reproduce:**
  - the six `kernel/psc/seeds.mojo` seeds. They form one orbit under `G`,
    which is a scratch check of the six words only;
  - the `DEGREE4_STATE` of `tests/test_multidegree_sieve.py`;
  - the Lean control pairs `wTPair = (0112201, 1200112)` and `w4Pair`.
- **Fail closed:**
  - a bucket overflow, a pair outside the window, or a disagreement with a
    calibration target aborts the run;
  - lengths beyond the window are reported as "not enumerated", never as
    zero.

### 3.6 Decision for A

**Proceed, narrowed** to the ternary irreducible census for `k = 2, 3`,
`n ≤ 12`. An extension to `n = 13` (and 14 if the budget allows) is needed
only as input to B. The census is canonical Mojo:
- a driver and a module under `kernel/`;
- reuse of `psc/words` (`k2`, `k3`), `psc/defect_degree` (`n4`, `k4`),
  `psc/symmetry` and `psc/histogram`;
- binary words handled as the sub-census of words avoiding letter 2, not
  with a second kernel.

It enumerates by signature bucketing:
- stream `(N_1, …, N_k)` per word;
- bucket by the exact signature;
- test irreducibility and `K_{k+1}` only inside buckets.

The cost is `O(3^n·n·3^k + Σ|B|²·n)`.

It must settle four scratch items:
- (i) the minimal lengths 7 and 12;
- (ii) completeness of the six length-7 seeds. The six seed words form
  **one** `G`-class; this is a scratch check of six explicit words. So if the
  length-7 list is exactly the seeds, the attack note's "six classes" counts
  normalised pairs and agrees with the defect-degree note's "one six-element
  relabelling orbit". The census must settle which reading is right;
- (iii) the length-12 `K₄ ≠ 0` count, and whether any irreducible
  length-12 pair is `∼₄`. This is possible a priori, since `S(4) = 12`;
- (iv) the scratch counts 12/24/6 at `n = 12/13/14`.

**Contracts and receipts.**
- The regression test ends with `require_contract(...)`. No ledger claim is
  targeted by this note.
- Promotion to a finite-domain claim would go through `tools/make_ledger.py`
  and `claim_governance.toml`, and is not proposed here.
- The domain is the finite set of equal-length word pairs, not
  `pip_corpus()`, so the census-library rule about walking the corpus does
  not apply.

## 4. Experiment B: strict systems outside PIP

### 4.1 Exact claim proposed

Run a budgeted exploratory search, over the primitive substitutions on
`{0,1,2}` with images of length ≤ 3 that are not in the PIP corpus, for
strict systems. These are finite, nonempty, child-closed (under the
zero-return reduction `red`), coincidence-free sets of irreducible pairs. The
two classes searched are irreducible non-Pisot and reducible `χ_M`. The
purpose is leave-one-out controls for the reductio lemmas.

### 4.2 Prior art

- **In the repository** (§1): R2, R3, R3′, Proposition B′, Corollary B;
  the scratch landscape and windows; the 28 pinned carriers;
  `ex:nonpisot` (`1/012/1`, reducible, `K₂ ≠ 0`).
- **Literature.**
  - Martensen §3.2–3.3 and §4: off the irreducible case, Parikh balance is
    not the spectrally meaningful relation. The relation that is
    meaningful is `∼_{L_λ}` (Perron lengths). Livshits' letter-equivalence
    version always terminates in constant length (Dekking). Persistent
    non-termination comes from eigenvalues 0 and roots of unity.
  - Martensen Theorem 3.10(b) (with `L = L_λ`) and Example 3.13 (a
    Morse–Thue rewriting on which no version terminates).
  - Sirvent–Solomyak Remark 2 expects non-termination for irreducible
    non-Pisot. The repository's Proposition B′ proves the prefix-seeded half
    on three letters.
  - Thue–Morse `0 ↦ 01, 1 ↦ 10` (`χ = x(x − 2)`, reducible, Perron root the
    integer 2) carries the strict system `{(01,10), (10,01)}` with `K₂ ≠ 0`.
    This is `thueMorse_control` in Lean.

### 4.3 Derivations that fix the search domain

The domain needs no new theorem. Each step is a consequence of a statement
already in the repository.

1. **Endpoint filter.** If the first-letter map `h(a) = σ(a)[0]` is
   eventually constant, there is no strict system. The same holds for the
   last-letter map. This is the eventually-constant case of Theorem A(1),(3)
   of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md): `A(C)` is
   a nonempty set of off-diagonal pairs, and `g × g` maps it into itself
   injectively. The two-line form below is recorded because the scratch
   `gsync` filter used it without justification.
   - Let `(u, v)` be a state. Its first child is the first block of
     `red(σu, σv)`, with first letters `(h(u₀), h(v₀))`.
   - Iterating inside the child-closed `C` gives states with first letters
     `(h^m(u₀), h^m(v₀))`. These are equal for large `m`, against
     `heads_ne` (an irreducible noncoincident pair has distinct first
     letters).
   - For last letters, use the last child, whose last letters are
     `(t(u_last), t(v_last))` with `t(a) = σ(a)[−1]`. Then apply the mirror of
     `heads_ne`: an irreducible noncoincident pair has distinct last letters,
     since equal last letters would make the length-`(n−1)` prefixes
     balanced.
   - This is the `gsync` filter of the scratch window search, now with its
     justification.
   - **Strong-coincidence filter (prior, cut-pair Theorem A(4)).** No pair
     of `A(C)` is left strongly coincident. So a specimen whose three letter
     pairs all carry a left strong-coincidence witness, or by reversal all
     three right witnesses, has no strict system. This needs only that `σ`
     is nonerasing. It is a further domain filter: a witness is a verdict,
     and an absent witness within budget is undecided.
2. **Theorem-driven partition** (scratch sizes, exact Python over the
   59,319 substitutions):

   | class | primitive | non-synchronizing | status |
   | --- | --- | --- | --- |
   | PIP | 4,554 | 1,542 | the corpus; not part of B (C4 domain, `C4StandingCorpus`) |
   | irreducible, both non-Perron roots outside | 3,960 | 1,812 | **no strict system** (R3) |
   | irreducible, exactly one outside (real roots) | 3,216 | 1,704 | strict ⇒ `K₂ ≡ 0` (R2), `r(C) ≢ 2 (mod 3)`, and R3′ admissibility |
   | reducible `χ_M` | 21,588 | 10,134 | no structural theorem; 276 strict carriers (scratch), 28 classes pinned |

   The non-synchronizing totals sum to 15,192, the count the scratch window
   search tested. In the one-outside class:
   - `|det M| = 1` for 1,356 specimens. Only these admit `r(C) = 4`, and
     more generally `r = 3k+1`.
   - `r(C) = 3` needs `|det M| ≤ β`, i.e. `|α₂α₃| ≤ 1`.
   - All sizes in the table are scratch, computed by
     `wf9/probe/classes.py` with an exact Sturm count of roots in `(−1, 1)`.
3. **Seeded closures are pointless where B2 lives.**
   - In the one-outside class every swap seed `(ab, ba)` has
     `K₂(ab,ba)_{ab} = 1`, so its closure is infinite (Corollary B(iii)).
   - Every prefix seed `bpa-W` is non-terminating (Proposition B′).
   - A swap-seeded or prefix-seeded run there can only end capped.
4. **Greatest fixed point.**
   - Let `P_L` be the set of all irreducible noncoincident pairs with
     `K₂ = 0` and length ≤ `L`. It is exactly the output of A at `k ≥ 2`.
   - Iterate `X ↦ {T ∈ X : every child of T lies in X}` from `X = P_L`. The
     limit is the union of all strict systems with `K₂ ≡ 0` and all states
     of length ≤ `L`. It is nonempty iff such a system exists.
   - The iteration is exact and finite. Its correctness requires `P_L` to be
     **complete**. The scratch C program instead rejected children of length
     `< 7` on the strength of the scratch minimum; the port must take every
     length from A's list instead.
5. **The rank-one subclass.** Let `σ` be Parikh-collinear (`M = p·wᵀ`,
   rank 1, `χ_M = x²(x − β)`; RSW §3).
   - Then `M^{⊗r}x = (w^{⊗r}·x)·p^{⊗r}`.
   - `Lie_r ∩ ℚ·p^{⊗r} = 0` for `r ≥ 2`: the Dynkin operator gives
     `θ(P) = r·P` on `Lie_r` and `θ(p^{⊗r}) = 0`, since `[p,p] = 0`.
   - So `M^{⊗r}` kills `Lie_r`, and at the first defect degree the
     intertwiner `D_r N = M^{⊗r} D_r` (Lemma 0) reads `D_r N = 0`.
   - Every spectral constraint of the defect machinery is void there.
     Fixed points of such `σ` have bounded `k`-binomial complexity (RSW
     Corollary 3.6), so the conclusion of the reduction lemma is not
     contradicted there either.
   - This does not make the subclass more likely to carry a `K₂ ≡ 0` strict
     system. It says only that no current obstruction applies there. The
     constant-length carriers `012/120/201`, `012/201/120` and `102/210/021`
     among the 28 classes lie in it.

### 4.4 Hypotheses that transfer and those that do not

**Transfer.**
- R2, R3 and R3′ need only irreducibility of `χ_M` and finiteness and child
  closure. They need neither strictness nor legality nor reachability.
- The endpoint filter needs only `heads_ne`.
- The greatest-fixed-point argument needs only completeness of `P_L`.

**Do not transfer.**
- Strict systems over a reducible `σ` are statements about **Parikh** balance.
  By Martensen they carry no spectral meaning of their own, and they are not
  counterexamples to anything spectral.
- They are combinatorial controls only. Neither R2 nor R3 constrains them.
- None of this touches PIP: B is outside the corpus by construction, and a
  find there bears on (H) and combinatorial Concentration only.

### 4.5 Known negative controls

- A budget is not a verdict. In the general-structure note §7, swap-seeded
  closures of `σ = (1, 2, 001)`, `χ = x³ − x − 2`, and of
  `(01, 002, 122)` reached 10⁶ letters without closing. R2/R3 explain why.
  The port should keep one such run as a budget-exhaustion control,
  reported as `BUDGET_LENGTH` through `psc/bounded_bpa.mojo`.
- `ex:nonpisot` closes with 4 states, all with `K₂ ≠ 0`. It gives a pair of
  controls for the fixed-point code:
  - with the `K₂ = 0` filter off, the iteration seeded with these four
    states must keep all four;
  - with the filter on, they are not in `P_L` and must be discarded.

  Whether `1/012/1` carries some *other* `K₂ ≡ 0` strict system is a window
  question, answered only in scratch so far.
- The Lean `cyc3Norm` system (the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` on the relabellings
  of `wTPair` and their swaps) is child-closed and strict with `K₂ ≡ 0`, but
  not primitive. The search must exclude it through the primitivity screen.
  Fed to the fixed-point step alone, it must survive. This is a positive
  control that the iteration keeps closed sets.

### 4.6 Decision for B

- **B1 (both-outside): stop.**
- **B2/B3 seeded closures: stop.** No new swap-seeded landscape. In B2 it is
  theorem-guaranteed to cap. In B3 the scratch landscape and the 28 pinned
  carriers already provide what the controls need.
- **B2/B3 `K₂ ≡ 0` window: proceed, narrowed, fused with A.**
  - Port the window search to Mojo as a labelled exploratory search. The
    domain, in the deterministic `psc/corpus.mojo` `image_words` order, is
    the primitive, non-synchronizing specimens outside PIP and outside the
    both-outside class.
  - The window is `L = 13`, to reproduce the scratch result, with `L = 14`
    as a stated extension if A reaches it. The budget is the size of `P_L`.
  - Classification uses exact arithmetic (`psc/real_root_sign.count_real_roots`
    for the roots in `(−1, 1)`).
  - Output: "no `K₂ ≡ 0` strict system with all states ≤ `L` among `N`
    specimens", or the found systems with their substitutions. A window
    statement is never a verdict and never enters a certificate.

### 4.7 Bearing on the concurrent ClosedComponentSearch draft

When this gate was written, untracked files from a parallel workflow step
were in the working tree: `kernel/psc/closed_component_search.mojo`,
`kernel/c4_closed_component_search.mojo`,
`kernel/tests/test_c4_closed_component_search.mojo` and
`oracles/python/c4_closed_component_search.py`. They are not read in full,
reviewed or relied on here. Their module docstring describes three tests:
- strong-coincidence witnesses;
- swap-seeded exploration;
- a length-bounded core over **all** irreducible noncoincident pairs of
  length ≤ `L`.

These run over the irreducible non-Pisot and the reducible classes. The
decisions above apply to that draft as follows:
- **Seeded exploration in the irreducible non-Pisot class** can only end
  capped, or be decided by a strong-coincidence witness. A completed
  exploration there would contradict R3 or Corollary B(iii). It belongs
  among the draft's R2/R3 consistency checks, not among its verdicts.
- **The length core in the irreducible non-Pisot class** loses nothing by
  restriction to the `K₂ = 0` pairs (R2). That list is far smaller, so the
  restriction lets `L` reach the scratch window of 13 and beyond. In the
  both-outside subclass the core must be empty at every `L` (R3); a
  nonempty core there is a defect, to be raised.
- **In the reducible class** the all-pairs core is the right object, since
  strict systems with `K₂ ≠ 0` exist there. Its `K₂ ≡ 0` part is the window
  of §4.6.

## 5. The reductio lemmas: what each control drops, and what B could add

| Lemma family (Lean) | Hypotheses | Existing controls, and the hypothesis each drops | What B could add |
| --- | --- | --- | --- |
| `Binomial.ChildSystem.reduction_lemma`, `PrimitiveExpansion.reduction_limit_of_primitive` | primitive, `≥ 2` letters, a state, all states `∼₂`, irreducible, noncoincident | `thueMorse_control` drops `∼₂`; `binary_reduction_premise_empty`: the premise is empty on two letters; `cyc3Norm` appears to meet all but primitivity (no Lean statement of that) | a `K₂ ≡ 0` strict system for any primitive `σ` would be a **full** control and would refute combinatorial Concentration |
| `KernelCofactor` representative theorems | balance, `C ≠ ∅`, strongly connected `N_C`, irreducible `χ_M`, `ℓ > 0` with `ℓM = βℓ` (no Pisot) | `wT_rep_hyps` drops irreducibility (identity substitution) | a one-outside `K₂ ≡ 0` system (a strongly connected sink SCC of it) would be a **full** control |
| `Degree2Sector` (`exA_sector` and the Sector theorems) | normalisation, balance, `kw ≠ 0`, irreducible `χ_M` | `exA_sector` drops irreducibility | nothing in the irreducible class: by R2 these hypotheses force Pisot (also the module's own informal remark). Pinned reducible carriers are primitive drop-irreducibility controls only |
| `Degree3Sector.deg23_iii…`, `SectorBridge.exists_weight_root_q3` | `∼₂` states, a nonzero `K₃` column, irreducible `χ_M` with Pisot moduli, `ρ(S) ≤ β` | `m0_control` (matrix level, full); `census_empty_control` (degenerate full, `im Q₃ = 0`); `wT`, `cyc3Norm` drop irreducibility (and primitivity) | a one-outside system with `r(C) = 3` drops only the Pisot moduli; a reducible `K₂ ≡ 0` system drops only irreducibility |
| `Degree4Floor.sieve4…`, `theoremA_of_primitive`, `SectorBridge.exists_weight_root_q4` | `∼₃` states, a nonzero `K₄` column, irreducible Pisot `χ_M`, root bound | `w4_controls` (identity substitution; drops irreducibility and Pisot); `cyc4_galoisOrbit_input`; `plastic_matrix_controls`; `m0_no_degree4` (content) | a one-outside system with `\|det M\| = 1` and `r(C) = 4` drops only Pisot |
| `Degree4Floor.ssign_root_bound_of_primitive` | primitive, balanced states, a root `β` with `‖β‖ > 1` and every other root of modulus `< 1` (no irreducibility) | `plastic_empty_control` (degenerate, empty system) | no search needed: the pinned carrier `012/120/201` (`M = J`, `χ = x²(x − 3)`) with its strict system `{(012,120), (120,201), (201,012)}` and swaps appears to meet every hypothesis as stated, so it is a **candidate non-degenerate full control**. Not formalized or checked in Lean here |

So: a full control of a reductio lemma whose hypotheses include
irreducibility of `χ_M` together with Pisot moduli is not expected. One
would be a strict component of a PIP, which C4 excludes on the corpus and
which is open in general. The absence of such a control is the intended state
of a reductio lemma, not a loose end.

What the leave-one-out controls show is that a hypothesis does work. The
existing controls mostly drop irreducibility of `χ_M`, often together with
primitivity (`wT`, `w4`, `cyc3Norm` use the identity or a permutation
substitution) or with the Pisot moduli. Two hypotheses lack a control that
drops only them:
- **"Pisot", keeping irreducibility, primitivity and `K₂ ≡ 0`.** No existing
  control drops it alone. B's one-outside window is the only route to one.
- **"`K₂ ≡ 0`" in a primitive literal system.** Only `thueMorse_control`
  drops it, and only on two letters.

An empty window leaves both gaps open, and they are then recorded as open,
not as closed.

## 6. Non-claims

The following are not claimed:
- Concentration;
- combinatorial Concentration;
- (H), (N0), C4, BH, A1′, G1 or PSC;
- any count or minimal length of irreducible ternary pairs, all of which are
  scratch until A runs;
- the alphabet-independence of `S(k)` beyond its report by Golm et al.;
- the coincidence of the scratch minima with `S(3)`, `S(4)` as anything but
  an observation;
- that `012/120/201` is a Lean-checked control;
- any statement for strict systems with states longer than a stated window.

The partition sizes of §4.3 are scratch sizing figures.

## 7. Scratch probes of this gate (not evidence, not replayable from the repository)

All files are under the session scratchpad,
`/tmp/claude-0/-home-user-pisot-substitution-conjecture-research/0b08a8cb-c07f-54b1-a1b8-36d7f74c35c1/scratchpad/wf9/`:
- `probe/deck.py`: `S(1), S(2), S(3) = 2, 4, 7` by brute force over binary
  words.
- `probe/dk.py`: `D_3(n)`, `D_4(n)` for `n ≤ 13`, matching Table I.
- `probe/binirr.py`: `2·C_{n−1}` and no `K₂ = 0` pair, `n ≤ 12`.
- `probe/seeds.py`: the six length-7 seeds form one `G`-orbit.
- `probe/classes.py`: the §4.3 partition, exact.
- `lit/`: the PDFs and texts read.

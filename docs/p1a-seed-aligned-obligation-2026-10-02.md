# P1a: the aligned obligation of one swap seed — 2026-10-02

**Status:** exact finite census plus an elementary reduction. It moves no
theorem status. #84, #138, G1 and PSC remain open.

## 1. Question

Theorem 5.38 needs `OP_seed`: every overlap reachable from **one** swap seed
`(ab, ba)` is productive. The all-vertex `OP_all` contains the Arnoux–Ito
strong coincidence condition (Proposition 5.39(iii)). Does the one-seed
weakening shrink the aligned branch (#138), and can the seed be chosen so
that the aligned branch is vacuous?

## 2. Elementary reduction

The seed of `{a,b}` contains `(a,b,0)`. For any distinct `x,y`, an offset-zero
vertex `(x,y,0)` is productive exactly when `{x,y}` is eventually coincident in
the Barge–Diamond sense (prefix strong coincidence for that pair; PR #82).
Hence

```text
OP_seed for the seed of {a,b}
  =>  {a,b} is eventually coincident, and
      every pair {x,y} met at offset zero below that seed is eventually coincident.
```

So the aligned obligation of a seed is precisely its **aligned pair set**:
the unordered distinct pairs met at offset zero in its closure (taken up to
coincidences). When that set is all three pairs, `OP_seed` for that seed
implies the prefix strong coincidence condition for `sigma`.

## 3. Exact census

Canonical Mojo: `mojo/psc/seed_aligned_cover.mojo`,
`mojo/tests/test_seed_aligned_cover.mojo`. Exact Perron-field closures of
each of the three swap seeds of every specimen in the 4,554-member corpus; no
closure capped.

| seeds per specimen whose aligned pair set is all three pairs | specimens |
| --- | ---: |
| 3 | 3,264 |
| 2 | 120 |
| 1 | 1,134 |
| 0 | 36 |

| seeds per specimen that meet only their own pair at offset zero | specimens |
| --- | ---: |
| 1 | 102 |
| 0 | 4,452 |
| 2 or 3 | 0 |

Of the 13,662 seed closures, 11,166 meet all three pairs.

## 4. Consequences

- **No seed choice removes the aligned branch in general.** Only 102
  specimens have a seed whose closure stays inside its own pair, and none has
  two. Choosing the seed to be a Barge–Diamond good pair does not make #138
  vacuous.
- **On 3,264 specimens the aligned branch is the strong coincidence
  condition.** Whatever seed is chosen, `OP_seed` there implies eventual
  coincidence of all three pairs. A proof of the aligned branch that is
  uniform over PIP substitutions must therefore prove the ternary prefix
  strong coincidence condition on a class containing them.
- **Literature status.** Strong coincidence is proved for two letters
  (Barge–Diamond, Bull. SMF 130, 2002) and is open for three or more letters
  in general (Akiyama–Barge–Berthé–Lee–Siegel, *On the Pisot substitution
  conjecture*, Progr. Math. 309, 2015). The aligned branch is thus not a
  sub-lemma that the one-seed reduction makes easier; it carries that open
  problem.
- Every route order in `p1-two-route-map-2026-10-01.md` §4 passes through the
  aligned branch, so this cost is not avoided by working Route B first.

## 5. Decision

**Redirect the framing, not the program.** #138 should be stated and reviewed
as the ternary PIP prefix strong coincidence problem, with the reductions
already proved (hub star, fixed-edge / alternating-E normal form) as partial
results toward it. Novelty claims for the aligned branch are limited to those
reductions and to the non-unimodular setting. The 36 specimens with no
all-pairs seed, and the 102 with an own-pair-only seed, are the only corpus
specimens where the one-seed premise is strictly weaker than strong
coincidence on the aligned side.

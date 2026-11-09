# Degree five of the Concentration attack

Base revision: the merge of [PR #521](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/521).
The definitions reuse `Defect4.Equiv3`, `Defect4.K4`, and the existing signed
`Normalisation`. The degree-five results concern finite words and tensors.

## Lean statements

- `Defect5.Equiv4` is `Equiv3` plus equality of every degree-four scattered
  count. It is preserved by concatenation and substitution. The integral
  defect `K5` is additive on equivalent blocks.
- `Defect5.n5_subst` expands a substituted count using the 16 compositions of
  five. The all-singleton composition gives the fifth tensor power of the
  incidence matrix with output letters indexing rows. The other 15 terms
  involve counts of orders one through four. Their difference vanishes under
  `Equiv4`, giving `k5_subst`. For a fixed pair and substitution, the tensor
  identity is equivalent to vanishing of that combined correction, which
  may happen without `Equiv4`. The signed child identities use the exact
  ordered children and the swap signs from the existing normalization.
  `q5_mul_ssign` states the matrix identity over integers on every finite
  alphabet. `k4_rep_of_equiv4` invokes the degree-four theorem with its
  original balance hypothesis.
- The two proper shuffle relations at degree five use splits 1+4 and 2+3.
  The reverse splits give the same shuffles, with multiplicity. Products
  of scattered counts include overlaps. The overlap terms have at most
  four positions and cancel on `Equiv4` pairs.
- `Lie5` works in the 243 word coordinates over the rationals. It constructs
  the standard longest-suffix bracketings of the 48 Lyndon words, checks
  annihilation by both shuffle families, and checks an integral left inverse
  on the bracket columns. For each word coordinate, an integer certificate
  writes a nonzero multiple of its reconstruction residual as a combination
  of shuffle rows. The residual therefore vanishes over the rationals.
  The universal statements quantify over arbitrary rational tensors.
  `finrank_shuffleAnnih5Space` gives dimension 48, the numerical value of
  `(3^5 - 3)/5` at this degree. `Defect5Lie` supplies the Lie membership
  for every ternary defect column, the rational signed identity on those
  columns, and the vanishing of the inherited degree-four defect.
- The integral word and signed-child identities use no characteristic
  hypothesis. The span proof uses invertibility of the checked nonzero
  denominators in `ℚ`. In characteristic five the pure tensor `00000`
  satisfies the proper shuffle equations because the relevant multiplicities
  are 5 and 10. Every bracket column vanishes in that coordinate.

## Independent finite replay

Run the independent Python oracle from the repository root.

```sh
python3 oracles/python/c4_degree_five.py \
  --check-lean proof/PscVerif/PscVerif/Lie5Data.lean
```

The oracle builds shuffles from index masks, computes exact rational row rank,
and compares the emitted witnesses byte for byte. Lean independently checks
the identities from its own commutator and shuffle expansions. The oracle
counts scattered subwords by combinations of positions. Its modular rank
checks give 195 over fields of size 2, 3, and 7 and 192 over the field of
size 5.

| Removed hypothesis or mutated operation | Finite control |
| --- | --- |
| Degree-four balance | The third Thue–Morse blocks agree through degree three and have degree-four defect 8 at `0101`. After one substitution the degree-five defect at `00001` is −8. Applying the incidence tensor to the original degree-five defect gives 0. The original degree-five defect also fails a proper shuffle equation. |
| Correct tensor action | The fourth Thue–Morse blocks agree through degree four. For `0 → 02, 1 → 1, 2 → 2`, the action gives 32 at `00012`, agreeing with direct substitution. The transposed action gives 0 there. |
| Signed normalization | On the fourth blocks, the letter swap sends the pair to its reverse. The signed singleton column sends −8 to 8 at `00001`. An unsigned coefficient gives −8. |
| Degree-four balance of the actual children | The same pair has a proper balanced cut after two letters. Its first cut pair `01 / 10` already differs in degree two. A declaration of the whole swapped pair as one child is an algebraic example and does not model the first-cut reduction. |
| Characteristic | The pure fifth power passes the shuffle equations modulo five and lies outside the bracket span. |

These are finite adversarial controls on hypotheses and orientation. None is
evidence of a strict degree-five carrier for an irreducible Pisot substitution.

## Conditional sector calculation

The content multiplicities from the finite basis are per distinct permutation.

| Sorted content | Multiplicity |
| --- | ---: |
| (5,0,0) | 0 |
| (4,1,0) | 1 |
| (3,2,0) | 2 |
| (3,1,1) | 4 |
| (2,2,1) | 6 |

In a diagonal eigenbasis a word of content `(i,j,k)` has tensor weight
`β^i α^j γ^k`. The multiplicity table is a finite calculation. The arithmetic
comparison in `Degree5Sector` uses `b = |β| > 1`, two contracting moduli
`x,y`, and `bxy ≥ 1`. It gives `bx > 1` and excludes weights of types
`(4,1,0)`, `(3,2,0)`, and `(3,1,1)` **if** their orbit with the maximal
exponent at the Perron root occurs in the signed spectrum and that spectrum
has the Perron upper bound. Transitivity on the three roots supplies the
required placement once orbit transport to the rational image is proved.

For a unit determinant, all three placements of `(2,2,1)` lie strictly
below the bound. Their moduli are `bx`, `by`, and `xy`. Thus the
degree-four argument that forces a signed eigenvalue at the Perron modulus
has no counterpart from this bound alone. The immediate mathematical
obstruction is to exclude a nonzero realizable defect image supported on
the surviving `(2,2,1)` weights, or to derive a stronger constraint on that
image. Before applying the conditional comparison to a child system in Lean,
a degree-five diagonalization and rational quotient spectrum bridge is
required. The finite algebra leaves Concentration, G1, C4, and PSC open.

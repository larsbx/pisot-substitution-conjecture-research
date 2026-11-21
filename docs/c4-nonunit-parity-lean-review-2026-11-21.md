# Lean review of nonunit rank-two parity

Source revision `629d3c60f71817b76d479deaa6b802dc0c25a4ff`, [PR #636](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/636).

## Source decision

The target is the finite implication from the fixed-tiling count and the two-by-two
eventual range to the two possible cubics modulo two, followed by the algebraic
consequence of the signed factor identity. These are deductions from the
[original source decision](c4-nonunit-rank-two-residue-stop-go-2026-11-21.md)
and standard matrix identities. [Barge, Lemmas 13–14 and Theorems 17 and 22](https://arxiv.org/abs/1301.7094)
supplies the published twin and covering structure. The cover theorem requires
border forcing. [Barge–Diamond, Theorem 4](https://arxiv.org/abs/math/0702669)
supplies the eventual-range cohomology sequence, with connectedness and
nonsingularity needed for the particular dimension formula in the note.
[Barge–Kellendonk–Schmieding, Theorem 5](https://arxiv.org/abs/1204.1432)
supplies the torsion-free cokernel of the eigenfunction classes. In the cover
argument, equality of rational ranks is the additional reason all integral
classes on the base would come from eigenfunctions.

Proceed with an independent finite proof and a review of the geometric
interfaces. Compare with the pinned Mojo count, including the 48 specimens
whose counts are even and whose reduction has the factor `(t+1)^2`.

## Work shown

### Assumptions and hypotheses

| Lean result | Inputs |
| --- | --- |
| `even_card_fixedPoints` | A finite fixed-point type, an involution of the ambient type, freeness, and commutation with the map. For `Φⁿ` it is enough to commute with `Φ`. |
| `fixedLetters_card_zero_or_two`, `fixedSeams_card_of_complete` | Two periodic letters per endpoint map, all four legal seams, and a positive iterate. |
| `complete_range_of_edge_bound` | Ternary endpoint maps, the two injectivity implications of Theorem E, and at least as many eventual edges as vertices. |
| `fixedSeed_card`, `hull_count_of_classification` | The existing length substitution with positive lengths, nonempty images, finite alphabet, `β > 1`, and `n > 0`. The hull statement takes a bijection from fixed tilings to origin seeds. |
| `hull_parity_of_classification` | The preceding seed classifications at every positive power, complete two-by-two periodic range and a commuting free twin on the original Lean hull. |
| `charpoly_cubic`, `newton_two_three`, `all_power_traces_zero_iff` | A 3×3 matrix over a commutative ring for the identities and over `𝔽₂` for the equivalence. |
| `cube_zero_of_signed_factors` | The factorization of the characteristic polynomial of the powered reduced matrix, the signed polynomial identity and monic factors of the stipulated degrees. |

The count uses `LengthSubst` from `PeriodicPartnerHull` and the incidence
column theorem `PeriodicPartnerEvenTails.count_iterWord`. In the application irreducibility and coincidence rank enter through the
geometric results that supply the finite hypotheses.

### Derivation / reduction

#### The finite proof

1. Restrict the commuting involution to fixed points. Its permutation has
   square one and full support, so the cycle lengths are all two. The empty
   fixed set has even cardinality as well.
2. A positive iterate fixes only periodic letters, and it permutes the
   periodic set. On a two-element set the identity fixes two and the swap
   fixes zero. With every seam legal, the number of fixed seams is the
   product of the two fixed-letter counts, hence zero or four.
3. In a connected eventual range the cycle rank is `edges − vertices + 1`.
   A positive rank supplies the edge bound in Lean. The periodic sides have
   sizes `l,r ≥ 1` and there are at most `l*r` edges. The inequality
   `l+r ≤ l*r` forces both sizes to be at least two. Theorem E's implications
   then force non-injectivity. A non-injective ternary self-map has at most
   two periodic letters, so both sizes are two and all four edges occur.
4. For every `a`, count the letters `a` in `σⁿ(a)` by partitioning the
   matching positions into first, last and strictly interior. The first and
   last tests use the powers of the original endpoint maps. An image
   `σⁿ(a)=[a]` would give `βⁿℓ(a)=ℓ(a)` and is ruled out by the length
   hypotheses. Lean proves the additive identity
   `seedCount + firstFixed + lastFixed = tr(Mⁿ) + fixedSeams`. Each of the
   three correction counts is even in the square range. For any positive
   iterate, the fixed-seed count and the trace therefore have the same parity.
5. With `pᵢ = tr(Mⁱ)` and `χ_M = X³ − e₁X² + e₂X − e₃`, the proofs give
   `p₁=e₁`, `p₂=e₁²−2e₂` and `p₃=e₁³−3e₁e₂+3e₃`. Here `e₂` is the sum
   of the principal two-by-two minors and `e₃=det M`. The first and third
   trace parities give even `e₁,e₃`. Conversely, their evenness gives zero
   first and second traces over `𝔽₂`, and Cayley–Hamilton gives the recurrence
   `p_(k+3) = e₂ p_(k+1)` there. This proves the all-positive-power equivalence.
   The reduced characteristic polynomial is `X³` or `X(X+1)²`.
6. The additional input in Lemma S+ is
   `hₙ r̄ = (X+1) q̄₁`, where `hₙ` is the factor of the powered incidence
   characteristic polynomial prime to `X`. The dimensions used by the
   written argument give `deg r̄=1` and `deg q̄₁=0`. The factors are monic,
   so the reductions have the stipulated degrees. Lean gives `hₙ=1` and,
   by Cayley–Hamilton, `((M mod 2)ⁿ)³=0`. Thus the original reduction is
   nilpotent. For a 3×3 matrix this gives `χ_{M mod 2}=X³` and
   `(M mod 2)³=0`. This route needs no assertion about the order of the
   nonzero roots at the chosen power.

#### From the original legal hull to the seed type

The existing hull uses labelled tiles with half-open supports
`[x,x+ℓ(a))`. Its legality predicate requires every bounded patch to occur,
up to translation, in a supertile. `inflate_pow` and `hull_iterate_val`
identify the literal powered word placement and `inflateH^[n]`. The new
`legalSeams` tests whether two tiles abut in an original supertile.
`mem_legalSeams_of_origin` proves that an actual hull cut gives such a seam.

For the remaining bijection in Lemma N, split by the unique tile covering
zero under the half-open convention. If its left coordinate is negative,
the origin is interior. A child covering zero in the inflated tiling comes
from the unique parent covering zero. Equality of the fixed tiling and the
inflated tiling thus singles out a matching occurrence in the word of the
parent's own letter. If `u` is the prefix before the occurrence, its position
is forced to be `−ℓ(u)/(βⁿ−1)`. Positivity of tile lengths makes prefix
lengths strictly increasing. Both the prefix and suffix are nonempty exactly
when the origin lies strictly inside this seed. The one-tile seed occurs in a
level-zero supertile after translation.

If the tile at zero starts at zero, the left-hand tile ends there. To extract
it in Lean, one can use a point just to the left of zero and the positive
minimum tile length, or the existing left-neighbor interval construction.
Inflation preserves zero and the endpoints of the two adjacent parents.
The seed is the adjacent pair, with the left letter fixed by the last-letter
power and the right letter fixed by the first-letter power. An occurrence of
the pair at any common cut in a supertile supplies legality for the seed.

In both cases the positioned seed tiles an interval with zero in its interior
and is contained in its own `n`-fold inflation. The hypotheses of the existing
`LengthSubst.periodic_hull_of_seed` now have concrete witnesses. The nested
patches cover intervals obtained by multiplying both endpoints by
`β^(kn)`. These intervals exhaust the line. A fixed tiling containing the
seed contains every nested patch. Unique coverage in a tiling then forces
equality with their union. Covered intervals and seed type distinguish
interior seeds from seams and give the inverse of the extraction procedure.
The possibility of subtracting the same position twice is excluded by `iterWord_ne_singleton_self`. Primitivity, Pisot algebra and
recognizability supply context for the published dynamical results. The
literal count proof uses the expanding placement and the supertile definition
of legality.

For the eventual-range interface the seam map is
`(b,a) ↦ (g_R(b),g(a))`. Legal seams are closed under this map by inflation.
On a finite set its stable image is the periodic set. A legal edge is periodic
exactly when both endpoints are periodic, by taking a common multiple of
their periods. To identify every periodic letter with a vertex of that image,
one uses a legal neighbor on the appropriate side. Start with a legal seam
incident to the letter and take a sufficiently large multiple of its period.
Primitivity and recurrence give the legal neighbors. These are the
correspondences needed to apply `complete_range_of_edge_bound` to the
Barge–Diamond graph.

#### Original inflation, twins and the cohomological input

For the parity argument the required action is a free involution on
`Fix(Φⁿ)` for the **original** inflation. The written route first identifies
the stack relation as trivial on the original hull using the rank-free stack
rigidity lemma and dense stable equivalence. With that input, Barge's
Lemma 13 applies to the original Pisot family substitution. Its proof gives
disjointness at every inflation level. Inflation preserves maximal
equicontinuous fibres, so `Φ(ιT)` is a disjoint fibre-mate of `ΦT`.
Uniqueness in Lemma 13 gives `Φι=ιΦ`. This justifies keeping separate the
one-step commutation used for all the original counts and the positive
power used in the proper return presentation for Lemma S+. A conjugacy
that intertwines only a proper power guarantees parity on its multiples.
The repository's `LocalHull` puts the ordinary local topology on the same
underlying legal tilings and uses `inflateH` on those tilings. The
identification of this ordinary hull and its inflation with Barge's
classical hull, and the construction of the twin there, remain inputs. [Barge, Theorem 4 and Lemmas 13–14](https://arxiv.org/abs/1301.7094)

Theorem E uses the prior exclusion of strict systems through its
common-vertex contradiction. Its logical input is the result that a common
twin vertex would produce a forbidden strict system. The word-count, free
involution and Newton steps require neither of these assertions. Theorem H3,
with connectedness and the Barge–Diamond sequence for the original
nonsingular cubic, is the input giving positive eventual-range cycle rank.
The graph calculation then gives `dim H¹(Ω;ℚ) = 3 + 1 = 4`. See the
[twin endpoint argument](c4-nonunit-twin-endpoint-2026-11-21.md) and
[rank-two wall, Theorem H3](c4-rank-two-wall-2026-11-16.md#8-rank-two-is-excluded-at-dim-h1--3-theorem-h3).

For the stricter conclusion the written cover argument uses the proper
border-forcing presentation and the identification of its stack hull with
the original hull. It needs a two-sheeted cover `p:X→Y`, the maximal
equicontinuous map factoring through `p`, and the continuous odd sheet
function `z` on `X`. The even function `z²` descends to `Y`.
If `dim H¹(Y;ℚ)=3`, the rank-three eigenfunction subgroup and its
torsion-free cokernel imply that the class of this descended function
comes from an eigenfunction. Adjusting `z` by half of the resulting
continuous real logarithm produces an odd eigenfunction on `X`.
Its square is the pulled-back eigenfunction and continuity of the flow
forces the half frequency. Every continuous eigenfunction on `X` is
constant on the cover fibres because the maximal equicontinuous map
factors through the cover. This is the contradiction. The covering norm
satisfies `N p*=2`, so the lower bound `dim H¹(Y;ℚ)≥4` and the upper
bound from the square give equality and zero anti-invariant cohomology.
The ordered-pair cohomology presentation and its one removed odd line
must identify the resulting dimensions with `3+deg r` and `deg q₁`.
The Lean degree argument takes the outputs of these steps as hypotheses.
[Barge, Theorem 17](https://arxiv.org/abs/1301.7094) ·
[Barge–Kellendonk–Schmieding, Theorem 5](https://arxiv.org/abs/1204.1432) ·
[Covering argument](c4-even-stack-residue-2026-11-19.md#the-cover-requires-four-classes-on-its-base)

### Evidence and replay

The PR head `629d3c60f71817b76d479deaa6b802dc0c25a4ff` and GitHub merge
commit `bf31dfa49687748de5da998cc7c4cfbf00fa113f` have the same tree
`5ed960285f6a816941db37800b688b63a650db1c`. The source-only patch is
based on that tree. The Lean toolchain is the repository pin
`4.34.0-rc2`, with Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.
The locked Mojo compiler reports `1.1.0.dev2026090805 (34562fa1)`.

| Check | Result |
| --- | ---: |
| Labelled substitutions in the standing domain | 4,554 |
| Nonunit members | 1,926 |
| Theorem E filter | 840 |
| Tree filter | 1,362 |
| Union of endpoint and tree filters | 1,794 |
| At least one odd fixed count at powers 1 through 8 | 1,338 |
| Beyond the endpoint and tree filters | 132 |
| With parity as well | 72 |
| With `χ mod 2 = X(X+1)²` | 48 |
| With `χ mod 2 = X³` | 24 |

The unmodified Mojo regression and census pass. The Python oracle enumerates
the committed Python reference domain, replays 15,408 word-count and
trace comparisons through power eight, and matches all 72 labelled Mojo
survivors by substitution words and the three integer cubic coefficients.
All nonunit corpus determinants are even. The 24 nilpotent cases match
the earlier original square shape filter by specimen, and the earlier Mojo
shape regression supplies its `224:24` receipt. Within the final 24
there are twelve with `(e₁,e₂,e₃)=(2,0,2)` and twelve with `(4,4,2)`.
The JSON receipt lists each triple of words and its eight counts.

The separate Mojo productivity replay passes on exactly those 24 and
reports a largest graph of 31,441 states with zero caps. The box-productivity
criterion and the imported link to overlap coincidence give the prior
pure-discrete classification. The parity calculation is independent of
this spectral evidence. [Box-automaton certificate and its imports](pds-certificate-from-the-box-automaton-2026-10-07.md)

With `REVIEW_DIR` set to the absolute path of the extracted verification
directory, replay from a checkout with the proposed patch applied:

```sh
(cd proof/PscVerif && lake --wfail build PscVerif.PeriodicPartnerFixedPointParity PscVerif.PeriodicPartnerFixedPointHull)
(cd proof/PscVerif && lake env lean "$REVIEW_DIR/FixedPointParityAudit.lean")
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_twin_fixed_points.mojo)
(cd kernel && pixi run --locked mojo run -I . nonunit_residue_census.mojo) > mojo-residue-census.log
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_even_stack_residue.mojo)
(cd kernel && pixi run --locked mojo run -I . "$REVIEW_DIR/residue_productivity.mojo") > mojo-residue-productivity.log
python3 oracles/python/c4_fixed_point_parity.py --mojo-census mojo-residue-census.log \
  --mojo-productivity mojo-residue-productivity.log
python3 tools/make_proof_bank.py --check
git diff --check
```

The scoped local builds passed with warnings treated as errors. The axiom
audit reached all 24 named source proofs and inspected 65 compiled
declarations, including generated helpers, with only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The patch registers both
modules in the hosted periodic-partner workflow. Hosted CI awaits
publication.

### Negative controls

- The endpoint map `(1,0,0)` fixes three letters at power zero, zero at
  power one and two at power two. A pair of endpoint maps with two fixed
  letters and only three legal seams can have an odd fixed seam count.
  Lean compiles both checks.
- A singleton self-image would be counted once on the diagonal and removed
  twice in the endpoint subtraction. The expanding length equation is
  the guard against this input.
- **Odd determinant outside the standing corpus.** For `1/1222/2011`
  the periodic sides are both `{1,2}`. The first letters fix that pair and
  the last letters swap it. The words `11,12,22` occur within images and
  `21` follows by applying the seam map to `11`, so the range is a
  square. Its incidence has rows `(0,0,1),(1,1,2),(0,3,1)`.
  The cubic is `X³−2X²−5X−3` with no integer root among `±1,±3`.
  Its discriminant is `−279` and its Perron root is in `(3,4)`, so its
  two nonreal conjugates have modulus `sqrt(3/β)<1`. The matrix is
  primitive. Lean checks the determinant and first three traces
  `2,14,47`. The exact word counts are `0,14,45`. An even first count is
  compatible with an odd determinant, so power three matters.
- **Even counts with the other cubic.** The matrix `diag(1,1,0)` over
  `𝔽₂` has zero traces at all positive powers and nonzero cube, checked
  in Lean. The actual corpus word triple `1/122/201` has
  `(e₁,e₂,e₃)=(2,−1,2)` and starts with counts `0,6,18`.
  All 48 such cases survive the finite parity step.
- **Only a powered action.** Over `𝔽₂`, the direct sum of the zero
  scalar and a companion matrix of `X²+X+1` has trace one. Its third
  power is a rank-two projection and all positive powers of that
  projection have trace zero. Thus parity at multiples of three cannot
  alone recover the original trace.
- Thue–Morse has a free letter exchange and even counts at every checked
  power. Tribonacci has counts `0,2,6` and lies in the unit-determinant
  branch. Both are controls for the scope of the rank-two application.

### Non-claims / remaining gaps

The Lean hull classification currently requires the actual seed equivalence.
The natural next formalization is to extract the seed at zero and prove
uniqueness of its nested legal extension, using the existing growing-seed
lemma for existence. To obtain Theorem R from the standing geometric
hypotheses requires the original-hull twin construction, the identification
of the graph and cohomology actions, Theorems E and H3, and the signed factor
and dimension inputs from Lemma S+ and the covering argument. The finite
calculation proves a necessary-condition reduction. The geometric
obligation to rule out rank two in the square nilpotent residue for
unbounded image lengths remains open.

# Irreducible distinct binomially equivalent pairs: exact census and minimal lengths — 2026-11-07

**Status:** exact finite computation on a stated window (ternary `n ≤ 12`,
with the extension `n = 13, 14`; binary `n ≤ 20`). Canonical Mojo:
`kernel/psc/binomial_pairs.mojo` (kernel), `kernel/binomial_pair_census.mojo`
(driver), pinned by `kernel/tests/test_binomial_pair_census.mojo`, which ends
with `require_contract` (no ledger claim is targeted, added or moved). An
independent stdlib oracle, `oracles/python/binomial_pair_census.py`, is run
by `tests/test_binomial_pair_census_oracle.py`. This is experiment A of the
[stop/go gate](c4-solidify-stop-go-2026-11-07.md), run as its §0 and §3.6
decided: binary only as a calibration, ternary for `k = 2, 3` with `n ≤ 12`,
the four scratch items of §3.6, the controls of §3.5.

Notation follows the gate and the manuscript
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex` (`def:balanced`; the
defects `K_r` of `thm:defect-intertwiner`). `N_r(w)` is the vector of
scattered-subword counts of length `r`, `K_r(u, v) = N_r(u) − N_r(v)`,
`u ∼_k v` means `K_1 = … = K_k = 0`, and the *first defect degree* of a
balanced pair is the least `r ≥ 2` with `K_r ≠ 0`.

## Results at a glance

- **Ternary minimal lengths** (gate item (i)). The shortest irreducible
  distinct ternary pairs with `K₂ = 0` have length **7**; the shortest with
  `K₁ = K₂ = K₃ = 0` have length **12**. No irreducible ternary pair with
  `K₁ = … = K₄ = 0` exists for `n ≤ 14`.
- **Length 7** (item (ii)). There are exactly **6** unordered irreducible
  `K₂ = 0` pairs, and they are exactly the six pairs of `kernel/psc/seeds.mojo`.
  They form **one** orbit under relabelling × swap, and also one under
  `G = S₃ × ⟨reversal⟩ × ⟨swap⟩`. So the attack note's "six classes" counts
  the six normalised pairs, and the defect-degree note's "one six-element
  relabelling orbit" is the right reading.
- **Length 12** (item (iii)). There are exactly **12** unordered irreducible
  `∼₃` pairs. All have `K₄ ≠ 0`, so none is `∼₄`. They form one `G`-orbit,
  whose least element is `w4Pair = (011220100112, 120010112201)`. This is also
  `DEGREE4_STATE` of `tests/test_multidegree_sieve.py`. Under relabelling ×
  swap alone they form two orbits, and reversal joins them.
- **Lengths 12, 13, 14** (item (iv)). The irreducible `∼₃` pairs number
  **12, 24, 6**, and all have `K₄ ≠ 0`. This is the scratch figure 12/24/6,
  reproduced exactly. Their `G`-orbits have sizes `{12}`, `{12, 6, 6}` and
  `{6}`.
- **Binary calibration.**
  - The census reproduces the closed form: `2·C_{n−1}` ordered irreducible
    pairs for `2 ≤ n ≤ 20`.
  - It finds no irreducible pair with `K₂ = 0` for `n ≤ 20`, as the theorem
    `binary_no_equiv2` requires.
  - Its binary class counts equal Table I of Chrisnata et al.: `D_3(n)` for
    `3 ≤ n ≤ 20` and `D_4(n)` for `4 ≤ n ≤ 20`.

**What this certifies.** It is the pinned exhaustive enumeration behind two
repository statements that had none.
1. **The minimality remark withdrawn from the Lean control `w4Pair`**
   (`proof/PscVerif/PscVerif/Defect4.lean`; side-notes ledger, 2026-11-06 Lean
   entry, "Caught in review").
   - Over the alphabet `{0,1,2}`, no distinct irreducible 3-binomially
     equivalent pair has length `≤ 11`.
   - At length 12 there are exactly 12 such unordered pairs, and `w4Pair` is
     one of them.
   - So `w4Pair` has the least possible length. This covers alphabets of at
     most three letters, since binary pairs are the sub-census of words
     avoiding `2`.
   - The remark is restored at integration, citing this census: the `w4`
     control bullet of the `Psc.Defect4` docstring (a finite computation, not a
     Lean statement).
2. **The length-12 calibration of `tests/test_multidegree_sieve.py`.** Its
   `DEGREE4_STATE` is commented "found by exhaustive enumeration", an
   enumeration that was not in the repository. The census reproduces that
   enumeration:
   - the state is one of exactly 12 irreducible `∼₃` pairs at length 12;
   - none exists at a shorter length;
   - its first defect degree is 4, which agrees with that test's
     `lowest_nonzero_defect_degree == 4` and `coincidence_boundaries == [0, 12]`.

## 1. Assumptions and hypotheses

**The finite object.** For `d ∈ {2, 3}` and a length `n ≥ 1`, the census
counts the set `P(d, n)` of unordered pairs `{u, v}` with:
- `u, v` words over `{0, …, d−1}`;
- `u ≠ v` and `|u| = |v| = n`;
- `p(u) = p(v)`, where `p` is the Parikh vector, i.e. `K₁ = 0`;
- irreducibility: `p(u[0,j)) ≠ p(v[0,j))` for every `0 < j < n`.

It counts `P(d, n)` by first defect degree `2`, `3`, `4` and `5+`. The class
`5+` (`DEGREE_FIVE_PLUS` of `psc/defect_degree.mojo`) means
`K₂ = K₃ = K₄ = 0`. It is never relabelled as 5 (gate §3.4). The quantifiers
are "for every `n` in the window", and nothing beyond it:
- ternary: `n = 1..12`, and the extension `n = 13, 14`;
- binary: `n = 1..20`.

Binary words are the sub-census of words over `{0,1,2}` that avoid `2`. They
use the same alphabet-3 kernels, not a second kernel (gate §3.6).

**Imported, and used only as calibration targets, never as inputs.**
- *Table I of J. Chrisnata, H. M. Kiah, S. Rao, A. Vardy, E. Yaakobi,
  H. Yao, "On the number of distinct k-decks: enumeration and bounds",
  ISCIT 2019.* It gives `D_3(n)` for `3 ≤ n ≤ 20` and `D_4(n)` for
  `4 ≤ n ≤ 20`. The values are transcribed in `table_i_d3`, `table_i_d4`, from
  the paper text read for the gate (scratch `wf9/lit/nsf/10191056.txt`).
- *The deck lemma.* For `n ≥ k` the `k`-deck (the multiset of length-`k`
  subsequences, i.e. `N_k`) determines `N_1, …, N_{k−1}`. So `D_k(n)` is the
  number of `(N_1, …, N_k)` classes. It is standard, and is reported by Golm,
  Nahvi, Gabrys and Milenkovic, arXiv:2201.12671, §I. It is used only to read
  the table.
- *`S(2), S(3), S(4) = 4, 7, 12`.* These are the least lengths with two
  distinct `∼_k` words. They are reported only as a consistency line, as the
  gate §3.4 allows.
- *`Psc.PrimitiveExpansion.binary_no_equiv2`.* This is Lean, standard axioms:
  no binary irreducible pair has `K₂ = 0`. The census computes this count
  instead of assuming it, and a nonzero value aborts the run.
- *The binary closed form `2·C_{n−1}`.* This is gate §3.3 (b), a written
  derivation via bicoloured Motzkin paths. It is checked, not used.

**Machine arithmetic.** Counts are 64-bit `Int`. Every addition and
multiplication in the lattice-walk recurrence, the Catalan recurrence, the
word count `dⁿ` and `scattered_count` goes through
`finite_exact.checked_int`, which raises on overflow. The walk counts are
bounded by `9ⁿ < 2⁶³` for `n ≤ 19`, so the window is far inside the range.
No floating point is used.

**Hypotheses that do not transfer.** The census is about words, not about a
substitution:
- nothing here involves `σ`, the balanced-pair algorithm, the PIP corpus or
  a strict component;
- the census-library rule about walking `pip_corpus()` does not apply
  (gate §3.6), since the domain is the finite set of equal-length word
  pairs.

## 2. Derivation / reduction

**(a) The pairs with `K₂ = 0`.** For a pair of distinct words, `K₂ = 0` and
`K₁ = 0` hold exactly when they lie in one `(N₁, N₂)` class.
- The kernel lists the words of each Parikh vector in lexicographic order,
  with the multiset next-permutation step (`class_words`).
- It sorts their `N₂` rows (`psc.words.n2`) by a stable merge sort on indices
  (`sorted_row_order`), and takes the runs of equal rows.
- It then tests every pair inside a run. So every irreducible `K₂ = 0` pair
  is examined, and no other pair is.

Two elementary cuts skip pairs before the full test. Neither changes the
set:
- equal first letters make the length-1 prefixes balanced, a cut at 1;
- equal last letters, together with `p(u) = p(v)`, make the length-`(n−1)`
  prefixes balanced, a cut at `n − 1`.

Irreducibility is tested on prefix Parikh codes `c₀(n+1) + c₁`, where the
third coordinate is `j − c₀ − c₁`. Every pair kept is then re-tested with the
library predicate. That predicate requires `psc.bpa.coincidence_boundaries`
to equal `[0, n]`, together with `psc.words.is_balanced`.

**(b) Degree among the `K₂ = 0` pairs.** Each kept pair is classified by
`psc.defect_degree.first_defect_degree`, which streams `N₂`, `N₃` and `N₄`.
The result is cross-checked against an independent route: the
`(N₁, N₂, N₃)` and `(N₁, …, N₄)` sub-classes of the same sort, built from
the rows `psc.words.n3` and `psc.defect_degree.n4`.
- A pair in different `N₃` sub-classes must have degree 3.
- A pair in the same `N₃` sub-class but different `N₄` sub-classes must have
  degree 4.
- Any other pair must have degree `5+`.

A disagreement raises, and so does a degree of 2 inside an `(N₁, N₂)` class.

**(c) The total, and the degree-2 count.** A pair `(u, v)` of length `n` is
the walk `d_j = p(u[0,j)) − p(v[0,j))` on the zero-sum lattice.
- Each letter pair `(a, b)` gives one step `e_a − e_b`: `d` zero steps and
  `d(d−1)` unit steps.
- The pair is balanced iff `d_n = 0`.
- It is irreducible iff in addition `d_j ≠ 0` for `0 < j < n`.

`irreducible_ordered_pairs` runs this first-return recurrence on the box
`|d₀|, |d₁| ≤ n`. A step outside the box raises.
- For `n ≥ 2`, the condition at `j = 1` excludes `u = v`. At `n = 1` every
  balanced pair is a coincidence, so the count is 0.
- The swap `(u, v) ↦ (v, u)` is a fixed-point-free involution on the ordered
  pairs, so the ordered count is even and the unordered count is half of it.
  An odd count raises.
- The degree-2 count is the total minus the enumerated `K₂ = 0` count. A
  negative difference raises.

**(d) Symmetry classes.** `G = S₃ × ⟨reversal⟩ × ⟨swap⟩` maps `P(3, n)` to
itself and preserves the first defect degree:
- relabelling and swap are clear;
- reversal preserves balance;
- it maps balanced prefixes to balanced suffixes, and a balanced suffix of
  length `j` is the complement of a balanced prefix of length `n − j`;
- `N_x(rev w) = N_{rev x}(w)`.

The class of a pair is named by its least element. That element is the lesser
of `psc.symmetry.canonical_pair` of the pair and of its reversal
(`g_canonical`). `orbit_representatives(…, False)` gives the classes under
relabelling × swap alone.

**(e) Class counts and Table I.** The number of runs of the `N₂`, `N₃` and
`N₄` sorts is the number of `(N₁, N₂)`, `(N₁..N₃)` and `(N₁..N₄)` classes of
words. On binary words of length `n ≥ k`, the deck lemma makes the last two
equal to `D_3(n)` and `D_4(n)`. This is the gate's calibration (ii), "by
bucketing without the irreducibility filter".

**Cost.** The cost is `O(dⁿ · n · 3⁴)` for the rows. On top of that come the
pair tests inside classes: 1,652,286 candidate pairs at `(3, 12)`, and
296,298,324 at `(2, 20)`.

## 3. Evidence and replay

**Commands** (from `kernel/`, with Mojo 1.1.0.dev2026090805 as pinned by
`pixi.lock`).

```
pixi run --locked mojo run -I . binomial_pair_census.mojo          # window: d=3 n<=12, d=2 n<=20  (~32 s)
pixi run --locked mojo run -I . binomial_pair_census.mojo 14 20    # extension: d=3 n<=14          (~74 s)
pixi run --locked mojo run -I . -I tests tests/test_binomial_pair_census.mojo   # regression     (~51 s)
```

From the repository root:

```
python3 -m pytest -q tests/test_binomial_pair_census_oracle.py     # oracle: d=3 n<=9, d=2 n<=14 (~11 s)
python3 oracles/python/binomial_pair_census.py 3 12 10             # manual oracle replay d=3 n=10..12 (~43 s)
```

The times are wall-clock on the session machine. They are not part of any
contract. The driver's output is deterministic: the `ROW`, `MINIMAL`, `ITEM`,
`LIST`, `GCLASS`, `PINNED`, `CALIBRATION`, `IMPORT` and `CONTROL` lines are
the replay target.

**Caps and the window.** The window bounds are the only bounds; inside the
window nothing is capped.
- Beyond the window the driver prints `NOT_ENUMERATED`, never zero.
  `minimal_length` returns `none_for_n<=N`, labelled "not a statement beyond
  the window".
- The extension (`TERNARY_MAX` 13 or 14) counts the degree-3 pairs of
  `n ≥ 13` without keeping them. Their `G`-classes are printed as `not_kept`,
  and asking for them raises (`pairs_of_degree`).
- `TERNARY_MAX > 14` and `BINARY_MAX > 20` are refused.

**Fail-closed behaviour** (refuse to conclude; gate §3.5). Each of the
following raises and aborts the run:
- an alphabet outside `{2, 3}`, or `n < 1`;
- a Parikh vector with a negative entry, or a letter outside `0..2`;
- a ragged row table;
- class members out of lexicographic order;
- a prefix-code verdict that `coincidence_boundaries` contradicts;
- a degree of 2 inside an `(N₁, N₂)` class, or a degree disagreeing with
  the sub-class sort;
- a word count other than `dⁿ`;
- an odd ordered total, or a negative degree-2 count;
- a lattice step outside its box;
- a checked-arithmetic overflow;
- a histogram key outside `psc/histogram.mojo`'s capacity;
- in the driver, any binary calibration disagreement: the closed form, a
  nonzero `K₂ = 0` count, Table I `D_3`, or Table I `D_4`.

The regression test pins every count below. Any change fails it.

**The table.** Unordered pairs throughout; the ordered counts are twice
these. The "irreducible pairs" column is `|P(d, n)|`. `G`-classes are
counted among the pairs of that degree.

Ternary (`d = 3`). Rows 13 and 14 are the extension: the test pins row 13,
and row 14 is recorded here from the extension run.

| `n` | words | `(N₁,N₂)` classes | `(N₁..N₃)` classes | `(N₁..N₄)` classes | irreducible pairs | degree 2 | degree 3 | degree 4 | 5+ | `G`-classes 3 / 4 / 5+ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 1 | 3 | 3 | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0 / 0 / 0 |
| 2 | 9 | 9 | 9 | 9 | 3 | 3 | 0 | 0 | 0 | 0 / 0 / 0 |
| 3 | 27 | 27 | 27 | 27 | 15 | 15 | 0 | 0 | 0 | 0 / 0 / 0 |
| 4 | 81 | 78 | 81 | 81 | 90 | 90 | 0 | 0 | 0 | 0 / 0 / 0 |
| 5 | 243 | 216 | 243 | 243 | 594 | 594 | 0 | 0 | 0 | 0 / 0 / 0 |
| 6 | 729 | 568 | 729 | 729 | 4161 | 4161 | 0 | 0 | 0 | 0 / 0 / 0 |
| 7 | 2187 | 1410 | 2181 | 2187 | 30357 | 30351 | 6 | 0 | 0 | 1 / 0 / 0 |
| 8 | 6561 | 3309 | 6522 | 6561 | 228087 | 228063 | 24 | 0 | 0 | 2 / 0 / 0 |
| 9 | 19683 | 7307 | 19482 | 19683 | 1752315 | 1752117 | 198 | 0 | 0 | 19 / 0 / 0 |
| 10 | 59049 | 15303 | 58152 | 59049 | 13699053 | 13697823 | 1230 | 0 | 0 | 105 / 0 / 0 |
| 11 | 177147 | 30435 | 173340 | 177147 | 108604737 | 108597093 | 7644 | 0 | 0 | 662 / 0 / 0 |
| 12 | 531441 | 57882 | 516279 | 531429 | 870958746 | 870908340 | 50394 | 12 | 0 | 4215 / 1 / 0 |
| 13 | 1594323 | 105468 | 1535652 | 1594251 | 7052051538 | 7051728264 | 323250 | 24 | 0 | not kept / 3 / 0 |
| 14 | 4782969 | 185214 | 4563195 | 4782621 | 57566222343 | 57564053691 | 2168646 | 6 | 0 | not kept / 1 / 0 |

Binary (`d = 2`): the calibration rows. The `(N₁..N₃)` and `(N₁..N₄)`
columns are Table I's `D_3(n)` (`n ≥ 3`) and `D_4(n)` (`n ≥ 4`). The
irreducible column is `C_{n−1}`, i.e. `2·C_{n−1}` ordered.

| `n` | words | `(N₁,N₂)` classes | `(N₁..N₃)` classes | `(N₁..N₄)` classes | irreducible pairs | degree 2 | degree 3 | degree 4 | 5+ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 2 | 2 | 2 | 0 | 0 | 0 | 0 | 0 |
| 2 | 4 | 4 | 4 | 4 | 1 | 1 | 0 | 0 | 0 |
| 3 | 8 | 8 | 8 | 8 | 2 | 2 | 0 | 0 | 0 |
| 4 | 16 | 15 | 16 | 16 | 5 | 5 | 0 | 0 | 0 |
| 5 | 32 | 26 | 32 | 32 | 14 | 14 | 0 | 0 | 0 |
| 6 | 64 | 42 | 64 | 64 | 42 | 42 | 0 | 0 | 0 |
| 7 | 128 | 64 | 126 | 128 | 132 | 132 | 0 | 0 | 0 |
| 8 | 256 | 93 | 247 | 256 | 429 | 429 | 0 | 0 | 0 |
| 9 | 512 | 130 | 480 | 512 | 1430 | 1430 | 0 | 0 | 0 |
| 10 | 1024 | 176 | 926 | 1024 | 4862 | 4862 | 0 | 0 | 0 |
| 11 | 2048 | 232 | 1764 | 2048 | 16796 | 16796 | 0 | 0 | 0 |
| 12 | 4096 | 299 | 3337 | 4092 | 58786 | 58786 | 0 | 0 | 0 |
| 13 | 8192 | 378 | 6208 | 8176 | 208012 | 208012 | 0 | 0 | 0 |
| 14 | 16384 | 470 | 11408 | 16328 | 742900 | 742900 | 0 | 0 | 0 |
| 15 | 32768 | 576 | 20608 | 32604 | 2674440 | 2674440 | 0 | 0 | 0 |
| 16 | 65536 | 697 | 36649 | 65075 | 9694845 | 9694845 | 0 | 0 | 0 |
| 17 | 131072 | 834 | 63976 | 129824 | 35357670 | 35357670 | 0 | 0 | 0 |
| 18 | 262144 | 988 | 109866 | 258906 | 129644790 | 129644790 | 0 | 0 | 0 |
| 19 | 524288 | 1160 | 185012 | 516168 | 477638700 | 477638700 | 0 | 0 | 0 |
| 20 | 1048576 | 1351 | 306285 | 1028448 | 1767263190 | 1767263190 | 0 | 0 | 0 |

**Minimal length of each first defect degree** in the window:

| degree | ternary | binary |
| --- | --- | --- |
| 2 | 2 | 2 |
| 3 | 7 | none for `n ≤ 20` (and none at any length: `binary_no_equiv2`) |
| 4 | 12 | none for `n ≤ 20` (same theorem) |
| 5+ | none for `n ≤ 14` | none for `n ≤ 20` (same theorem) |

**The listed pairs** (each as `u|v`, with `u` lexicographically first).

`n = 7`, degree 3: one orbit, of size 6, with least element `0112201|1200112`
(`wTPair`).

```
1220012|2011220   0221102|2100221   1022110|2110021
0112201|1200112   0211002|1002210   0122001|2001120
```

`n = 12`, degree 4: one `G`-orbit, of size 12, with least element
`011220100112|120010112201` (`w4Pair`, `DEGREE4_STATE`).

```
122001211220|201121220012   022112100221|210022121102   102212110021|211002122110
011221200112|120011212201   122002011220|201122020012   022110200221|210020221102
102211010021|211001022110   011220100112|120010112201   021100202210|100220211002
012202001120|200112022001   021101002210|100221011002   012200101120|200110122001
```

`n = 13`, degree 4: three orbits, by least element and size:
- `0012220001102|2000110222001`, size 12;
- `0112201110021|1200111022110`, size 6;
- `0112202110021|1200112022110`, size 6.

`n = 14`, degree 4: one orbit, `01122021110012|21001112022110`, size 6.

**Independent replay** (`oracles/python/binomial_pair_census.py`; stdlib,
shares no code with the Mojo kernel). It uses different methods:
- `N_r` from `itertools.combinations`;
- the total from the renewal identity `W(n) = Σ_{k=1}^{n} F(k)·W(n−k)`,
  with `W(n) = Σ_c multinomial(n; c)²`;
- grouping by `(Parikh, N₂)` in a dictionary.

The pytest runs it for `d = 3, n ≤ 9` and `d = 2, n ≤ 14`. It checks the
following:
- the degree counts of the table;
- the renewal total against brute force (`d = 3, n ≤ 6`; `d = 2, n ≤ 10`);
- the binary closed form for `n ≤ 20`;
- the class counts at `(3, 4), (3, 7), (3, 8), (2, 7), (2, 8), (2, 12)`,
  with Table I at the binary ones;
- the length-7 list against the six seeds;
- the negative controls.

The manual replay `python3 oracles/python/binomial_pair_census.py 3 12 10`
printed, in about 43 s:

```
{'n': 10, 'total': 13699053, 'degree2': 13697823, 'degree3': 1230, 'degree4': 0, 'degree5plus': 0, 'degree4_pairs': []}
{'n': 11, 'total': 108604737, 'degree2': 108597093, 'degree3': 7644, 'degree4': 0, 'degree5plus': 0, 'degree4_pairs': []}
{'n': 12, 'total': 870958746, 'degree2': 870908340, 'degree3': 50394, 'degree4': 12, 'degree5plus': 0, 'degree4_pairs': ['011220100112|120010112201', '011221200112|120011212201', '012200101120|200110122001', '012202001120|200112022001', '021100202210|100220211002', '021101002210|100221011002', '022110200221|210020221102', '022112100221|210022121102', '102211010021|211001022110', '102212110021|211002122110', '122001211220|201121220012', '122002011220|201122020012']}
```

So the whole ternary window `n ≤ 12` agrees in two languages and by two
methods, including the twelve length-12 pairs. The extension rows `n = 13, 14`
are Mojo only.

**Addendum 2026-11-09 (partial replay of rows 13 and 14).** The oracle of
experiment B, `oracles/python/c4_closed_component_search.py`, is stdlib
Python and shares no code with this kernel. It rebuilds the normalised
irreducible `K₂ = 0` pairs by grouping all words by `(Parikh, N_ab)` in a
dictionary. `python3 -I oracles/python/c4_closed_component_search.py universe 14`
printed, in 1 min 40 s:

```
{"7": 6, "8": 24, "9": 198, "10": 1230, "11": 7644, "12": 50406, "13": 323274, "14": 2168652}
```

These equal degree 3 + degree 4 of rows 7..14 of the ternary table, where
degree 5+ is 0 (`50,394 + 12`, `323,250 + 24`, `2,168,646 + 6` at
`n = 12, 13, 14`). So the
`K₂ = 0` totals of the extension rows now have an independent replay. The
split between degree 3 and degree 4 at `n = 13, 14` does not, since that
oracle computes no `K₃` or `K₄`. Locator:
[closed-component search](c4-closed-component-search-2026-11-07.md) §1.

**The four scratch items of gate §3.6, decided.**
- (i) The minima are 7 and 12. Confirmed.
- (ii) The length-7 list is exactly the six seeds: one orbit, both under
  relabelling × swap and under `G`. The "six classes" of the attack note (§4,
  "Windows") counts normalised pairs.
- (iii) There are 12 pairs at length 12, all with `K₄ ≠ 0`, and no
  irreducible length-12 pair is `∼₄`. The gate allowed a `∼₄` pair a priori,
  since `S(4) = 12`.
- (iv) The counts 12/24/6 at `n = 12/13/14` are confirmed, all with
  `K₄ ≠ 0`. The drop from 24 to 6 is now an exact count.

**Consistency with the imports.**
- The least `n` with fewer `(N₁..N_r)` classes than words, for
  `r = 2, 3, 4`, is `4, 7, 12` on binary and on ternary words. That is
  `S(2), S(3), S(4)`, as imported. The driver prints `IMPORT … consistent`.
- Every pair in the ternary window has first defect degree at most 5, as the
  import predicts (gate §3.4). The census sees no irreducible `5+` pair at
  all for `n ≤ 14`.

**Finite observations** (by-products, not calibrated against any source).
- The ternary minima 7 and 12 equal `S(3)` and `S(4)`. No mechanism for this
  is known, and it is recorded only as an observation (gate §3.4).
- At `n = 12` the ternary `(N₁..N₄)` classes number `3¹² − 12`. The binary
  collapse `2¹² − D_4(12) = 4` occurs on each of the three two-letter
  sub-alphabets. A `∼₄` class shares its Parikh vector, so it cannot mix
  words of different letter supports. Hence no two distinct length-12 words
  that use all three letters are `∼₄`.
- The ternary class counts `(N₁..N₃)`, `(N₁..N₄)` for `n ≥ 5` are exact
  counts. They are not compared with any source.

## 4. Negative controls

All are pinned by `kernel/tests/test_binomial_pair_census.mojo`; the driver
prints them as `CONTROL` lines.
- **Positive control of the degree classifier** (Ochsenschläger; LLR Lemma
  30). The Thue–Morse blocks `(φ^k(0), φ^k(1))`, `k = 1..4`, have first
  defect degree `2, 3, 4, 5+`.
  - At `k = 4` the kernel stops at `5+`. The degree-five coordinate
    `K₅_{01010} = 64 ≠ 0` (by `scattered_count`) shows the degree is exactly
    5 there.
  - `scattered_count` itself is pinned against `n2`, `n3` and `n4` on a test
    word.
- **Negative controls of the irreducibility filter.**
  - The Thue–Morse blocks for `k ≥ 2` are reducible. Only `k = 1`, `(01, 10)`,
    is irreducible, and it has degree 2.
  - The `S(2)` witness `(0110, 1001)` has degree 3 and boundaries `0, 2, 4`.
  - The `S(3)` witness `(0110001, 1000110)` has degree 4 and boundaries
    `0, 2, 5, 7`.
  - The commutation pair `(xy, yx)` with `x = 012 ∼₁ y = 120`, i.e.
    `(012120, 120012)`, has degree 3 and boundaries `0, 3, 6`.
  - All three are rejected as reducible.
- **Controls of the kernel's two routes.**
  - The lattice-walk total agrees with a brute-force count by
    `is_irreducible_pair` over all balanced pairs: `d = 3, n ≤ 7` and
    `d = 2, n ≤ 12`.
  - The prefix-code test agrees with `coincidence_boundaries` on every
    ordered pair in every ternary Parikh class with `n ≤ 6`.
  - The stable row sort is checked on a table with ties.
  - Inside every run, the degree from `first_defect_degree` must agree with
    the `N₃`/`N₄` sub-class sort.
- **Fail-closed refusals** (pinned):
  - an alphabet of size 4;
  - `n = 0`;
  - the closed form at `n = 1`;
  - a negative Parikh entry;
  - a letter `3`;
  - listing the uncounted-degree pairs of an extension row.

## 5. Non-claims / remaining gaps

- **No statement beyond the window.** The census says nothing about ternary
  `n ≥ 15` or binary `n ≥ 21`, which are `NOT_ENUMERATED`. For binary, the
  zero count of `K₂ = 0` irreducible pairs at every length comes from the
  Lean theorem `binary_no_equiv2`, and the closed form at every length from
  gate §3.3 (b). The census checks both only for `n ≤ 20`.
- **Not relabelled.** `5+` is not relabelled as 5. "None for `n ≤ 14`" is not
  a claim that irreducible ternary `∼₄` pairs never exist. Longer ones are
  not tested here.
- **No novelty for unrestricted minimal lengths.** Those are the `k`-deck
  numbers `S(k)`. Only the irreducibility specialisation (ternary minima 7
  and 12, and the counts) is new relative to the sources the gate read.
- **The oracle's reach.** The CI oracle covers `d = 3, n ≤ 9` and
  `d = 2, n ≤ 14`. The ternary rows `n = 10..12` were replayed once by hand
  (output above). The extension rows `n = 13, 14` have no independent
  replay; the scratch figures 24/6 from an earlier session agree with them,
  but those figures are not evidence. (2026-11-09: their `K₂ = 0` totals,
  degree 3 + degree 4, now have one; the 24/6 degree-4 counts still do not.
  See the addendum under "Independent replay".)
- **The `n = 14` row is not pinned** by the regression test, to keep it
  under about two minutes. It is recorded here from the extension run.
- **The symmetry classes of degree-3 pairs** at `n = 13, 14` (323,250 and
  2,168,646 pairs) are not computed.
- **Nothing about substitutions.** Nothing here is about a substitution, the
  balanced-pair algorithm, a strict component, the PIP corpus,
  Concentration, combinatorial Concentration, (H), C4 or PSC.
- **Experiment B is not run here.** The window search of gate §4.6 needs the
  complete list `P_L` of irreducible `K₂ = 0` pairs of length `≤ L`.
  `census_length(3, n)` produces it, with `kept_from = DEGREE_THREE`, for
  every `n` up to 14; this note does not use it.
- **No promotion.** No ledger claim is added or promoted. Promotion to a
  finite-domain claim would go through `tools/make_ledger.py` and
  `claim_governance.toml`, and is not proposed here.
- **The Lean remark is restored as a citation only.** At integration the
  `Psc.Defect4` docstring cites this census for the minimality of `w4Pair`; the
  minimality is not a Lean statement. Citing the census in
  `test_multidegree_sieve.py` remains a proposed edit, not made.

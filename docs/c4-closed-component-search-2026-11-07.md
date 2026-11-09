# C4 off the PIP corpus: the `K₂ = 0` window search for strict systems — 2026-11-07

**Status:** exploratory window search, exact and labelled (AGENTS.md
"exploratory searches"); its outputs are window observations, never
verdicts, except where a strong-coincidence witness decides. Canonical Mojo:
`kernel/psc/closed_component_search.mojo` (kernel),
`kernel/c4_closed_component_search.mojo` (driver), pinned by
`kernel/tests/test_c4_closed_component_search.mojo`, which ends with
`require_contract` (no ledger claim is targeted, added or moved). Independent
stdlib oracle: `oracles/python/c4_closed_component_search.py`, run by
`tests/test_c4_closed_component_search_oracle.py`. This is experiment B of
the [stop/go gate](c4-solidify-stop-go-2026-11-07.md), run as its §0, §4.6
and §4.7 decided: fused with experiment A
([binomial-pair census](c4-binomial-minimal-pairs-2026-11-07.md)), whose
complete `K₂ = 0` list it consumes. Nothing here changes C4, (H), (N0), BH
(#139), A1′ (#138), G1 or PSC. Human review pending.

**Revision 2026-11-09 (after review).** The scope of the reproduction of the
scratch window is stated exactly: the non-PIP part only (§3.3, §5). An
`L = 11` endpoint pass is now logged (§3.4). Every consistency-violation name
now fires on a positive control, and the find path (`emit_component`) is
exercised (§4). An `L = 13` stride-21 slice is pinned and replayed whole by
the oracle (§3.5). The oracle's `P_14` sizes are recorded as an independent
replay of A's `K₂ = 0` totals for `n = 12..14` (§1). The completeness check
of `P_L` and the dependence of 870 verdicts on Lemma 4 are worded exactly
(§1, §3.2, §5). The root count is cross-checked against the Routh count of
`psc.pisot_screen` (§4). No figure of the first version changed.

Notation is the gate's: `K_r(u,v) = N_r(u) − N_r(v)`, a pair is
*irreducible* if `|u| = |v| = n`, `p(u) = p(v)` and `p(u[0,j)) ≠ p(v[0,j))`
for `0 < j < n`; R2, R3, R3′, Corollary B and `r(C)` are those of the
[general-structure note](c4-general-structure-2026-11-06.md) §3; Theorem A is
that of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md) §2.
Manuscript `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`:
`def:balanced`, `def:bpa`, `thm:defect-intertwiner`, `ex:nonpisot`.

## 0. What the gate decided, and what this note runs

The literature stop/go check for this experiment is the gate itself (§2 there
lists the sources read); no new route is opened here. Its rows are applied
as follows.

| Gate row (§0) | Run here as |
| --- | --- |
| B1, both-outside irreducible non-Pisot: **stop** | No search. The window is run on the 1,812 non-synchronizing both-outside specimens only as a consistency check of R3: a nonempty limit there is a defect and raises (gate §4.7). Their rows in §3 are consistency data, not observations: R3 already decides them. |
| B2, one-outside seeded closures: **stop** | No seeded exploration anywhere. The only seeded run is the gate's §4.5 budget-exhaustion control, through `psc/bounded_bpa.mojo`. |
| B2/B3, `K₂ ≡ 0` window: **proceed, narrowed, fused with A** | The search of this note: the greatest fixed point below the complete list `P_L` of experiment A, `L = 13` and the extension `L = 14`, on the non-synchronizing one-outside and reducible specimens, with exact root classification. |
| B3, reducible `K₂ ≠ 0` strict systems: **stop a new search; redirect** | Not searched. The 28 pinned carriers of `kernel/tests/test_c4_quotient_spectrum.mojo` are checked to have `K₂ ≠ 0` on their seeds (pinned, §3.6). |
| Strong-coincidence filter (gate §4.3 item 1) | A verdict where all three letter pairs carry a witness on one side; undecided otherwise. |

An earlier interrupted run of this workflow step left a draft under the same
file names. It ran swap-seeded explorations with verdict labels in the
irreducible non-Pisot class, an all-pairs length-7 core, and its own second
enumeration of the `K₂ = 0` pairs. Those parts contradict the gate (§4.6,
§4.7, and AGENTS.md "do not re-enumerate") and were deleted, not adapted;
none of its figures is cited here. What was kept: the exact class arithmetic,
the strong-coincidence witness search with its level budget, the streamed
child kernel (now looking up `P_L`), and the ordered re-derivation of a found
carrier.

## 1. Assumptions and hypotheses

**Domain.** The 59,319 triples `(σ(0), σ(1), σ(2))` of words of length 1..3
over `{0,1,2}` (the 39 `image_words` of `psc.corpus`, in its order), with
incidence `M[i][j] = |σ(j)|_i`. Primitivity is Boolean matrix powers
(`psc.pisot.is_primitive`); PIP is the corpus screen of `psc.pisot`;
irreducibility of `χ_M` is the absence of an integer root; the number of
non-Perron roots outside the unit disc is `conjugates_outside`, an exact
Sturm–Tarski count over unbounded rationals (`psc.real_root_sign.count_real_roots`):
three real roots are counted in `(−1, 1)` (`±1` are not roots of an
irreducible cubic); with one real root `β` and a pair `α, ᾱ`,
`β|α|² = |det M|`, so the pair is outside iff no real root lies in
`(|det M|, B)` for the Cauchy bound `B`. A specimen is *synchronizing* when
its first-letter map `h(a) = σ(a)[0]` or its last-letter map `t(a) = σ(a)[−1]`
is eventually constant (endpoint types A, B; `psc.c4_cut_attractor.eventually_constant`).

The exact partition (the gate's §4.3 table, there scratch, now computed and
pinned by the regression and by the oracle):

| class | primitive | non-synchronizing | role here |
| --- | ---: | ---: | --- |
| PIP | 4,554 | 1,542 | the corpus; not part of B |
| irreducible, one non-Perron root outside (R3′ class) | 3,216 | 1,704 | **window domain** |
| irreducible, both outside (R3 class) | 3,960 | 1,812 | R3 consistency pass only |
| reducible `χ_M` | 21,588 | 10,134 | **window domain** |

The non-synchronizing column sums to 15,192, the scratch window search's
count. The window domain has 11,838 specimens, and with the R3 pass this note
runs on 13,650 of the 15,192: the PIP row is not searched (§3.3).

**Strict system** (cut-pair note §2). A finite nonempty set `C` of irreducible
noncoincident (`u ≠ v`) balanced pairs containing every block of the
zero-return factorisation `red(σ(u), σ(v))` of each `(u,v) ∈ C`. No
reachability or legality is imposed. `σ` is nonerasing throughout.

**The list `P_L`.** `P_L` is the set of normalised (`u₀ < v₀`) irreducible
noncoincident pairs with `K₁ = K₂ = 0` and length `≤ L`. It is read from
experiment A: `census_length(3, n, DEGREE_THREE)` keeps every pair of first
defect degree at least three, i.e. every `K₂ = 0` pair, at each `n`;
`k2_zero_universe` raises unless the kept count equals the census's `K₂ = 0`
count at every length and every member has `K₂ = 0`. That check guards
against a `kept_from` mismatch and a mislabelled member only. With
`kept_from = DEGREE_THREE` both numbers come from the same loop of
`census_length`, so the check cannot see a pair the enumeration missed.
**The search is only as complete as `P_L`**, and completeness of `P_L`
rests on two things:
- the exactness of `census_length`'s class enumeration, the contract pinned
  by `kernel/tests/test_binomial_pair_census.mojo` for `n ≤ 13`;
- independent replays of its `K₂ = 0` counts (below the size table).

The `n = 14` row of A is recorded in A's note but not pinned there, so the
`L = 14` extension inherits that status (§5).

| `n` | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `\|P_n \ P_{n−1}\|` | 6 | 24 | 198 | 1,230 | 7,644 | 50,406 | 323,274 | 2,168,652 |

These are A's table (degree 3 + degree 4: `50,394 + 12`, `323,250 + 24`,
`2,168,646 + 6`); `P_13` has 382,782 members and `P_14` 2,551,434. No length
below 7 occurs because A finds none, not because of a cut: lengths `2..6`
are looked up and are empty.

The independent oracle (`oracles/python/c4_closed_component_search.py`,
signature grouping in a dictionary, no shared code) rebuilds the list and
prints its sizes. `universe 14` printed, in 1 min 40 s single-threaded on
2026-11-09:

```
{"7": 6, "8": 24, "9": 198, "10": 1230, "11": 7644, "12": 50406, "13": 323274, "14": 2168652}
```

This is the table above, so the `K₂ = 0` totals of A's rows `n = 12, 13, 14`
now have an independent replay in a second language. The split between
degree 3 and degree 4 in rows 13 and 14 does not, since this oracle computes
no `K₃` or `K₄`.

**Theorems used, and how.**
- *Verdicts:* Theorem A(4) of the cut-pair note (repository-proved, written
  proof, human review pending; nonerasing `σ` only) and its reversal
  (Lemma 4 below, a written argument first given in this note, human review
  pending). Of the 5,754 domain verdicts, 870 are decided by right witnesses
  only and so rest on Lemma 4 as well (§3.2).
- *Consistency checks only* (a contradiction raises; nothing is concluded
  from their holding): the endpoint filter of gate §4.3 item 1 (from
  `Psc.Binomial.heads_ne`), R2, R3 and R3′ (written proofs, human review
  pending).

**Budgets.** The window itself has none: for a given `L` the fixed point is
exact. The strong-coincidence search inflates witness words of at most
20,000 letters (`left_witness` at the level bound that keeps
`|σ^{n−1}(x)|·max|σ| ≤ 20,000`, at most 32 levels); a pair without a witness
inside that budget is undecided (`−1`), never "not coincident".

## 2. Derivation / reduction

**Lemma 1 (normalisation).** For a balanced `(u, v)` the blocks of
`red(σ(v), σ(u))` are the swaps of those of `red(σ(u), σ(v))`, in order: a
zero return is a position where the Parikh prefixes of the two tracks agree,
a condition symmetric in the tracks. So the normalised image of a strict
system is a set of normalised states closed under normalised children; and
such a set `S` lifts to the ordered strict system `S ∪ swap(S)`, since
swapping preserves irreducibility and noncoincidence. For an irreducible
noncoincident pair, normalisation orders the sides by first letter, which
differ (`heads_ne`). ∎

**Lemma 2 (the window; gate §4.3 item 4).** Let `F(X) = {T ∈ X : every
normalised child of T lies in X}` on subsets of `P_L`, and `X* = ⋂_k F^k(P_L)`
(reached after finitely many steps). (a) If `S` is a strict system with
`K₂ = 0` on every state and every state of length `≤ L`, then its
normalisation `S'` lies in `P_L` and `S' ⊆ F(S')`, so by monotonicity
`S' ⊆ X*`. (b) `X* = F(X*)`, so a nonempty `X*` is closed under normalised
children, noncoincident and irreducible, hence (Lemma 1) a strict system.
**So `X* = ∅` iff `σ` has no strict system with `K₂ = 0` on every state and
every state of length `≤ L`.** Part (a) uses that `P_L` contains every
`K₂ = 0` irreducible pair of length `≤ L`: a list cut by a minimum length
(the scratch C program rejected children of length `< 7`) would make (a)
depend on that minimum. Here every block is looked up in A's list. ∎

**Lemma 3 (carriers of a nonempty limit).** A nonempty `X*` has a sink SCC
in its child graph; it is closed, noncoincident, and carries a cycle (every
state has a child), i.e. a strict carrier in the sense of
`psc.carrier.profile_component` (`is_closed_nonproductive`). `strict_carriers`
reads them that way and raises if a nonempty `X*` has none. A found carrier
is re-derived on ordered pairs by `psc.c4_cut_attractor.strict_closure`
(which raises on a coincident factor) and must normalise onto itself, with
ordered size `m` or `2m`. ∎

**Lemma 4 (reversal).** Let `σ̃(a)` be `σ(a)` reversed. For a balanced
`(x, y)` of length `n`, `k` is a zero return of `(x̃, ỹ)` iff `n − k` is one
of `(x, y)` (the totals are equal). Since `σ̃(w̃)` is the reversal of `σ(w)`,
the children of `(ũ, ṽ)` under `σ̃` are the reversals of those of `(u, v)`
under `σ`, so `C` is a strict system of `σ` iff `C̃` is one of `σ̃`; a left
witness for `σ̃` is a right witness for `σ`. Applying Theorem A(4) to `σ̃`:
no last-letter pair of a strict system of `σ` is right strongly coincident.
A strict system is nonempty, and the first (last) letters of any of its
states form one of the three unordered letter pairs. **So all three letter
pairs left-witnessed, or all three right-witnessed, means no strict system at
all** (any length, any `K₂`). ∎

**The streamed kernel.** `child_indices` reads `σ(u)` and `σ(v)` letter by
letter from a per-specimen flat image table, never building them. A zero
return is detected by the first two coordinates of the Parikh difference
(the third is their negated sum, both tracks having read the same number of
letters). A block is oriented by its first letters and looked up exactly by
its base-3 codes (binary search in rows sorted by
`psc.binomial_pairs.sorted_row_order`). The kernel stops at the first block
that is coincident, longer than `L`, or not in `P_L`. The regression checks
it against the package's `children` on every member of `P_11` for six
substitutions (§4).

**Consistency checks.** `window_specimen` names each failure; the driver
prints the specimen and raises (refuse to conclude). The checks are the
functions `specimen_violations`, `carrier_violations` and
`r3prime_violation`, so each name can be shown to fire (§4).
`r3prime_violation` refuses a cubic that is not irreducible on every branch,
whatever the degree, so a mislabelled one-outside class fails closed. The
first version refused it only on the `r(C) = 3k` branch.

| name | fires on | source |
| --- | --- | --- |
| `A4-all-pairs` | a nonempty limit with all pairs witnessed on one side | Theorem A(4), Lemma 4 |
| `A4-left`, `A4-right` | a carrier with a left-witnessed first-letter pair or a right-witnessed last-letter pair | Theorem A(4), Lemma 4 |
| `endpoint` | a nonempty limit on a synchronizing specimen | gate §4.3 item 1 |
| `R3` | a nonempty limit in the both-outside class | Theorem R3 |
| `R2` | a carrier state with `K₂ ≠ 0` over an irreducible non-Pisot cubic (only possible with a universe other than `P_L`) | Theorem R2 |
| `R3prime-*` | a one-outside carrier with `r(C) ≡ 2 (mod 3)`, or `r(C) = 3k` and `\|det M\|^k > β`, or `r(C) = 3k+1` and `\|det M\| ≠ 1` (`r ≥ 5` is not determined and not checked) | Theorem R3′ |

**What a find would have been** (gate §5). A `K₂ ≡ 0` strict system of a
primitive `σ` would be a full control of
`Binomial.ChildSystem.reduction_lemma` /
`PrimitiveExpansion.reduction_limit_of_primitive` and would refute
combinatorial Concentration; one in the one-outside class (a sink SCC of it)
would be a full control of the `KernelCofactor` representative theorems, and
with `r(C) = 3` or (`|det M| = 1`, `r(C) = 4`) a leave-one-out control
dropping only Pisot for `Degree3Sector` / `Degree4Floor`; one in the
reducible class would drop only irreducibility. None was found (§3.3).

## 3. Evidence and replay

### 3.1 Commands

```sh
cd kernel
# the window at L = 11 and L = 13, all passes (domain, R3, endpoint): about 25 s and 5.5 min on 4 workers
pixi run --locked mojo run -I . c4_closed_component_search.mojo 11 20000 0 28764 1 all
pixi run --locked mojo run -I . c4_closed_component_search.mojo 13 20000 0 28764 1 all
# the L = 14 extension, domain and R3 passes
pixi run --locked mojo run -I . c4_closed_component_search.mojo 14 20000 0 28764 1 domain+r3
# the L = 13 stride-21 slice pinned by the regression
pixi run --locked mojo run -I . c4_closed_component_search.mojo 13 20000 0 28764 21 domain+r3
# the regression (about 1 min 45 s; L = 11 on the whole window domain and the
# R3 pass, and the L = 13 stride-21 slice of both)
pixi run --locked mojo run -I . -I tests tests/test_c4_closed_component_search.mojo
cd ..
python3 -m pytest -q tests/test_c4_closed_component_search_oracle.py     # about 20 s
python3 -I oracles/python/c4_closed_component_search.py domain
python3 -I oracles/python/c4_closed_component_search.py universe 14     # |P_n| for n <= 14, about 1 min 40 s
python3 -I oracles/python/c4_closed_component_search.py window 11       # the full L = 11 replay
python3 -I oracles/python/c4_closed_component_search.py window 13 0 28764 21   # the L = 13 slice, whole
python3 -I oracles/python/c4_closed_component_search.py compare LOG     # recompute a log's WINDOW_SPECIMEN lines
```

Arguments of the driver: `L WORDS START STOP STRIDE PASSES`; `PASSES` is
`domain`, `domain+r3` (default) or `all`. The census is deterministic:
`parallel_fold.parallel_map_fold` folds in index order. Output lines:
`PARTITION`, one `PASS` line per pass and class, one `WINDOW_SPECIMEN` JSON
line per specimen with a first-pass survivor (the oracle's input), one
exact `CCS_` record per carrier found, then the labelled `VERDICT` and
`WINDOW OBSERVATION` lines.

### 3.2 Strong coincidence (verdicts)

| pass | class | specimens | all left-witnessed | all right-witnessed | **either: no strict system at all** |
| --- | --- | ---: | ---: | ---: | ---: |
| domain | one-outside | 1,704 | 240 | 240 | **456** |
| domain | reducible | 10,134 | 4,644 | 4,644 | **5,298** |
| R3 | both-outside | 1,812 | 186 | 186 | 216 |
| endpoint | one-outside | 1,512 | 930 | 930 | 1,512 |
| endpoint | both-outside | 2,148 | 1,464 | 1,464 | 2,148 |
| endpoint | reducible | 11,454 | 9,282 | 9,282 | 11,454 |

So 5,754 of the 11,838 domain specimens have no strict system at all.
Every synchronizing specimen is also decided by strong coincidence, as it
must be (an eventually constant endpoint map gives every pair a trivial
witness). The left and right counts agree because reversal preserves the
class and swaps the endpoint maps (Lemma 4). These counts do not depend on
`L`.

**Which verdicts rest on Lemma 4.** A verdict from left witnesses alone uses
Theorem A(4) only. A specimen that is all right-witnessed but not all
left-witnessed (either − all-left) also uses the reversal argument of
Lemma 4. In the domain these number `456 − 240 = 216` (one-outside) and
`5,298 − 4,644 = 654` (reducible): **870 of the 5,754 verdicts rest on
Lemma 4 as well as on Theorem A(4).** The other 4,884 rest on Theorem A(4)
alone. Of those, 24 one-outside and 3,990 reducible specimens are also
all right-witnessed.

### 3.3 The window (observations)

| `L` | pass | class | specimens | with a first-pass survivor | first-pass pairs | removal rounds | **nonempty limit** |
| ---: | --- | --- | ---: | ---: | ---: | --- | ---: |
| 11 | domain | one-outside | 1,704 | 12 | 12 | 1 each | **0** |
| 11 | domain | reducible | 10,134 | 24 | 36 | 1 each | **0** |
| 11 | R3 | both-outside | 1,812 | 48 | 108 | 1 each | 0 |
| 11 | endpoint | one-outside / both-outside / reducible | 1,512 / 2,148 / 11,454 | 0 / 36 / 0 | 0 / 60 / 0 | 1 each | 0 |
| 13 | domain | one-outside | 1,704 | 96 | 228 | 1 each | **0** |
| 13 | domain | reducible | 10,134 | 174 | 702 | 1 each | **0** |
| 13 | R3 | both-outside | 1,812 | 144 | 1,698 | 1 each | 0 |
| 13 | endpoint | one-outside / both-outside / reducible | 1,512 / 2,148 / 11,454 | 36 / 60 / 162 | 60 / 768 / 210 | 1 each | 0 |
| 14 | domain | one-outside | 1,704 | 96 | 900 | 1 each | **0** |
| 14 | domain | reducible | 10,134 | 246 | 2,856 | 1 each | **0** |
| 14 | R3 | both-outside | 1,812 | 144 | 7,344 | 1 each | 0 |

A *first-pass survivor* is a member of `P_L` all of whose children lie in
`P_L`. The `L = 11` endpoint row was logged on 2026-11-09 (`11 20000 0 28764 1
all`). Its empty limits also follow from the `L = 13` row: the limit at
`L = 11` is closed under children and lies in `P_11 ⊆ P_13`, so it lies inside
the limit at `L = 13`. Its first-pass counts do not follow. At `L = 11` all 156
first-pass survivors of the domain and R3 passes are length-7 pairs
with a single child, of length 11, which fails in turn (for `12/0/20`:
`(1022110, 2110021)`; scratch probe, not pinned). At every `L` run, every
first-pass survivor is removed in exactly one round.

**Window observation (`L = 13`, not a verdict): no strict system with
`K₂ = 0` on every state and every state of length ≤ 13 among the 11,838
domain specimens** (1,704 one-outside, 10,134 reducible).

**What of the scratch figure this reproduces.** Gate §1's scratch window
(`k2zero_strict.c`) covered all 15,192 non-synchronizing specimens with
images ≤ 3. This note reproduces only its **non-PIP part**, from canonical
Mojo over A's complete list: 13,650 of the 15,192 specimens (the 11,838 of
the domain plus the 1,812 of the R3 pass). The 1,542 non-synchronizing PIP
specimens are outside experiment B (gate §0, §4.3 item 2). **Their
`K₂ = 0` window remains scratch**, and it is the part that bears on C4.
Nothing here may be cited for it.

**Extension (`L = 14`, not a verdict): the same holds with every state of
length ≤ 14**, over `P_14` (2,551,434 pairs). This row rests on A's `n = 14`
row, which A records but does not pin (§5). The size of `P_14` is now
replayed independently (§1).

**The pinned `L = 13` slice.** The regression pins the stride-21 slice of the
off-corpus list at `L = 13`, domain and R3 passes:

| class | specimens | strong-coincidence verdicts | with a first-pass survivor | first-pass pairs | removal rounds | nonempty limit |
| --- | ---: | ---: | ---: | ---: | --- | ---: |
| one-outside | 99 | 28 | 9 | 21 | 1 each | 0 |
| reducible | 478 | 265 | 15 | 48 | 1 each | 0 |
| both-outside (R3) | 80 | 9 | 8 | 135 | 1 each | 0 |

These are the driver's figures (`13 20000 0 28764 21 domain+r3`; 32
`WINDOW_SPECIMEN` rows). The oracle replays the slice whole (§3.5).

Runtime (4 workers): `L = 11` about 20 s, `L = 13` 5 min 25 s for all
passes, and `L = 14` 23 min 23 s for the domain and R3 passes (one core
shared with an oracle replay). The greatest fixed point costs one streamed
pass over `P_L` per specimen.

**Rerun after the revision (2026-11-09).** The library changes are the
factored checks, `ordered_children`, `lift_size` and the uniform R3′
refusal. After them, the three driver runs `11 … all`, `13 … all` and
`14 … domain+r3` were rerun. Apart from timing lines, each log is
byte-identical to the first version's: every `PARTITION`, `PASS` and
`WINDOW_SPECIMEN` line, and the closing lines. The `11 … all` comparison
covers its domain and R3 lines. Rerun times, with one to four cores shared
with oracle replays: 22 s, 6 min 33 s and 23 min 8 s.

### 3.4 Consistency checks

No check fired at `L = 11`, `13` or `14`. The carrier-level checks
(`A4-left`, `A4-right`, `R2`, `R3prime-*`) are vacuous on these runs, since
no carrier was found. The specimen-level checks were live; each requires an
empty limit, and every limit was empty:
- `A4-all-pairs` on every strong-coincidence-decided specimen of the passes
  run: domain 5,754, R3 216, and at `L = 11, 13` the 15,114 synchronizing
  ones;
- `R3` on the 1,812 both-outside specimens;
- `endpoint` on the 15,114 synchronizing ones, at `L = 11` and at `L = 13`
  (both logged).

That a check *can* fire is shown separately, by positive controls in the
regression (`test_every_violation_name_fires`), because no run reached a
carrier:
- On the real path, `ex:nonpisot` with the universe of its two normalised
  `K₂ ≠ 0` states, mislabelled both-outside, reports exactly `R3, R2`. Its
  carrier's first- and last-letter pairs carry no witness, so `A4-left` and
  `A4-right` stay silent, as Theorem A(4) requires. Labelled one-outside, the
  same input raises, since its cubic `x(x − 2)(x + 1)` is reducible.
- On the factored functions, every other name fires on stated inputs:
  - `A4-all-pairs` and `endpoint` through `specimen_violations`;
  - `A4-left` and `A4-right` through `carrier_violations`, with synthetic
    masks;
  - `R3prime-degree`, `R3prime-det-power` and `R3prime-unimodular` through
    `r3prime_violation`, on real one-outside cubics: `12/0/20` (`|det| = 1`),
    `1/22/011` (`χ = x³ − 4x − 2`, `|det| = 2 < β`) and `01/02/111`
    (`χ = x³ − x² − 4x + 3`, `|det| = 3 > β`).
- The silent branches are pinned as well: `r(C) = 3` under `|det| < β`,
  `r(C) = 4` under `|det| = 1`, and `DEGREE_FIVE_PLUS`.

### 3.5 Independent oracle

`oracles/python/c4_closed_component_search.py` (stdlib; `Fraction` Sturm
chains; no shared code) recomputes: the partition (`domain`: PIP 4,554 /
1,542; one-outside 3,216 / 1,704; both-outside 3,960 / 1,812; reducible
21,588 / 10,134), with the endpoint flag decided by composing each map three
times rather than by its cycle type; `P_L` by grouping all words by
`(Parikh vector, N_ab)` in a dictionary (`universe 11`:
`7:6 8:24 9:198 10:1230 11:7644`); and the fixed point on materialised
inflations. Agreement:
- every `WINDOW_SPECIMEN` line of the Mojo `L = 11` run (84 specimens:
  `first_pass`, `rounds`, `survivors`) is recomputed equal (`compare`);
- the full `L = 11` replay over the window domain and the R3 pass (`window
  11`, 16 minutes single-threaded) gives the Mojo totals exactly (specimens /
  with a first-pass survivor / first-pass pairs / nonempty limit:
  one-outside 1,704 / 12 / 12 / 0, reducible 10,134 / 24 / 36 / 0,
  both-outside 1,812 / 48 / 108 / 0) and exactly the same 84 rows, so no
  specimen with a first-pass survivor is missing from either side;
- the pytest pins the partition, the `P_11` sizes, the permutation, `cyc3`
  and `ex:nonpisot` controls, five specimens with first-pass survivors at
  `L = 11`, and a stride-97 slice whose totals and rows equal the Mojo
  driver's (`11 20000 0 28764 97`).

Beyond CI, one-off oracle replays (`compare`, scratch logs) recompute every
`WINDOW_SPECIMEN` line of the Mojo `L = 13` run equal: all 672 rows of the
three passes (34 minutes single-threaded, the oracle building its own
`P_13`). The 96 one-outside rows of the `L = 14` run are recomputed equal as
well (37 minutes, over the oracle's own `P_14`, of size 2,551,434 by
`universe 14`, §1). The other 390 `L = 14` rows are not replayed.

**The `L = 13` slice, replayed whole (2026-11-09).** `window 13 START STOP
21` was run as four contiguous chunks, `START` in `0, 7203, 14406, 21609`
(multiples of 21, so the union is exactly the stride-21 slice), each
building its own `P_13` (382,782 pairs), 9 to 11 minutes each in parallel.
Merged, the chunks give the Mojo driver's totals exactly:
- one-outside 99 / 9 / 21 / 0;
- reducible 478 / 15 / 48 / 0;
- both-outside 80 / 8 / 135 / 0

(specimens / with a first-pass survivor / first-pass pairs / nonempty
limit). They also give the same 32 rows, compared in both directions, so
on this slice no specimen with a first-pass survivor is missing from either
side.

A `compare` checks only the listed rows, not that no other specimen has a
first-pass survivor. Outside the `L = 13` slice, at `L = 13, 14`, that
completeness rests on the Mojo runs, on the pinned `L = 11` contract and
`L = 13` slice of the same code, on A's list, and on the full `L = 11`
replay above.

### 3.6 The reducible class: the 28 pinned carriers (gate row B3)

`kernel/tests/test_c4_quotient_spectrum.mojo` pins one strict system per
relabelling × reversal class of strict carriers with images `≤ 3` (28
classes). The regression imports that table (`from test_c4_quotient_spectrum
import carriers`, resolved by `run_tests.sh`'s `-I tests`), so the two tests
read one table instead of two copies. Moving the table into a library module
would touch that tracked test, and is left as a proposed cleanup. For each
class representative the regression checks:
- **its seed has `K₂ ≠ 0`** (all 28), and in fact every state of its ordered
  strict closure has `K₂ ≠ 0`, 123 ordered states in all, so none lies in
  `P_L` and the `K₂ = 0` window cannot see it;
- the specimen is reducible and non-synchronizing (all 28 are in the window
  domain);
- with the `K₂` filter off (the universe is the carrier's own normalised
  states) the fixed point keeps every state; with it on (`P_9`) the limit
  is empty.

So the window's empty answer on the reducible class is not a statement about
strict systems in general there: 28 classes of them exist, all of first
defect degree 2 on every state.

### 3.7 Fail-closed behaviour

Refusals that raise never abort, and never return an empty structure that
could read as evidence. They are:
- an erasing or malformed `σ` (checked before any `psc.bpa.sigma3` call,
  which aborts);
- a universe pair that is unbalanced, reducible, coincident, not normalised,
  duplicated, too long, or beyond the code range;
- a `K₂ = 0` universe whose census count disagrees with its kept list. This
  catches a `kept_from` mismatch only, not a pair missed by the enumeration
  (§1);
- a lookup before `seal`; an inflation that does not close;
- a nonempty limit without a strict carrier;
- an ordered re-derivation that meets a coincidence, leaves the carrier, or
  is neither `m` nor `2m`;
- an exact record (`emit_component`) whose ordered child rows give a lift
  size (`lift_size`) different from that re-derivation;
- a non-irreducible cubic handed to `conjugates_outside`, or to the R3′
  check on any branch, so a mislabelled class fails closed;
- a nonpositive witness budget.

A worker failure aborts the census after replaying the first failing
specimen serially. A consistency violation prints the specimen and raises.

## 4. Negative controls

- **The iteration keeps closed sets.** The permutation substitutions
  `0/1/2` and `1/2/0` keep all of `P_9` (each pair's only child is a
  relabelling, `K₂ = 0` is relabelling-invariant): first pass 228, no
  removal round. The Lean `cyc3Norm` system (`SectorBridge`: `wTPair` and its
  two relabellings under `0 ↦ 1 ↦ 2 ↦ 0`) fed alone survives as one strict
  carrier of 3 normalised states, ordered lift 3, `r(C) = 3`; with the third
  state removed, the second fails the first pass and the first dies in the
  one removal round. Both substitutions are refused
  by the primitivity screen (`CLASS_NOT_PRIMITIVE`), so they never enter the
  domain.
- **`ex:nonpisot` (`1/012/1`, gate §4.5).** Its strict closure of `(01, 10)`
  has 4 ordered states, all `K₂ ≠ 0`, normalising to `(01, 10)` and
  `(12, 21)`. With the filter off the fixed point keeps both; with it on,
  none is in `P_9` and the
  window of `1/012/1` is empty. The same holds for all 28 carriers (§3.6).
- **A budget is not a verdict (gate §4.5).** The swap-seeded bounded
  balanced-pair graph of `1/2/001` (`χ = x³ − x − 2`, both-outside) at 20,000
  states and 1,000 letters stops with `BUDGET_LENGTH` and is capped. The same
  specimen has 2 first-pass survivors and an empty limit at `L = 11`, which
  says nothing beyond length 11; that it has no strict system at all is R3.
- **Witness budgets.** `12/0/20` has left levels `[−1, −1, −1]` and right
  `[−1, −1, 1]` at 20,000 letters (undecided, not excluded); at a 1-letter
  budget every pair is `−1`. `112/0/1` is decided only deep (left levels 14,
  1, 15). `10/102/211`, the reversal-class of the pinned carrier
  `01/201/112`, has left `[1, −1, −1]`, right `[−1, −1, 2]`; its 4-state
  strict closure of `(102, 210)` has first-letter pairs `{1,2}` only and
  last-letter pairs `{0,1}, {0,2}`, avoiding the witnessed pairs, as
  Theorem A(4) and its reversal require.
- **Consistency checks fire.** `1/2/0` over `P_9` labelled both-outside and
  synchronizing reports `R3` and `endpoint`; labelled one-outside, the R3′
  check refuses the reducible cubic and the call raises. Every other name
  fires on a positive control (§3.4).
- **The find path runs.** No search found a carrier, so the exact record is
  exercised on known closed sets.
  - `cyc3Norm` under `1/2/0`, in the order `(wTPair, t1, t2)`, gives the
    ordered child rows `(0,0,1,0)`, `(1,0,2,1)`, `(2,0,0,1)`: `σ(w) = t1`,
    `σ(t1) = swap(t2)`, `σ(t2) = swap(w)`. That is an even number of swaps
    around the cycle, so the lift is `m = 3`, as `strict_closure` finds.
  - `ex:nonpisot`'s two normalised states give a lift of `2m = 4`.
  - In both, `emit_component` prints `CCS_TEST_COMPONENT_META`, the
    countermodel block and the `CCS_TEST_ORDERED_CHILD` lines, and
    `lift_size` of the rows equals the ordered re-derivation.
- **Second exact root count.** On every irreducible cubic of the off-corpus
  list, `conjugates_outside` (Sturm–Tarski) equals
  `psc.pisot_screen.roots_outside_unit_circle − 1` (Routh, `|z| > 1`)
  wherever the Routh array decides: 7,158 of the 7,176 one- and
  both-outside specimens, 84 of 85 distinct cubics. The Routh array refuses
  `x³ − 6x − 3`, a one-outside cubic with 18 specimens. That is a Routh
  singularity, and `psc.pisot_screen` documents that a refusal is not a
  verdict either way.
  On the PIP corpus the Routh count is 1 on 3,744 specimens and refuses the
  Pisot cubics `x³ − x² − 2x − 2` and `x³ − 2x² − x − 2` (810 specimens). On
  the refused cubics the Sturm–Tarski count is the only exact method in
  play.
- **Streamed kernel.** `child_indices` agrees with the package's `children`
  on every member of `P_11` for `0/1/2`, `1/2/0` (all succeed), `12/0/20`
  (1 succeeds), `112/0/1` (2), `10/102/211` and Tribonacci (none).
- **Failed stronger variants preserved, not deleted.** The draft's
  seeded-exploration "verdicts" in the irreducible non-Pisot class are
  withdrawn: by R3 or Corollary B(iii) such a run can only cap (gate §4.7).
  The scratch C program's rejection of children of length `< 7` (gate §4.3
  item 4) is not used.

## 5. Non-claims / remaining gaps

- **Window only.** Nothing is claimed for strict systems with a state longer
  than `L`, or with a state of `K₂ ≠ 0`. "No `K₂ = 0` strict system with all
  states ≤ 13" is not "no strict system".
- **The PIP part of the scratch window is not reproduced.** This note
  reproduces the non-PIP part (13,650 of the 15,192 specimens: 11,838 domain
  plus 1,812 both-outside) of the scratch `k2zero_strict.c` figure of gate §1.
  The 1,542 non-synchronizing PIP specimens are outside experiment B, and
  their `K₂ = 0` window remains scratch. The same holds for the scratch
  `≤ 11` window on the 592,134 specimens with images ≤ 4.
- **870 verdicts rest on Lemma 4 too.** Of the 5,754 strong-coincidence
  verdicts, 216 one-outside and 654 reducible are decided by right witnesses
  only. They rest on Lemma 4 of this note (a written proof, human review
  pending) as well as on Theorem A(4). The other 4,884 rest on Theorem A(4)
  alone (§3.2).
- **The one-outside class.** For the 1,248 one-outside domain specimens not
  decided by strong coincidence, (H)'s open conjunct is **open**: a strict
  system there needs `K₂ ≡ 0` (R2), `r(C) ≢ 2 (mod 3)` and the R3′
  admissibility, an unwitnessed first-letter pair and an unwitnessed
  last-letter pair, and (by this note) a state longer than 13 letters
  (longer than 14, granting A's unpinned `n = 14` row).
- **The reducible class.** For the 4,836 reducible domain specimens not
  decided by strong coincidence, only the `K₂ = 0` window is established;
  strict systems with `K₂ ≠ 0` exist in 28 pinned classes and were not
  searched for (gate row B3).
- **The reductio-lemma gaps stay open** (gate §5): no control dropping only
  "Pisot" (keeping irreducibility, primitivity and `K₂ ≡ 0`), and no
  primitive literal `K₂ ≡ 0` control on three letters. An empty window
  records them as open, not as closed.
- **The consistency passes are not evidence for R3 or the endpoint filter.**
  They only failed to contradict those written arguments on finite windows.
- **The `L = 14` row** rests on A's `n = 14` row, which A records but does
  not pin. The size of that row's `K₂ = 0` list is now replayed
  independently (§1), but the window itself is replayed only on its 96
  one-outside rows (§3.5). It is an extension, not part of the pinned
  contract.
- **The `L = 13` row** is pinned on its stride-21 slice only (657 of the
  13,650 specimens of the domain and R3 passes) and replayed whole by the
  oracle on that slice. On the rest it is the driver's run, with all 672
  rows recomputed by the oracle (`compare`). That a specimen outside the
  slice has no first-pass survivor rests on the Mojo run alone.
- **Not reproduced here.** The swap-seeded landscape of the
  general-structure note §6 (276 carriers, 294 systems, 7,974 productive,
  25,068 capped, length-7 seed-independent search) is not ported: the gate
  stopped the seeded search. It remains scratch, except the 28 class
  representatives pinned natively. Its seed-independent length-7 search is
  superseded on the window domain only for `K₂ = 0` systems (this note), not
  for `K₂ ≠ 0` ones.
- Nothing is claimed for images longer than three, for PIP substitutions
  (`C4StandingCorpus`), C4, (H), (N0), BH, A1′, G1 or PSC. No novelty is
  claimed: the method is the gate's.
- The census is not registered as a ledger claim. The side findings of this
  note are recorded in the `docs/side-notes-ledger.md` entry dated
  2026-11-07, "C4 off the PIP corpus: the `K₂ = 0` window search" (added at
  integration, 2026-11-09), and they are listed there, not here. That covers
  the withdrawn draft verdicts, the `L = 11` length-7 survivors, the empty
  windows, the 28 carriers with `K₂ ≠ 0` on all 123 states, the non-PIP scope
  of the reproduction, and the Routh refusals.

# Formal versus realized overlap carriers — 2026-10-04

**Status:** exact finite census over the standing 4,554-member corpus, plus an
elementary region argument stated and proved below. Finite evidence only; no
ledger node, open problem, or PSC status changes. **Provisional:** the §3
numbers are from the first full run, whose region was sized in floating
point; the exact-kernel re-run, the receipts under `docs/evidence/` and the
oracle receipt check are pending and will replace this sentence.

## 1. Why this exists

`completion-ledger-2026-09-11.md` §V records "formal producer-free cycles:
1,764; globally surviving at tested collars: 0; maximum death radius 7;
collar tested to 40". No instrument for that line is in the repository: not
on `main`, and not in the 2026-09-08 archive bundle, whose nearest relative is
the retracted letter-graph detector (`archive/2026-09-08/notes_2026_06/
H3_LETTERGRAPH_BUG_2026_06_13.md`, a transpose bug reporting 11k–19k spurious
trapped cycles). The line is therefore not reproducible and is superseded
here by an exact census of a precisely defined object. The two are **not**
claimed equal: carriers replace simple cycles, and death depth replaces the
collar radius.

## 2. Objects

Fix a primitive irreducible Pisot substitution on three letters, with the
exact tile lengths `l_a` and overlap states `(i, j, t)` of
`mojo/psc/overlap_seed_patch.mojo`.

- **Potential overlap:** a genuine state `(i, j, t)` with
  `t = sum_a w_a l_a`, `w in Z^3`, not required to be reachable from a seed.
- **Formal graph `F_sigma`:** the inflation closure of the potential overlaps
  of the region `K_T` below.
- **Realized graph `R_sigma`:** the swap-seed overlap graph (the
  overlap-productivity object of issue #84).
- **Carrier:** a recurrent SCC of `F_sigma` after deleting coincidences, i.e.
  a maximal set carrying coincidence-free ("producer-free") cycles. Carriers
  are counted because the number of simple cycles is not canonical.
- **Death depth:** the least number of inflations from a carrier to a
  coincidence.

Let `q(t) = sum_k |sigma_k(t)|^2` over the two contracting embeddings and
`rho` the largest contracting modulus. Inflation sends `t` to `beta t + c`
with `c` a difference of two prefix positions.

**Region argument.** Let `T >= max_c sqrt q(c) / (1 - rho)`. Then:

1. `K_T = {q(t) <= T^2}` is forward closed: on the contracting coordinates
   `sqrt q(beta t + c) <= rho sqrt q(t) + sqrt q(c) <= rho T + (1 - rho) T = T`.
2. Every state on a cycle lies in `K_T`: if `sqrt q(t) > T`, then
   `sqrt q(t') <= rho sqrt q(t) + (1 - rho) T < sqrt q(t)`, so along a cycle
   the value strictly decreases while outside `K_T`, stays inside once
   inside, and cannot return to a value above `T`.
3. Hence every carrier, and every path from a carrier to a coincidence, lies
   in the closure of the genuine potential overlaps of `K_T`.
4. A carrier is wholly realized or wholly unrealized: `R_sigma` is forward
   closed and a carrier is strongly connected.
5. If no state of the closure of `K_T` is nonproductive, then no potential
   overlap at all is nonproductive. A nonproductive state has a nonproductive
   child, so it starts an infinite nonproductive path. Along it
   `sqrt q - T` contracts by `rho`, so the path enters the finite set
   `{q <= T'^2, |t(beta)| < l_max}` for any `T' > T` and repeats a state. The
   repeated segment is a nonproductive cycle, which lies in `K_T` by 2.

The kernel is exact. `q(t)` is an element of `Q(beta)` (`Tr(t^2) - t^2` for a
real contracting pair, `2N(t)/t` for a complex pair), so membership in `K_T`
is one exact sign at the Perron root. `rho`, `T` and the enumeration box are
rational upper bounds: Sturm isolation or `|chi_0|/beta`, `T = A/64`, and the
trace-dual basis with Cauchy–Schwarz,
`|w_a| = |Tr(t l*_a)| <= l_max |l*_a(beta)| + T sqrt q(l*_a)`.

## 3. Census

`pixi run formal-overlap-census records` (canonical
`mojo/psc/formal_overlap.mojo`, driver `mojo/formal_overlap_census.mojo`).
Receipts: `docs/evidence/formal-overlap-carriers-2026-10-04/`.

| Quantity | Value |
| --- | ---: |
| specimens | 4,554 |
| formal states / largest formal graph | 23,286,258 / 114,033 |
| realized states (equals the standing overlap census) | 1,118,850 |
| formal nonproductive states | 0 |
| specimens with a carrier vertex outside the seed box | 0 |
| closed carriers | 0 |
| formal carriers | 13,260 |
| specimens with an unrealized carrier | 2,928 |

| | unrealized | realized |
| --- | ---: | ---: |
| carriers | 7,182 | 6,078 |
| aligned (an offset-zero vertex) | 52 | 4,808 |
| strict zipper | 7,130 | 1,270 |
| with a coincidence as a direct child | 36 | 4,194 |
| death depth range (mode) | 1–14 (3) | 1–6 (1) |

Death-depth histograms: realized `1:4194 2:1398 3:306 4:144 5:24 6:12`;
unrealized `1:36 2:582 3:1728 4:1014 5:1326 6:588 7:642 8:342 9:144 10:240
11:252 12:192 13:72 14:24`. The deepest unrealized carriers (depth 14, eight
states) and the largest (322 states, depth 10) occur in specimens `7 5 30`
and `7 9 14`. The Padovan/plastic substitution `0 -> 1, 1 -> 2, 2 -> 01`
(specimen `1 2 4`) is the smallest control: one realized aligned carrier (58
states, depth 4) and one unrealized strict carrier (16 states, depth 6).

## 4. Reading

- **No producer-free closed component exists, formal or realized.** Every
  formal carrier exits to a coincidence, and by item 5 of §2 every potential
  overlap of every corpus specimen is productive. On this object the realized/formal distinction is therefore
  **not** the distinction between productive and nonproductive: the stronger,
  realization-free statement holds on the whole corpus.
- **What realization does separate is the escape mechanism.** Realized
  carriers are 79% aligned and 69% leave in one inflation. Unrealized
  carriers are 99.3% strict zippers, die later (modal depth 3, up to 14), and
  almost never have a direct coincidence child.
- **Consequence for the proof route.** Productivity of every potential overlap
  (formal productivity) implies `OP_all`, hence `OP_seed`, with no realization
  hypothesis; it is the object the archived Q-infinity certificates addressed.
  It is a stronger target than #84, and its hardest instances are exactly the
  unrealized strict carriers. A proof of #84 may instead use realization, but
  the census says realization buys a faster, aligned escape, not productivity
  itself. Either route meets the strict-zipper branch (#139) as its core.

## 5. Verification

- Mojo regression `mojo/tests/test_formal_overlap.mojo`: the plastic control,
  the realized carriers equal the realized graph's own, a single-carrier
  specimen, and a non-Pisot input failing closed.
- Independent oracle `src/psc_research/formal_overlap.py`: exact `Fraction`
  arithmetic, its own root isolation, SCC algorithm and a deliberately looser
  region (triangle-inequality digit bound). Carriers do not depend on the
  region once it contains every cycle, so agreement also checks that.
  `scripts/check_formal_overlap_receipts.py` re-derives the summary from the
  records and recomputes a strided sample; `tests/test_formal_overlap.py`
  recomputes two fixtures on every run.

None of this is a universal theorem: a clean corpus is finite evidence, and
the region argument only makes the census complete per specimen.

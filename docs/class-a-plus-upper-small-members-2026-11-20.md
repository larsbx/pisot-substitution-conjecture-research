# Plus-Class-A upper small members: complete swap-seed certificates

**Status:** finite-domain, computer-assisted certificates with swap-seed scope
for exactly 70 members. Local canonical and independent replay agree; hosted
exact-head acceptance is pending. No governed claim status changes. Universal
BH (#139), residual A1′ (#138) and the PSC remain open.

Date: November 20, 2026. Base source: `main@11c15bce`.

## Statement

For the literal ordered plus-Class-A substitution

```text
x -> x y^(n+d) x,   c -> c y^n x,   y -> x y^(n+1) c,
```

and each of the 70 parameter pairs

```text
n = 0..6,   n+5 <= d <= 2n+11,
```

the graph of strict integral overlaps reached by actual ordered children from
the eighteen canonical swap sources (the nine literal swap intersections and
their track reversals) is finite. Every state has an actual original-occurrence
path to a typed full integral zero, and the composed original proper prefixes
satisfy `M^m w = P - Q`. The largest graph has 2,922 states and the greatest
depth is 9.

These are the upper-strip members below the
[all-source entry theorem](class-a-plus-upper-all-source-entry-2026-11-16.md),
whose arithmetic needs `n >= 7`. That theorem's non-claims record the
`n <= 6` upper members as open; this note discharges them at swap-seed
scope only.

**Lemma (PIP boundary).** Write `J = 2n+12-d`. The incidence cubic of the
plus family is

```text
chi(x) = x^3 - (n+4) x^2 + (J-n-7) x - 2,     chi(-1) = -J.
```

If `J = 0` then `-1` is a root and `chi` is reducible. If `J < 0` then
`chi(-1) > 0` and `chi(x) -> -inf` as `x -> -inf`, so `chi` has a real root
below `-1`. Hence no member with `d >= 2n+12` is Pisot, and every PIP member
of the family lies in `1 <= d <= 2n+11`. `tests/test_class_a_plus_upper_small_certificate.py`
also checks with the exact screen that `d = 2n+12, ..., 2n+19` are not PIP
for `n < 40`.

**Assembly at the constituents' own scopes.** The
[constant-entry note](class-a-plus-constant-entry-2026-11-14.md) and the
[BH roadmap](bh-escape-roadmap-2026-11-14.md) record a canonical swap-seed
cover for `n >= 0, 1 <= d <= n+4`. The all-source theorem covers
`n >= 7, n+5 <= d <= 2n+11`, which is stronger than seed scope there. With
the 70 members here and the lemma, every PIP member of the plus-Class-A
family has a canonical swap-seed cover by actual occurrence paths to typed
coincidence. Each part keeps its own source quantifier and its own acceptance
status. Pending hosted acceptance recorded for a constituent stays pending,
and no all-strict-source statement is claimed below `n = 7`.

## Work shown

### Assumptions and hypotheses

The words above are used literally, with ordered images and original
occurrence indices. The Perron field is the exact screened cubic field of the
literal incidence matrix (`psc.overlap_seed_patch.build_seed_overlap_tables_screened`).
The binder `bind_small` requires the following:

- the literal images;
- the incidence cubic `(chi0, chi1, chi2) = (-2, n-d+5, -(n+4))`;
- a Perron root in `(b, b+1)`, where `b` is the exact integer floor from `perron_floor`;
- positive tile lengths;
- every proper-prefix position;
- exact scaling of each image's length by `beta`.

On the five seams, `b = n+3` is asserted, which is the interval the seam
certificate used before. Caps are 6,000 states and 2×10⁷ occurrence pairs per
member. Reaching a cap refuses; it never yields a verdict.

Pre-code gate: the
[plus-constant source and hypothesis gate](bh-class-a-plus-constant-stop-go-2026-11-14.md)
already fixes the complete plus PIP domain `n >= 0, 1 <= d <= 2n+11`. It names
the upper chambers as separate targets and permits complete swap-seed
certificates for small members that "retain their seed scope". This note uses
the same construction on further finite members. No new mechanism, invariant
or universal statement is proposed, so no new literature review was run.

### Derivation / reduction

For each member the builder interns the eighteen swap sources, then expands
every state in breadth-first order. For each state it takes every ordered pair
of child occurrences `(i, j)` of its top and bottom images. The transported
full offset is

```text
M w + Parikh(bottom prefix j) - Parikh(top prefix i).
```

A pair is kept only when it is a geometrically strict interior overlap, which
is decided exactly in the Perron field. Typed full zero `(a, a, 0, 0, 0)` is
the only terminal. A complete backward breadth-first search gives each state's
distance to a terminal. `select_edges` then picks an original edge that
decreases that distance, and `verify_small` rebuilds the graph and refuses any
missing, extra or reordered state, edge, index or distance. Composing the
selected edges' prefixes gives the original-prefix identity for every state.

The only change to the canonical module is its domain.
`small_parameters` admits the five seams or the 70 upper members.
`perron_floor` replaces the fixed bracket `n+3 < beta < n+4`. It scans
`x = 0..1+max(n+4, |n+5-d|, 2)` (Cauchy) for the last `chi(x) < 0`, and
refuses an integer root.

### Evidence and replay

[Evidence packet](../evidence/class-a-plus-upper-small-2026-11-20/README.md).
Canonical run with Mojo `1.1.0.dev2026090805` from `kernel/pixi.lock`:

```text
cd kernel
pixi run --locked mojo run -j 1 -I . tests/test_class_a_plus_upper_small_entry.mojo
pixi run --locked mojo run -j 1 -I . tests/test_class_a_plus_upper_small_entry.mojo --emit-certificates > upper.log
cd ..
python oracles/python/class_a_plus_small_certificate.py --native-log upper.log --scope upper
python -m pytest -o addopts='' tests/test_class_a_plus_upper_small_certificate.py
```

The 70 members together have 53,222 states, 524,222 indexed ordered edges and
8,027,160 enumerated occurrence pairs. There are 53,222 paths with 171,954
edges in total, the greatest depth is 9, and the run records 4 native refusals.

| n | d | members | states | largest | edges | max depth |
| --- | --- | --- | --- | --- | --- | --- |
| 0 | 5..11 | 7 | 5,400 | 1,912 | 28,312 | 7 |
| 1 | 6..13 | 8 | 6,372 | 2,096 | 42,506 | 6 |
| 2 | 7..15 | 9 | 6,922 | 2,254 | 55,454 | 7 |
| 3 | 8..17 | 10 | 7,636 | 2,406 | 71,608 | 7 |
| 4 | 9..19 | 11 | 8,318 | 2,590 | 89,234 | 8 |
| 5 | 10..21 | 12 | 8,856 | 2,754 | 106,766 | 8 |
| 6 | 11..23 | 13 | 9,718 | 2,922 | 130,342 | 9 |

The emit transcript has 630,808 records and is byte-identical across runs:
SHA-256 `4385f8f0a32ad4b595c68105c4185477ad42c1d15cfd4964a8f70b64c7a53fab`.
The independent Python oracle rebuilds every child by Cartesian enumeration
over the literal words. It reproduces every native vertex, edge, path and
counter for all 70 members. It also re-derives each original-prefix
certificate. The 195 pytest cases pass.

### Negative controls

- **Native refusals.** The run refuses `(7,12)`, which is the theorem's first
  member and lies outside the finite scope, and `(0,12)`, which is the first
  non-PIP member. It also refuses a state cap of 18 at `(0,5)` and a perturbed
  distance vector at `(1,6)`.
- **Oracle refusals.** The oracle refuses `(7,12)`, `(0,12)`, `(0,4)`,
  `(6,24)`, `(-1,5)` and a boolean parameter. It refuses a state cap of 18 or
  a pair cap of 1, an empty transcript and an unknown scope.
- **Seam regression.** The seam regression
  `kernel/tests/test_class_a_plus_small_entry.mojo` prints unchanged totals
  (`1428 10232 97808 1428 3352 4 12`) after the domain change. The seam
  oracle's 78-case suite still passes.

### Non-claims / remaining gaps

- The scope is the eighteen swap sources and what they reach. Below `n = 7`,
  arbitrary strict integral overlaps are not covered.
- No Lean binding for these members. Lean binding of the written `n >= 7`
  entry path stays the companion obligation.
- Hosted exact-head acceptance of this packet and of the cited constituents
  is pending where their own records say so.
- The assembly is a cover of one parametric family. It gives no
  arbitrary-ternary BH, residual A1′ or general spectral statement.

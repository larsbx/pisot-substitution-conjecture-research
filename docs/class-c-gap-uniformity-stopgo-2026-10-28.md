# Class C, gaps d ≥ 6: stop/go for a gap-uniform certificate (2026-10-28)

**Status:** stop/go and design note with an exact finite profile; no theorem.
No claim status changes. Class C is certified line by line for gaps `d ≤ 5`
([gap 4](issue139-ac-gap4-2026-10-22.md), [gap 5](issue139-gap5-2026-10-23.md));
gaps `d ≥ 6` are BH's class-C residual in the
[completion ledger](completion-ledger-2026-10-26.md), next obligation 1.

## The lines

```text
sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,   sigma(y) = c y^(n-d+eps) c,   eps = ±1,
(p, q, r) = (n+d, n, n-d+eps),   M = [[2,1,0],[0,1,2],[n+d, n, n-d+eps]],   det M = 2 eps.
```

Unlike class A, where the y-run is `n + eps` for every gap, the y-run here is
`n − d + eps`: the gap enters the third image. Ray-by-ray tabulation cannot
finish, since there is one line per gap and sign.

**Perron algebra.** The characteristic polynomial is

```text
chi(t) = A(t) − n t(t−1),   A(t) = t(t−1)(t−2) + (d − eps) t(t−3) − 2 eps,
```

so `n β(β−1) = A(β)` eliminates `n` linearly, exactly as class B's
`q β(β+1) = A(β)` ([class-B ray certificate](class-b-ray-certificate-2026-10-27.md),
Lemma 1), and `d` enters `A` linearly too. A left eigenvector is
`L = (L_y (n+d)/(β−2), L_y (βn + d − n)/((β−2)(β−1)), L_y)`.

## Proposed claim

**Target (Theorem T_C, frozen tail).** For each sign there are a fixed finite
label set `F_eps` and a floor `c_eps` such that, for every gap `d ≥ d_0` and
every `n ≥ 4d + c_eps`, the complete canonical swap-seed overlap graph of
`(n+d, n, n−d+eps)` has label set exactly `F_eps`, and every label has an
offset-zero descendant.

The proof would be **one** finite labelled graph per sign, certified for every
`(n, d)` in the tail cone at once:

1. **Strictness.** Each label of `F_eps` is a strict overlap: two Perron signs
   per label, each a polynomial in `h = 1/β` and `u = d h` after eliminating `n`.
2. **Seeds.** The nine real swap seeds are in `F_eps`; the other three seed
   candidates are not strict.
3. **Closure.** For each label and segment pair, the run index that keeps the
   child in `F_eps` is affine in `(n, d)` and realizable on the whole cone, and
   every other child is non-strict (again a sign in `(h, u)`).
4. **Hitting.** The finite graph on `F_eps` reaches offset zero along edges
   that are real on the whole cone.

On the tail `n ≈ β + d − 2 − eps`, so `n ≥ 4d` corresponds to `u = d/β ≲ 1/3`: the
sign questions live on a **compact** box in `(h, u)`, which Bernstein
subdivision decides exactly, as in #335 (`class-a-gap-theorem-2026-10-23.md`,
Lemma 3'). Unlike class A, no carrier grows with the parameters: there is no
affine-in-`l` row table and no potential beyond the finite graph's depths.

## Prior art and transfer

No new mechanism is proposed, so the reviews already on record are reused:
the class-A d ≥ 5 [stop/go](class-a-gap-uniformity-stopgo-2026-10-23.md)
(Barge; Akiyama–Barge–Berthé–Lee–Siegel; Berthé–Bourdon–Jolivet–Siegel;
Minervino–Thuswaldner; Akiyama–Gähler–Lee; Hollander–Solomyak) and the
gap-4/5 notes (Akiyama–Lee's overlap algorithm, Minervino–Thuswaldner's
non-unit representation, Barge's initial-letter criterion). For class C:

- `|det M| = 2`, so the unimodular results (BBJS) do not apply;
- the trace is `n − d + 3 + eps`, at least `d − 1` (plus) or `d + 3` (minus)
  from the observed domain starts, so above the Akiyama–Gähler–Lee bound of 2;
- Minervino–Thuswaldner give a representation, not a family theorem.

No source states a coincidence or pure-discrete-spectrum result for these
lines. Novelty would lie in the certificate, not in the reduction.

## Exact finite profile

`kernel/class_c_gap_profile.mojo` (canonical) builds the exact complete graph
of a member and records its label set losslessly as typed `k`-intervals, via
the same `substitution_block` as class A's datasets. A capped graph or a
non-hitting vertex aborts; only the three exact screening refusals (reducible,
non-Pisot, imprimitive) mark a member as outside the PIP domain.

**Domain (finite observation, d = 5..30).** The first PIP member is
`n = 2d − 5` (plus) and `n = 2d + 1` (minus); the members just below are
refused by screening.

**Frozen tail.** For every gap `5 ≤ d ≤ 30` and every `n` from `4d` (plus) or
`4d + 4` (minus) to 24 beyond, all members have **the same** label set:

| sign | members compared | labels | typed rows |
| --- | ---: | ---: | ---: |
| plus | 650 | 196 | 77 |
| minus | 650 | 214 | 81 |

The common sets are written out in the packet. The member just below each
onset has a different set (negative control in
`kernel/tests/test_class_c_gap_profile.mojo`). The gap-5 note's per-line tail
vertex counts (196, 214) are the `d = 5` case; that the set is the same for
every gap is new here. The per-line checker needed floors 62 and 132 at gap 5,
far above `4d = 20`: without the frozen structure it pays for every member.

**Strip.** Below the onset the graphs are larger and shrink with `n`. Along a
diagonal `n = 4d − j` the vertex count becomes constant in `d` past a floor
that grows with `j` (tables `diagonals-*.txt` in the packet, `j ≤ 16`,
`d ≤ 30`). For large `d` every diagonal `10 ≤ j ≤ 16` reaches 280 vertices
(plus) and every `4 ≤ j ≤ 16` reaches 250 (minus), with a transient wave
between that repeats one step lower on each next diagonal (`n − 3d` fixed).
On plus the 21 members `n = 4d − j`, `10 ≤ j ≤ 16`, `d ∈ {20, 25, 30}` share
**one** 280-label set: a second frozen regime inside the strip. On minus the
same window is not yet settled at `d = 20` (counts 250, 252, 258). Near the
domain edge (`n ≈ 2d`) the counts grow with `d`, by about 150 per step. Every
strip member hits.

## Decision

**Go** for Theorem T_C on both signs: one frozen finite graph per sign,
certified on the tail cone by exact signs on a compact `(h, u)` box. The floor
`c_eps` is whatever the certificate accepts; the tail members below it and
the strip are not covered.

**Redirect** the strip `2d − 5 ≤ n < 4d + c` (plus), `2d + 1 ≤ n < 4d + c`
(minus) to a separate stop/go after T_C. Its middle band looks like a second
frozen regime that the same certificate shape could cover, but the transient
wave and the near-edge regime grow, as class A's `n < 5d` strip does.

## Non-claims

- Nothing here is uniform in `n` or `d`: the profile is finite (gaps 5–30,
  `n ≤ 4d + 28`), and the onsets `4d`, `4d + 4` and the domain starts are
  observations.
- No BH, G1 or PSC claim changes; class C gaps `d ≥ 6` remain open.
- The Perron algebra above is a derivation for the design, not yet checked
  by an executable certificate.

Replay commands and the full profile are in
[the packet](../evidence/class-c-gap-profile-2026-10-28/README.md).

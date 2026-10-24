# Direct lines of attack: how #84, #138 and #139 have narrowed (2026-10-23)

**Status:** orientation and planning surface. It changes no claim status,
proof-ledger node or manuscript statement. When it disagrees with
`claim_governance.toml`, the [proof ladder](proof-ladder.md), the
[roadmap](research-roadmap-2026-09-21.md) or the manuscript, those control.
Pinned baseline: `main@a08079b`.

The three trackers are open because their universal statements are unproved,
not because the targets are unchanged. Each target is now much narrower than
its original issue text. This note records the narrowing, so that effort goes
to the shortest remaining distance to the objective.

## 0. The objective and the shortest chain

```text
PIP (ternary, standing regime, non-unit allowed)
=> finite seed-patch overlap graph                     [proved]
=> closed recurrent obstruction normal form           [proved]
=> A1′ (#138)  +  BH (#139)                            [OPEN — the only gap]
=> one-seed overlap productivity (#84)                 [proved assembly]
=> pure discrete spectrum                              [proved + imported]
```

`thm:two-obstruction-completion` turns #84 into exactly `A1′ ∧ BH`.
**#84 therefore has no independent work target.** It closes when #138 and
#139 close. The by-products are:

- **BH alone ⇒ G1** (Proposition 4 / Corollary 5 of the
  [overlap-depth note](bpa-termination-by-overlap-depth-2026-10-02.md),
  manuscript Proposition 5.47). #139 is the highest-leverage branch.
- **PDS ⇒ G1** is already repository-proved (`PDSImpliesRepoG1`), so #44's
  renewal route is a parallel structural programme, not on the direct path.

## 1. How each target narrowed

| Tracker | Original statement | Current exact target | Narrowed by |
| --- | --- | --- | --- |
| **#84** | every swap seed (or every overlap) productive | **one** swap seed productive, and only via `A1′ ∧ BH` | Theorem 5.38 (one seed suffices); two-obstruction completion theorem |
| **#138** | two-sided all-pairs strong coincidence (Arnoux–Ito), for σ and its reversal | **one-sided A1′**: the two letters of the residual bad hub edge, both fixed by the first-letter map, are eventually coincident | endpoint normal form (C/D/E/F), Barge–Diamond good edge, squaring reduction; reversal is not a premise |
| **#139** | no closed nonproductive SCC (exclude every bad cycle) | **BH**: every *cyclic, seed-reachable, strict-zipper* vertex has *some* composable, occurrence-indexed child path to offset zero | bad-SCC dichotomy (aligned vs strict zipper); half-coincidence suffices (equal letters not needed); existential descendant, not "every edge descends" |

## 2. What is already settled inside the narrowed targets

### #138 / A1′

- **Theorems E, H, K** ([A1′ note](p1a-a1-prime-2026-10-05.md)) prove all-pairs
  strong coincidence on the **whole catch-up-free `|det M| = 2` class**, for
  every image length. The only exception is a residue of Theorem K's one
  explicit family `F` (`σ(o)=y, σ(y)=o w₁ o, σ(z)=o w₂ o`). Inside `F`,
  Lemma Φ2 handles the crossing members, and Theorems Φ, Ψ, Ξ and Λ/Λ′/Λ″ close
  whole cells of the non-crossing part. Only the remaining non-crossing cells
  are open.
- **Finite domain:** `SC_all` holds on all 408,798 substitutions of total image
  length ≤ 10, and Theorem Ω gives PDS on 145,806 substitutions.
- **Attack interface:** A1′ is equivalent to proximality of the two fixed hub
  rays σ^∞(x), σ^∞(c) ([proximality note](p1a-a1-proximality-2026-10-19.md)).
  The [length-window lemma](two-obstruction-moment-interface-2026-10-20.md)
  reads Parikh defects from three length observations.

### #139 / BH

- On the catch-up-free `|det M| = 2` class, **PSC ⇔ PPVC ⇔ BH** outside the
  open part of `F` ([Proposition Z](p1b-catch-up-free-ppvc-2026-10-07.md)).
  On that class the strict zipper is *the* remaining problem.
- Within Theorem E's normal form `x→x y^p s_x, c→c y^q s_c, y→t y^r s_y`, the
  following are proved. They are computer-assisted, each at the acceptance
  scope its own note records, and independent human review is pending. A and
  C are the two-parameter `(q, d)` domains of the
  [run-index note](p1b-class-a-run-index-2026-10-21.md), with one line per gap
  `d` and sign:

  | Class | Proved | Remaining in class |
  | --- | --- | --- |
  | D | every PIP member ([assembly audit](class-d-assembly-audit-2026-10-21.md)); explicit finite-BPA bounds on `b=0` ([corollary](class-d-g1-corollary-2026-10-22.md)) | none |
  | B | everything below slope 5/2 ([Theorem C](p1b-symbolic-cone-2026-10-08.md)) | the top layer: `r=q±1` sectors with slopes accumulating at 3 |
  | A | gaps `d ≤ 4`, both signs, each line on its whole domain ([d=4](class-a-d4-rays-2026-10-23.md)) | one line `(n+d, n, n±1)` per gap `d ≥ 5` |
  | C | gaps `d ≤ 5` ([gap 4](issue139-ac-gap4-2026-10-22.md), [gap 5](issue139-gap5-2026-10-23.md)) | gaps `d ≥ 6` |

- **Calibrated limits.** No parameter-independent hitting depth exists on
  class A (`n/10 < L_n ≤ n+2`, [run-index note](p1b-class-a-run-index-2026-10-21.md)).
  A rank therefore has to be parameter-dependent and run-indexed.

## 3. The direct lines of attack, in order

1. **A d-uniform BH certificate for classes A and C.** The
   [gap-uniformity stop/go](class-a-gap-uniformity-stopgo-2026-10-23.md)
   decided *proceed, narrowed*. Per-regime label sets fit exactly and depend
   only on `l` (`n = d l + r`). The open obligation is a Perron sign lemma in
   `(h, u = d h)` plus the rounding by `d`. This replaces infinitely many
   per-gap tables with one certificate, and its stop condition is a failed fit.
2. **Finish A1′ on Theorem K's family `F`.** Close the remaining non-crossing
   cells. Together with (1) and the class-B top layer, this makes PSC on the
   whole catch-up-free `|det M| = 2` class reduce to BH alone.
3. **The class-B top layer.** This needs vertex families indexed by an extra
   variable and an inductive hitting argument. The constant-graph method
   certifies each sector but cannot exhaust them.
4. **Leave the class: BH in the full non-unit representation.** Supply a
   *good-branch existence* mechanism over every child-closed nonproductive
   candidate. One alternative legal child settles a vertex, as the
   [Nakaishi family](nakaishi-2024-first-entry-audit-2026-10-13.md) shows. The
   mechanism must keep the finite-place (M-adic) coordinates of the
   Minervino–Thuswaldner representation.
5. **A1′ off the class via fixed-ray proximality.** This uses the 2026-10-19
   reformulation; it is not yet a theorem.

Lines 1–3 finish a complete infinite class; lines 4–5 are the universal step.
A proof of 4 together with 5 closes #139, #138, #84 and PSC in the standing
regime.

**Lateral moves** — extending each scoped closure to neighbouring territory by relaxing one
load-bearing hypothesis — are ranked in the
[lateral-generalization strategy](lateral-generalization-strategy-2026-10-23.md). Its first move
shows classes A, C, D are conjugacy-isolated, while every Theorem C class-B member has
`min(p,q,r)+1` catch-up-regime conjugates with pure discrete spectrum.

## 4. Retired routes: do not spend cycles here

- **Cycle algebra and affine pumping:** a zero-shift-free six-edge cycle sits
  inside a productive graph.
- **Bounded collars:** a collision is not separated at any radius ≤ 12.
- **Generic Perron growth:** `ρ(N_S) = β` is the hard case, not a contradiction.
- **Contracting lower bounds** point the wrong way for forcing a hit.
- **Rank deficiency:** the intersection-vector span always has full rank.
- **One-tile / catch-up reduction:** there are catch-up-free specimens, and
  one-step M-adic ascent fails on all of them.
- **Literal transport** of a `b=0` spine to `b>0`: a rank-one update refutes it.
- **"Every edge descends":** this would reject productive graphs.
- **Euclidean-only or unimodular projections** in the non-unit case.

Each item has a dated entry in the [side-notes ledger](side-notes-ledger.md).

## 5. Firewall

Each of the following is an exact scoped theorem or proof interface, and none
of them closes a tracker:

- a family certificate;
- a finite-domain census;
- a fixed-ray reformulation;
- a closed tracker issue.

#138 and #139 close only on universal A1′ and universal BH, with no added
legality, FI, tile-length independence or unimodularity hypothesis. They close
through the governed ledger.

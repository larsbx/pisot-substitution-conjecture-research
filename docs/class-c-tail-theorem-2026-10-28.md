# Class C, gaps d ≥ 6: Theorem T_C, the frozen tail (2026-10-28)

**Status:** repository-proved, computer-assisted, at the stated scope; local
native validation complete; hosted acceptance and independent human review
pending. Design and prior art:
[class-c-gap-uniformity-stopgo-2026-10-28.md](class-c-gap-uniformity-stopgo-2026-10-28.md)
(decision: go). Canonical code: `kernel/psc/class_c_tail_certificate.mojo`,
driver `kernel/class_c_tail_certificate.mojo`. Packet:
[`evidence/class-c-tail-theorem-2026-10-28/`](../evidence/class-c-tail-theorem-2026-10-28/README.md).

## Statement

The class-C lines are

```text
sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,   sigma(y) = c y^(n-d+eps) c,   eps = ±1.
```

**Theorem T_C (scoped, computer-assisted).** Let `d >= 6`, and let
`n >= 4d` (`eps = +1`) or `n >= 4d + 4` (`eps = −1`). Then the member is PIP,
and its complete canonical swap-seed overlap graph has **exactly** the label
set `F_eps` of the profile packet (`frozen-tail-plus.txt`: 196 labels in 77
typed rows; `frozen-tail-minus.txt`: 214 labels in 81 rows). Every vertex has
an offset-zero descendant.

So boundary hitting (BH, #139) holds for every class-C member with gap
`d >= 6` on these tails, uniformly in `d`. Together with gaps `d <= 5`
([gap 4](issue139-ac-gap4-2026-10-22.md), [gap 5](issue139-gap5-2026-10-23.md)),
class C's open BH residual narrows to the strip
`2d − 5 <= n < 4d` (plus) and `2d + 1 <= n < 4d + 4` (minus). Those lower ends
are the observed PIP domain starts of the profile, not proved bounds.

## Proof

**Parametrization.** Put `s = (s1, s2) = (d, m)` with `n = 4d + c + m`, where
`c = 0` (plus) or `c = 4` (minus). The three run lengths
`(n + d, n, n − d + eps) = (5 s1 + s2 + c, 4 s1 + s2 + c, 3 s1 + s2 + c + eps)`
are affine in `s`, with first letters `(x, c, c)` and last letters `(x, x, c)`.
So each class-C tail is a two-parameter cone in the sense of
[p1b-symbolic-cone-2026-10-08.md](p1b-symbolic-cone-2026-10-08.md) §2: the
symbolic seed-graph closure of `psc.symbolic_cone`, with signs certified on
the integer region (Pólya) and signs at `beta` read on certified brackets.
Class C was not run on that engine before. The engine itself is unchanged;
only the class-C cone, its brackets and the cover are new.

**Brackets.** With `ell_y = 1`, the left eigen-equation `ell M = beta ell` of
`M = [[2,1,0],[0,1,2],[n+d,n,n−d+eps]]` reads `ell_x = (n+d)/(beta−2)`,
`ell_c = (ell_x + n)/(beta−1)`, `beta = (n−d+eps) + 2 ell_c`. So `beta` is
the fixed point of the decreasing map
`g(x) = (n−d+eps) + 2 (n + (n+d)/(x−2)) / (x−1)`. The driver proposes
`[x0, x1]`, `[x2, x1]` and `[x2, x3]` for the iterates `x0 = n−d+eps+2`,
`x_{k+1} = g(x_k)`. These are proposals only: `certify_cone` checks
`chi(L) < 0 < chi(U)` and `L > |det M| = 2` on the region, and proves PIP
(primitive support, `det M = 2 eps`, no rational root among `±1, ±2`, the
other two roots in the open unit disc by Rouché or Jury) before any sign at
`beta` is read.

**Pieces.** A *piece* is a cone (`d >= d0`, `m >= m0`), a diagonal
(`m = m0`, `d >= d0`) or a gap line (`d = d0`, `m >= m0`).
`certify_piece` runs the closure. By Lemma S′ of the cone note, if it
finishes, then at every integer point of the piece the exact seed-reachable
overlap graph is the symbolic graph with `s` substituted. `certify_piece`
then refuses unless:

1. every symbolic vertex has an offset-zero descendant (reverse reachability
   on the symbolic graph, valid at every point by Lemma S′);
2. every vertex offset `w` is a constant integer vector, so the label set is
   the same at every point of the piece;
3. as a cross-check only (not part of the proof), the symbolic graph equals
   the exact graph of `psc.overlap_seed_patch` at one interior member.

**Cover.** `cover` (as in class B's `class_b_cone_certificate`) tries the cone
at shifts `k = 0, 1, 2, …` and recurses on the strips a shift leaves: gap lines
`d = d0 + j` (`m >= m0`) and diagonals `m = m0 + j` (`d >= d0 + k`), `j < k`.
A line in turn is certified from its first certifying shift, and the members
below that shift are decided by the exact kernel (complete graph, every
vertex hitting, which `c_block` enforces). Every piece and member must give
one label set, or the cover raises. The run (both signs alike):

| region | how | label set |
| --- | --- | --- |
| `d >= 8`, `m >= 2` | symbolic cone (shift 2) | `F_eps` |
| `d = 6`, `m >= 2`; `d = 7`, `m >= 2` | symbolic gap lines (shift 2) | `F_eps` |
| `d = 6, 7`, `m = 0, 1` | 4 exact members | `F_eps` |
| `m = 0`, `d >= 8`; `m = 1`, `d >= 8` | symbolic diagonals (shift 0) | `F_eps` |

These five symbolic pieces and four members exhaust `{d >= 6, m >= 0}`. The
shifts are needed because some intermediate decisions of the closure (a run
end clipping a realness interval) change sign inside the region, though the
label set does not. At `d = 6` one such sign at `beta` is that of
`−m t^2 + (3m + 18) t − (2m + 36)`: positive at `m = 0` and negative for
`m >= 1` (`t = beta ≈ 3d + 3`). So the pieces at shifts 0 and 1 refuse ("a
sign at beta is not decided on any bracket"); at shift 2 every decision
certifies.

Finally, the common label set the cover prints is compared byte for byte with
the profile packet's `frozen-tail-*.txt` rows: equal on both signs. `square`

## Derivation of the design, and what changed

The stop/go note planned a new certificate with exact signs on a compact
`(h, u)` box. A Python prototype (scratch, not committed) confirmed the plan's
structure. Over the cone, the strict y-window of each child type stays within
a fixed integer bracket, and run-index realizability is affine in `(n, d)`.
With sampled signs, the symbolic closure from the seeds reproduced `F_eps`
exactly at `d0 = 6`. The repository's existing two-parameter cone engine
already decides exactly those questions: realness and run-position ranges as
certified region signs plus signs at a bracketed `beta`. So T_C reuses it
instead of adding a second sign engine. The onset at `4d` is visible there.
With `h = 1/beta`, in the limit `h → 0` the window ends are affine in
`u = d/beta`. On the tail `u < 1/3` (since `beta > n − d + 2 + eps`), and the
first window crossings sit at `u = 1/3`. This is the prototype's heuristic for
why the frozen set starts near `n = 4d`; it is not used in the proof.

## Evidence and replay

From `kernel/`:

```
mojo run -I . class_c_tail_certificate.mojo theorem 1     # plus, d >= 6, n >= 4d
mojo run -I . class_c_tail_certificate.mojo theorem -1    # minus, d >= 6, n >= 4d + 4
mojo run -I . tests/test_class_c_tail_certificate.mojo
```

The theorem logs (one line per piece, refusal or exact member, then the label
set), their comparison against the profile packet, timings and the test
receipt are in the packet.

## Negative controls

- **Below the onset:** the diagonal `n = 4d − 1` (plus) certifies just as
  uniformly for `d >= 8`, but with a different, 198-label set. Likewise
  `n = 4d + 3` (minus), 216 labels. The certificate does not return `F_eps`
  by construction.
- **Refusal, not decision:** gap 6 from the onset (`d = 6`, `m >= 0`) refuses
  on an undecided sign at `beta`, as does the shift-0 cone. The cover moves on
  to a shift; it never treats a refusal as a verdict. Any other error (PIP
  failure, non-hitting vertex, non-constant offset, failed cross-check)
  aborts the cover.
- **One set:** the cover's agreement check refuses a second label set.
- **Malformed pieces** (sign `0`, gap floor `< 2`, unknown kind, a corner
  outside the normal form) refuse.

## What is trusted

- **Proved by hand:** Lemma S′ of the cone note and the sufficiency of its
  region and bracket certificates (unchanged); the coverage argument above
  (five pieces and four members exhaust `{d >= 6, m >= 0}`); the eigen-equation
  derivation of the bracket map (proposals only, so its correctness is not
  load-bearing).
- **Trusted:** the Mojo implementation of `psc.symbolic_cone` (the engine of
  class B's Theorem C, reviewed by its author only), the exact kernel for the four members, and the
  new driver code in `psc.class_c_tail_certificate`.
- **Cross-checks, not part of the proof:** one exact graph per piece; the
  byte comparison with the independent profile packet; the regression test.

## Non-claims / remaining gaps

- Class C's strip `2d − 5 <= n < 4d` (plus), `2d + 1 <= n < 4d + 4` (minus) is
  open for every `d >= 6`, as is the exact PIP domain start there. The profile
  saw a second frozen regime in the plus strip (`n = 4d − j`, `10 <= j <= 16`)
  and diagonals that freeze in `d`. The `4d − 1` control suggests that each
  diagonal may certify on its own; that is a separate stop/go.
- Only BH (all-seed boundary hitting) is proved. No pure-discrete-spectrum,
  G1 or PSC claim is made for these members. Any such consequence needs the
  same additional inputs as the gap-5 lines.
- No claim status changes in `claim_governance.toml`. The completion
  ledger's obligation 1 (class-A strips, class-C `d >= 6`) is narrowed for
  class C to the strip above, not discharged.
- Independent human review is pending.

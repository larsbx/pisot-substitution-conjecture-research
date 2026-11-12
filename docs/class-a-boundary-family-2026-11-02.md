# Class-A boundary children: one skeleton (2026-11-02)

Audit item B1 of [dry-optimization-audit-2026-11-02](dry-optimization-audit-2026-11-02.md).
Refactor only: no claim, count, certificate or ledger status changes.

## What moved

Every `kernel/psc/class_a_boundary_<L>_children.mojo` repeated three loops around
its own tables and proofs. They now live once in
`kernel/psc/class_a_boundary_family.mojo`, over a `BoundaryFamily` trait
(`name`, `source`, `parameters`, `swapped`, `allowed`, `in_image`):

| Loop | Copies replaced | Now |
| --- | --- | --- |
| synthesize an edge (`_append`) | 24 | `append_child` |
| verify a packet (`verify_<L>_packet`) | 22 | `verify_child_packet` |
| verify a star (`verify_<L>_star`) | 15 | `verify_child_star` + `duplicate_occurrence` |
| `_dimensions` (n, d, A, n-1 with a slack bound) | 17 | `boundary_dimensions(k, t, slack)` |
| `_extend` | 4 | `extend_edges` |

Each converted module keeps its public API (tests and drivers are unchanged) and
declares a ten-line `<L>Children` struct binding its guard, image, source,
orientation and dimensions. Counts, child stars, paths, walks and `certify_<L>_children`
remain per label: they are the per-label mathematics.

Converted: b3 b4 b5 d0 d5 e2 e6 e7 f h5 h9 j8 j9 p p3 p9 r3 r4 r5 tx w9 y4
(append + packet, plus star where present), e h3 (append only: their packet
checks the guard but not the image), q3 (dimensions only). Left alone: h4, tm,
u, w, whose signatures differ (no `kind`, a run index `m`, or no image check in
the packet). Only exact canonical bodies were rewritten; the conversion
refused anything else.

## The one semantic change: the duplicate key

The old stars keyed an occurrence (i, j) as `i*s + j` with a hand-picked
stride `s` per module (`A+2`, `n-1+2`, and in p9 kind 0 `n+1`). That is
injective only while every `j < s`. `duplicate_occurrence` uses
`s = max j + 1` over the star itself, injective by construction, and refuses a
negative index. On every valid star both keys agree on "no duplicate"; the new
key can only stop a false collision. Error message wording is unified
(`"<L> packet refused"`, `"incomplete <L> star"`, ...); no test asserts message
text.

## Evidence and replay

Before/after program output of every test and driver that transitively imports
a children module (42 tests, 32 drivers), each with `mojo run -I . -I tests`:
the baseline from a worktree at `68b9c39`, the refactor from this commit.
Stripped of compiler diagnostics (paths and line numbers), all 74 outputs are
identical, 6,177 lines, with identical exit codes. Two consumers fail
identically on both sides: `class_a_finite_hub_integration.mojo` needs
arguments, and `tests/test_class_a_prefix_carry.mojo` does not compile at the
baseline.

`kernel/tests/test_class_a_boundary_family.mojo` pins the shared contract: the
H9 (`kind!=0` orientation, fixed-kind dimensions), B3 and P9 (the two old
strides) and F (`kind%2`) stars rebuild and verify through the generic
functions on every k<3, t<3 member, and a duplicated, a dropped and a mistyped
edge, a disallowed occurrence, the pair the old p9 stride conflated, a negative
index and a dimension overflow are refused.

The edited modules are pinned by evidence source manifests; each change is a
declared drift in `source_pins.toml` pointing here. Replaying an archived
packet means checking out its recorded revision.

## Non-claims

No proof, count or certificate is re-derived; equal output is a regression
over the existing finite sweeps, not a proof of equivalence on unbounded
parameters. Net size change is small (about −40 lines including the new
module) because each module now carries its binding struct; the gain is one
implementation of each verifier instead of up to 24.

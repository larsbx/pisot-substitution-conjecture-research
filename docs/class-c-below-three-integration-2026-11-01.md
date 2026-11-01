# Class-C #394: proof dependencies and integration (2026-11-01)

Inspected #394 head `b3f22ecad5ccd53510f6291a4e6d83fbfbca867c` against main
`3967ab32384e4add7c6d42a7519f42932c8625cb`. Main is already an ancestor;
GitHub reports mergeable. No further conflict resolution is needed.
This audit reconciles mathematical dependencies and source provenance. It
does not certify the trusted engine independently or prove general PSC.

## Replacement of the upper-region dependency

All objects use class C
`x -> xy^(n+d)x, c -> cy^n x, y -> cy^(n-d+eps)c`, eps=+1/-1,
integral bottom-minus-top offsets, the complete **canonical swap-seed**
graph, and offset zero as target. In particular, none silently replaces
that graph with the full legal-overlap graph.

| Dependency | Exact scope used | Accepted mainline source |
|---|---|---|
| T_C | d>=6; n>=4d plus / n>=4d+4 minus; every vertex hits offset zero | [tail theorem](class-c-tail-theorem-2026-10-28.md), #384 merge `40823631` |
| T_C2 | d>=1; 3d<=n<4d plus / 3d<=n<4d+4 minus; same hitting target | [strip theorem](class-c-strip-theorem-2026-10-29.md), #399 merge `242c831a` |
| Union at the required gap | d>=6, n>=3d, both signs | Both merges are ancestors of inspected main |
| Superseded #392 | d>=6, n>=3d+4 plus / n>=3d+6 minus | Strictly contained in the union; no longer a premise |

The statements include PIP before graph closure. T_C2 permits several label
sets, as does the new assembly; no single-label-set hypothesis is imported.
The exact integral sector inverse and root-identification audit remain
unchanged. This is an independent inspection of dependency sufficiency,
not independent mathematical certification of the engine or theorems.
Their documents' historical hosted/human-review labels are not rewritten.

Every load-bearing reference to #392 in the current derivation and stop/go
has been replaced. Original packet README/provenance references are retained
as immutable history and are interpreted by this dated reconciliation.
The original stop/go budget is not retrospectively reduced.

## Integer cover, including the edges

Use (A,B)=(8,16) plus or (16,8) minus and require d>=6, 2n>=5d+A.
If n>=3d, use the theorem union. For n<3d:

- d>=32, n<=3d-B: `u=2n-5d-A`, `v=3d-n-B` are nonnegative
  integers and invert to `d=A+2B+u+2v`, `n=3A+5B+3u+5v`.
  The determinant is -1, so there is no missing parity class.
- d>=32, n>3d-B: integer c=n-3d is -15..-1 plus or -7..-1
  minus. Every required line is certified from d=32. Its frontier
  intersection is d>=A-2c; that follows directly from 2n>=5d+A.
- 6<=d<=31: every required n<3d occurs in the finite records. The
  recorded A=8 minus set contains the selected A=16 minus set. The
  finite upper limits 3d+3/3d+5 exceed the needed 3d-1.

Thus no new gap is introduced. The four minus floor-48 tails and 52 prefixes
are not used by this cover. Extra c>=0 lines and upper finite members also
need no new justification: they stay as certificates at their own scope.
The [derivation](class-c-below-three-2026-10-29.md) gives the universal
integer argument. The new bounded native audit checks d=6..64, n=0..400;
its Python counterpart reads the actual line plan and finite CSV. The grid
is an error detector, never the universal proof.

## All 142 original changed files

The [machine-readable audit](../evidence/class-c-below-three-integration-2026-11-01/audit.json)
lists every original path, Git blob identity, category and decision.

| Category | Files | Decision |
|---|---:|---|
| New #394 sector/line/end/refusal/control evidence | 79 | Preserve every byte, including all surplus/failed attempts |
| New #394 kernel, test, oracle, derivation, stop/go and workflow | 7 | Required new result and replay surfaces; reconcile prose and gate |
| Inherited #392 evidence | 48 | Preserve immutable record; redundant as a theorem dependency |
| Inherited #392 replay source (driver/module/test/oracle) | 4 | Keep pinned paths for reproducibility and negative controls; below-three imports none of them |
| Inherited #392 derivation and stop/go | 2 | Preserve historical experiment; add explicit supersession notices |
| Inherited #392 active workflow | 1 | Retire duplicate acceptance gate; archive its exact bytes with checksums |
| Append-only side ledger | 1 | Keep both histories; append correction |

The size is dominated by complete evidence, not 142 necessary new proof
components. Removing historical evidence or its pinned replay sources to
shrink the diff would destroy useful provenance. The redundant automatic
workflow is the only retired execution surface. The historical native test
remains an ordinary regression; its original receipt is not called a fresh
source-attested acceptance result.

## Source-provenance failure and repair

All 66 current #394 source hashes match. Both original packets' checksum
manifests verify. All 67 inherited #392 source hashes match the exact original
commit `82dc6955faf68df5ee31292b9c2dd503b325a123`. Three differ from current
source: `kernel/pixi.toml`, `kernel/psc/class_c_tail_certificate.mojo`, and
`kernel/psc/symbolic_line.mojo`. Those changes were introduced on main by
additive tasks, T_C2's STRIP frame and fit-first line closure. Their old and
current digests are explicitly inventoried in `audit.json`.

The inherited workflow incorrectly checked those historical digests against
current sources. Its source step would fail even if all replay outputs agreed.
It is archived, not patched into a fictitious current attestation. The new
provenance guard validates the original pins against original Git bytes,
requires precisely the inventoried current drifts, and validates #394 pins
against current files. It also freezes every byte of both original packets
and the two theorem statements used by the replacement argument. No original
receipt, checksum, provenance record or evidence README is modified.

The previous below-three rebind `8450a9dc` remains unchanged, including its
recorded replay on `3aaf2b48`. It is neither erased nor treated as evidence
that this session reran those earlier jobs.

## Acceptance and remaining debt

Local: the original 746-graph below-three oracle and the 547-graph historical
slope-three oracle reproduce their recorded JSON byte for byte. The original
native regression and the new mainline assembly regression pass. The new
independent assembly oracle matches native counts. Negative controls remove
a required plus/minus bridge or a required minus finite end and must refuse.
Full native plan replay and repository checks are recorded separately in the
supplemental packet when complete; historical outputs are never overwritten.

The dedicated workflow now checks out the explicit PR head, validates the
integration provenance with full Git history, replays both original sign
plans and compares the new assembly receipts. Final exact-head hosted
acceptance must pass before merge. Queued jobs are not successful receipts.
Independent human review stays pending separately; governed claim status,
PSC, legal-overlap realization, G1 and non-unit transfer are unchanged.


## Follow-up source audit and clean test environment

The separate [validation supplement](../evidence/class-c-below-three-validation-2026-11-01/README.md)
adds a tokenizer-based import audit. All 57 local Mojo imports are present in
the original source pins. The actual external roots are `std` and `max`;
`a`, `it`, and `the` in historical metadata are comment/docstring artifacts.
The Python entry point also executes package initialization from
`reference/psc_research/__init__.py` and `reference/psc_research/bpa.py`.
Those two implicit sources were omitted by the original manifest; their
hashes are recorded in the new supplement and checked without changing the
old provenance. Original graph comparisons were run with those same bytes.

A full Python-suite collection attempt exposed an existing undeclared SymPy
dependency in three Class-A symbolic tests. Development dependencies now
include the tested `sympy==1.14.0`. The repaired environment collects those
tests successfully. This changes no certificate or mathematical hypothesis.

The dependency edit initially failed the separate Class-D provenance guard,
which intentionally pins historical `pyproject.toml` bytes. That refusal is
preserved in the validation supplement. The guard still verifies those old
bytes against the accepted Git object. A named, regression-tested exception
now admits only appending exactly `sympy==1.14.0` to the existing development
requirements, with every existing dependency, production requirement,
Python/build setting and other TOML value unchanged. The three pinned
historical Class-D Python sources do not import SymPy. Any changed existing
requirement, alternate SymPy version/range, production dependency, Python
version constraint or build setting still refuses. This is an explicit
integration-policy change, not a re-pinning of accepted evidence or a fresh
CI attestation. All 43 Class-D integration/rebind regressions pass; the final
branch still requires its own complete hosted acceptance before merge.

Fresh local replay is complete: all 53 declared native receipts, including
both selected sectors, 40 line families, 52 prefixes, 520 finite end members,
coverage outputs and controls, are byte-identical. All four original native
regressions (below-three, historical slope-three, T_C, T_C2) reproduce their
receipts. The supplement records 746+547 complete independent graph comparisons
and 152 passing focused Python tests. A broader suite run was interrupted
and is not recorded as a pass; its three observed provenance failures were
reproduced and repaired by the narrow dependency guard above. Final-head
hosted full-suite acceptance remains required. No general PSC or independent
proof-certification claim follows from these local results.

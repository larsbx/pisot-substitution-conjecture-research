# Audit of Theorem Ω and the finite-domain PDS certificate — 2026-10-08

## Scope and decision

The mathematical and implementation snapshot is PR #233 final head
`72f173dbc8dc0de1e5e13503b2911e0411d1fda8`, not its earlier `0871ada` head.
The PR merged as `cb9db58c9e25209c2a54ccd6955b509af88e8356`; the two trees
are identical. The merge also introduced `BoundedPureDiscreteSpectrum` with
status `finite-domain`. This audit does not change that status or promote any
other claim. The prior author's re-derivation and the earlier automated P2
review are not independent acceptance of the final mathematical argument.

Decision: proceed with exact representative replay and a separate review of
the sufficiency route. The finite-descent proof has no failed step identified.
The literature bridge needs explicit normalization, a substitution-power
argument, the signed overlap dictionary, and the flow-to-subshift import.
Independent mathematical review remains an acceptance condition. The completed
current-head census below supplies computational evidence; a workflow that has
only started is not completed evidence.

## Literature stop/go

The target is box productivity ⇒ formal productivity ⇒ PDS for one primitive
irreducible Pisot substitution. The sources inspected directly are:

| Source | Exact use | Hypothesis boundary |
| --- | --- | --- |
| Lee–Moody–Solomyak, *Consequences of pure point diffraction spectra for multiset substitution systems*, [arXiv:0910.4450](https://arxiv.org/abs/0910.4450), Theorem 4.7, Definition 6.7, Lemmas 6.8–6.9 | Realized overlaps, their subdivision graph, and coincidence reachability ⇒ PDS | A repetitive fixed tiling of a primitive substitution; Meyer return vectors. No unimodularity. |
| Lee–Solomyak, *Pisot family self-affine tilings, discrete spectrum, and the Meyer property*, [arXiv:1002.0039](https://arxiv.org/abs/1002.0039), Definition 2.7, Corollary 2.13, Theorem 4.3 | Pisot inflation gives Meyer control points | Diagonalizable expansion with conjugate eigenvalues of equal multiplicity; scalar expansion in one dimension satisfies this. |
| Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898](https://arxiv.org/abs/1003.2898), Definition 2.4, Theorems 2.5 and 2.7 | Direct return-vector Meyer statement and overlap-coincidence criterion | Quantifies over realized overlaps; its “potential overlap” is not the repository's formal lattice-overlap definition. No unit assumption. |
| Clark–Sadun, *When size matters: subshifts and their related tiling spaces*, [arXiv:math/0201152](https://arxiv.org/abs/math/0201152), Theorem 3.1 and Corollary 3.2 | Perron-length flow conjugate to a constant-roof suspension after rescaling | Primitive aperiodic subshift; exactly one incidence eigenvalue of modulus at least one. PIP satisfies this without unimodularity. |

Proceed for sufficiency. Formal lattice overlaps form a superset of realized
overlaps, so a positive formal certificate transfers. A failed formal
certificate does not by this literature route alone disprove PDS or PSC.
The necessity chain through Theorem S and the Barge coincidence-rank imports
is outside the acceptance decision here.

## Proof audit

Normalize the positive left Perron vector in `Q(beta)^3`. Its coordinates are
a rational basis of that degree-three field. The Minkowski embedding of their
integer span is a full-rank lattice: use all real embeddings, or the Perron
embedding and the real and imaginary parts of one complex embedding.
Injectivity alone would not prove discreteness; the invertible embedding
matrix does.

For each contracting embedding, descendant offsets satisfy
`t' = beta t + c`, with `c` in the finite prefix-difference alphabet. The
triangle inequality gives the bound
`|sigma_k(t_n)| <= max(|sigma_k(t_0)|, C_k/(1-|beta_k|))`.
The real overlap condition gives `|t_n| < ell_max`. These bounds put all
descendants in a compact region of that lattice, hence in a finite set.
No inverse incidence map or unit determinant is used.

On a period-p cycle, solve the affine recurrence and use
`|1-beta_k^p| >= 1-|beta_k|^p`. Summing the geometric series bounds every
contracting coordinate by `C_k/(1-|beta_k|)`. The trace-dual basis gives the
coordinate radii; a complex pair contributes twice its modulus bound.
Every cycle offset therefore lies in the box start set. The implementation
scans a larger set on its solved coordinate, which preserves containment.

A nonproductive vertex has no productive child. Inflated intersecting open
intervals have at least one intersecting child pair. An infinite choice of
nonproductive children repeats a vertex in the finite descendant set, giving
a nonproductive cycle contained in the box. This contradicts box productivity.
The reverse implication follows because all box states are formal overlaps.
Stopping expansion at coincidences preserves this reachability predicate.

For the literature bridge, anchor `y+T` at zero and set
`t = u_j-u_i-y`. Endpoint differences and same-type return translations are
integer sums of tile lengths. Child offsets are exactly
`beta t + prefix_bottom-prefix_top`; coincidence means equal types and zero
offset. This proves inclusion and preserves the relevant descendants, without
identifying the whole formal graph with the realized graph.

A legal repetitive tiling may be fixed only by `sigma^p`, particularly when
the first-letter map cycles. Use that power in LMS. Once a coincidence is
reached it persists under further substitution, so pad each witness to a
multiple of p. The expansion `beta^p` remains Pisot. Uniform witness depth
comes from the finite *realized* graph under the Meyer hypothesis, not from a
uniform bound on the infinitely many formal starting offsets.

Finally, Clark–Sadun Corollary 3.2 conjugates the Perron-length flow to a
constant-roof suspension after scaling. Its time-c map is the product of the
subshift map and the identity on the roof coordinate. Restricting a pure-point
unitary representation to this invariant subspace gives PDS of the subshift.
This supplies the specific import previously called merely “standard”.

## Replay and CI record

The canonical exporter `kernel/omega_box_audit.mojo` calls existing kernels.
The independent oracle `oracles/python/omega_box_audit.py` uses rational
interval sign certification, independent child enumeration, reverse BFS and
Kosaraju SCCs. It checks every exported vertex and edge, complete start-set
coverage and closure, all shortest depths, six aligned pairs, and the integer
coordinates of every recurrent offset. All five specimens passed:

| Specimen | det M | vertices | edges | recurrent | K_V | box D | S |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Tribonacci | 1 | 743 | 1,226 | 14 | 3 | 8 | 1 |
| cube | 3 | 85,287 | 229,578 | 1,166 | 17 | 51 | 7 |
| golden pump | 2 | 61,337 | 137,976 | 716 | 15 | 39 | 6 |
| plastic | 1 | 7,129 | 9,488 | 74 | 14 | 33 | 15 |
| real-secondary `1/02/202` | -1 | 2,835 | 5,638 | 24 | 4 | 10 | 4 |

The local canonical vertex regression passed all seven tests, including the
300 standing and 100 length-4 census slices, the seed-graph omission controls,
and refusal of a capped graph. The oracle rejected four deliberately damaged
Tribonacci exports: missing child, altered depth, wrong field, and a missing
start replaced by a duplicate state. No overlap-kernel defect was identified.

`oracles/python/omega_domain_audit.py` independently screened 42,895 incidence
matrices, weighting image Parikh vectors by integer multinomial counts. It
reproduced 4,554 standing, 135,990 images-at-most-four, 24,486 total-at-most-eight,
14,670 in the intersection and **145,806 in the union**. This supplies an exact
replacement for the historical floating-point intersection count cited in the
older vertex note. Counting specimens is separate from certifying each graph.

The recorded CI checkout is `1c5128de9e4fab2c93f2493c99235f27bd663987`, a PR
test merge, not the source head itself. Both have tree
`86c6b2a5274fca5105a26f1c2e961c8a1864440a`, independently checked through the
Git data API. The repaired workflow filter covers all fourteen local imports,
their five vendored packages and the toolchain lock. There is no remaining
dependency-filter defect identified in that closure.

In the saved CI snapshot:

- research run [37752293821](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/37752293821)
  has successful canonical Mojo, Python, source-provenance, policy, TLA+, Lean,
  and standing vertex-census jobs; the last certifies 4,554 productive specimens,
  none capped, box D = 51;
- larger-domain run [37752294014](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/37752294014)
  has a successful total-length-8 job: 24,486 productive, none capped, box
  D = 104 and largest graph 1,342,201; seven successful length-4 slices
  (01, 02, 03, 04, 07, 08, 11) cover 79,325 specimens;
- length-4 slices 00, 05, 06, 09 and 10 are still running. No completed
  current-head direct-productivity receipt is credited to those five slices.

Receipts and timestamped job-log excerpts are preserved in
[`evidence/omega-box-audit-2026-10-08/`](../evidence/omega-box-audit-2026-10-08/README.md),
with SHA-256 pins and replay commands. Existing earlier evidence is preserved.
The earlier PPVC plus SC_all route remains a separately recorded warrant for
the larger domain; this audit has not independently replayed all its historical
receipts and does not substitute a newly queued workflow for them.

The later `ci-followup.json` snapshot adds successful slices 00, 05, 06 and
10, each with 11,333 formally productive specimens and no caps or failures.
Their timestamped outputs are in `census-followup-excerpts.log`. Eleven
completed length-4 slices now cover 124,657 specimens; slice 09 remains
unfinished. The original snapshot and its excerpts are retained unchanged.

The complete local canonical Mojo suite passed all 68 test files; its
verbatim output is `mojo-suite.log` in the evidence packet. Local verification
results, including environment limitations, are recorded separately below.

The final `ci-completion.json` snapshot records **all thirteen box jobs green**
on the source head, and all twenty main research jobs successful. Slice 09
finished at 10:39:09 UTC. Summing actual productivity outputs over the twelve
length-4 slices gives 135,990, with zero nonproductive specimens, caps or
failures; the independent domain oracle agrees. The total-length-8 job gives
24,486 with the same zero counts. Together with the exact intersection count,
the completed direct census now covers the 145,806-member union. The maximum
box D is 104 and the largest graph has 1,432,357 vertices. The final slice's
timestamped output is `census-completion-excerpts.log`; earlier snapshots
remain unchanged.

## Local verification

| Gate | Result |
| --- | --- |
| `./kernel/run_tests.sh` with the supported Mojo compiler | All 68 files passed; complete claim receipts written. |
| Independent representative replay and negative calibrations | Five complete graphs passed; four damaged inputs rejected. |
| `./tools/verify_all.sh` after the Mojo run finished | 12 checks passed, local Lean build failed, Mojo layer skipped because Pixi is absent. The separately run full Mojo suite above passed. |
| Python suite and all 14 TLA+ models | Passed in the sequential verification run. |
| Ledger, math catalogue, vendoring, source integrity | Passed, generated/pinned surfaces unchanged. |
| Claim governance, including receipt coverage | Passed after the complete Mojo run. |
| Local Lean | Lake cannot detect its installed configuration; no local proof-build success is claimed. The exact-source CI Lean job is green; no Lean source changed. |
| `pixi run test` | Not invoked because Pixi is absent; its underlying canonical `run_tests.sh` was run directly. |

`verification-final.log` preserves the verification-run output. An initial
concurrent run observed partially written claim receipts and failed coverage;
the sequential rerun after Mojo completion passed governance and Python. The
Lean installation error remained. Neither local nor CI Lean checks formalize
the new Theorem Ω or replace independent mathematical review of its imports.

## Acceptance boundary

The dependency reduction has survived this proof and implementation audit after
the stated presentation repairs. This is an audit result, not a new universal
theorem or a status promotion. A separate review must assess the corrected
mathematical bridge; automated code review is not human mathematical acceptance.
The completed census supplies a current-head direct computational certificate
for the stated finite domain. The universal PSC and its open gates remain
open, and the converse route retains its independent literature-review debt.

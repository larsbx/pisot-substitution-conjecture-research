# Refining the physical-mass kernel to the exact PR #515 source

This packet binds the reusable finite-matrix implication to the **source
and exported evidence** of [PR #515](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/515).
It does not claim that the 43,915 concrete coordinates have been decoded
and proved acceptable inside Lean. The mathematical kernel and the
independent Quint model are described in the
[kernel note](physical-mass-kernel-2026-11-08.md); the
[literature decision](physical-mass-kernel-literature-gate-2026-11-08.md)
records why the refinement must retain the geometric hypotheses.

The executable mathematical implementation remains the pinned Mojo source.
The new Python file under `tools/` checks provenance, serialization and
receipt integrity. It introduces no replacement graph constructor,
physical sign test, SCC algorithm or mathematical certificate producer.

## 1. Exact source identity and evidence boundary

| Object | Identity or scope |
|---|---|
| PR #515 source commit | `51dd090a6aefeb92210410a3f7e20d51926d7e86` |
| Source Git tree | `25b480b58b5766efdb59c17592c5ae679326a284` |
| Parent, PR #497 | `49bc7e1af11b6ab04f84b79f8737500b6de3748b` |
| Tracked source inventory | 5,543 files, 83,651,515 bytes |
| Entire tracked-content SHA-256 | `c9709a1f4dec111840afcc2842944aaecaac12d408b56a0f2ba005a69c0f700b` |
| Exported physical-mass packet SHA-256 | `9eee6485f202becb8761e52f77e795b34916edf49ce75d6df821bf7fa1646683` |
| Packet size | 1,085,652 bytes, 43,940 records |
| Historical dedicated source run | [42415973913](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42415973913), successful at the pinned source head on 2026-11-07 |

The source commit is unsigned. Here authentication means matching Git
object identities from the repository and matching exact source bytes,
not a cryptographic author signature or an independent proof of geometric
meaning. The compact API observations are in
[`intake.json`](../evidence/physical-mass-kernel-2026-11-08/intake.json).
The historical source workflow succeeded, while several broader source
workflows failed. This is scoped source acceptance, not complete acceptance
of the old branch. The new kernel can be merged independently of the
unmerged #497/#515 stack by replaying this exact source checkout.

The machine-readable
[`source-manifest.json`](../evidence/physical-mass-kernel-2026-11-08/source-manifest.json)
pins the complete Git tree, a SHA-256 framing of every tracked file, 24
reference-file digests, the packet digest and all graph/witness summaries.
[`check_physical_mass_refinement.py`](../tools/check_physical_mass_refinement.py)
checks the actual bytes of **every** tracked file, including files for
which index flags could conceal edits from `git diff`; it also checks
that the index agrees with the tree. Extra `.mojo` and `.py` source files
under `kernel/` and `oracles/` are refused, including ignored files that
could shadow imports. Installed `kernel/.pixi` dependencies and bytecode
cache directories are excluded from that extra-source scan. Other build
products and installed toolchain binaries are outside the source-tree
assertion. The dedicated workflow uses a fresh checkout and the source's
locked Pixi environment.

The mass packet has one schema line, 43,915 `row` records, twelve `block`
records and twelve `graph` records. It contains coefficient triples for
mass and deficit, plus component witnesses and aggregate counts. **It does
not contain the actual state tuples or occurrence adjacency lists.** Those
are reconstructed by the source-pinned programs. A packet hash cannot
replace that reconstruction, nor can it by itself establish SCC membership
or geometric completeness.

## 2. Concrete quantities and transpose orientation

For each of the twelve sources, let `I = Fin n` index
`NewIncidenceGraph.states`. The graph constructor lists all literal
two-step occurrence pairs, retains repetitions, and appends newly reached
states until closure. Its three initial states, with fixed vertex indices,
are

\[
0=(0,1,0,0,0),\quad 1=(0,2,0,0,0),\quad 2=(1,2,0,0,0).
\]

These are the three distinct-letter, zero-displacement roots, repeated
for each source: 36 root instances in total. They are not a declaration
that every strict-PIP problem has these roots.

| Abstract object | Concrete interpretation | Pinned evidence |
|---|---|---|
| `T[i,j]` | Number of entries equal to `j` in `graph.rows[i]`; each literal occurrence counts | `build_new_incidence_graph`, then `authenticate_new_graph` |
| Edge `i → j` | `T[i,j] > 0`, from inverse parent row to inverse child column | Complete repeated-occurrence rows |
| `θ` | `β²`, where `β` is the positive Perron root of `x³ − x² − 3x − 2` | Authenticated source chart and exact polynomial reductions |
| `h_i` | Physical interval length of `[0,ℓ_a] ∩ [−ℓz,ℓ_b−ℓz]` for state `(a,b,z)` | Native exact length coefficients and oracle interval sweep |
| `e_j` | `θ h_j − Σ_i T[i,j] h_i` | Column `j` accumulation in the native deficit loop; omitted forward intervals in the oracle |
| Losing vertex | `e_j > 0` | Exact sign check, then a selected witness in each source block |
| `v_i` | Product-Haar measure of the actual compact overlap represented by state `i` | Written geometric construction of PR #497; not Lean-verified here |

Write

\[
\ell=(1,\beta/2,(\beta^2-\beta-2)/2),\qquad
\ell M^2=\beta^2\ell.
\]

Each packet `row source vertex c0 c1 c2 d0 d1 d2` represents
`h_i = ℓ·c` and `e_i = ℓ·d`. A negative integer coefficient is not a
negative physical length. The source algorithms decide real signs using
certified rational enclosures of the positive algebraic length basis;
an unresolved sign refuses the certificate. The provenance checker only
checks the pinned coefficients and their nonzero declarations. It does
not infer positivity by inspecting signs of individual integer fields.

The native code subtracts the mass of row `i` from deficit **column `j`**
for every occurrence `j` in `graph.rows[i]`. Thus it computes `Tᵀh`.
The independent Python oracle partitions both inflated physical intervals
by their literal ordered positions, sweeps the cuts from left to right,
checks that the total intersection mass is `θh_i`, and checks equality
of the full retained multiplicity counter with the incoming inverse row.
It sums genuinely omitted positive intervals directly. Replacing that
counter by a set loses multiplicity and can manufacture a false deficit.

### Track-swap orbit sizes

The quotient identifies `(a,b,z)` with `(b,a,−z)`. If `m_i` is the size
of its ordered orbit and `F` counts retained physical-forward occurrences
per representative, the required double-counting identity is

\[
m_i T_{ij}=m_j F_{ji}.
\]

Both pinned implementations reject a fixed orbit `(a,a,0)` on this
reachable class. Thus every `m_i=2` and `F=Tᵀ`; the common factor cancels.
For a mixed-orbit application, the correct dual vector is
`H_i=m_i h_i`, since

\[
(T^{\mathsf T}H)_j
=\sum_iT_{ij}m_i h_i
=m_j\sum_i F_{ji}h_i
=m_j(Fh)_j\leq\theta m_jh_j.
\]

The size-two simplification is a source-specific premise. A general
adapter must transport the weighted vector rather than reuse the
unweighted deficit formula without justification.

## 3. Explicit refinement obligations

The following statuses distinguish a generic theorem from an executable
instance and from actual geometry. “Executable” means the pinned Mojo
and oracle contracts, subject to their exact replay receipts; it does
not mean Lean has checked those programs or their output.

| Obligation | Evidence available | Remaining formal or geometric obligation |
|---|---|---|
| Finite, duplicate-free state universe | Native canonical lookup and oracle injectivity check | Decode these concrete states into the Lean index type |
| All retained literal occurrences and their multiplicities | Native canonical graph reconstruction compares every state and row; oracle uses independent occurrence counters | Prove that the constructor's domain and exclusions cover every geometric occurrence required by the application |
| Nonnegative matrix entries | Entries are occurrence counts | Kernel-checked transport from the serialized graph to `T : I → I → ℝ` |
| Strictly positive physical masses | Every retained interval has exact positive sign; typed physical-strip argument is written in PR #497 | Real algebraic embedding, interval interpretation and strict strip proof in Lean |
| Correct transpose and quotient orientation | Native column accumulation, independent forward/inverse multiplicity equality, and free-orbit checks | Kernel-checked orbit-count correspondence; use weighted `H` for mixed orbit sizes |
| Nonnegative deficits | Native exact signs; oracle omitted positive intervals and full partition budget | Prove the literal interval partition identity and its transport to `Tᵀh ≤ θh` |
| Nonnegative finite overlap vector | Written compact attractor/product-Haar construction | Actual measurable compact overlap sets and finite measure in the intended geometry |
| Supersolution `Tv ≥ θv` | Written PR #497 relation is the stronger equality `Tv=θv` | Formalize complete occurrence decomposition and the compact Haar scaling; Euclidean scaling alone is insufficient in the nonunit case |
| Complete source SCC inventory | Native canonical Tarjan partition and independent Python Kosaraju/condensation | Bind the concrete graph to Lean's relation; the generic source-ancestor theorem is separate |
| A losing vertex in every source SCC | Twelve selected source witnesses, each with certified positive deficit | Kernel-check each concrete component/witness against the decoded graph and masses |
| Every relevant vertex is represented | Complete closure from the declared three roots per source; each source SCC contains a declared root | Prove that the application requires precisely this root/domain inventory, or enlarge it with a new complete construction |
| Zero propagation and global nullity | Generic finite-sum, saturation, reachability and SCC theorem in Lean | Apply that theorem only after the concrete hypotheses above have been transported |
| Uniform strict-PIP consequence | No uniform conclusion supplied by this finite packet | Uniform conservative-source exclusion and a source-valid bridge to the actual one-step `Sync` newborn target |

The compact Haar normalization matters. The written source construction
uses the stable Euclidean factor together with the compact nonunit
factor; multiplication by the substitution scales their product measure
by `β⁻¹`, and two steps by `β⁻²`. In particular, the physical expansion
`θ=β²` must be the same scalar in the overlap supersolution and the
transpose budget. Matching names or matching approximate numerical values
does not establish this refinement.

The packet source graph is rooted by construction. In a finite rooted
closure every source SCC must meet the declared roots: any path from a
root to that SCC cannot enter it from a different component. The native
check uses the least vertex of the sorted component to test intersection
with indices `0,1,2`; the oracle checks that intersection directly. The
**losing witness need not itself be a root**. For source 10 it is vertex
4; source-root intersection and positive-deficit membership are separate
facts.

The matrix theorem itself does not require designated roots. Its exact
coverage condition is that every target vertex be reachable, along
positive row-to-column edges, from a positive-deficit vertex. A losing
vertex in each finite source SCC supplies that condition. Root coverage
is necessary when claiming that the supplied finite universe includes
every overlap relevant to an external problem.

## 4. Twelve-source inventory

Each graph has one inverse source SCC. The rows below are pinned by the
historical `summary.txt` and checked against both fresh exports.

| Source | Images `σ(0)/σ(1)/σ(2)` | States | Occurrences | Losing rows | Source SCC size | Losing vertex |
|---:|---|---:|---:|---:|---:|---:|
| 0 | `11/012/01` | 3,664 | 21,151 | 294 | 1 | 2 |
| 1 | `11/012/10` | 3,649 | 21,164 | 245 | 391 | 1 |
| 2 | `11/021/01` | 3,667 | 21,103 | 315 | 123 | 2 |
| 3 | `11/021/10` | 3,667 | 21,033 | 338 | 622 | 1 |
| 4 | `11/102/01` | 3,653 | 21,186 | 251 | 56 | 0 |
| 5 | `11/102/10` | 3,667 | 21,168 | 313 | 1 | 2 |
| 6 | `11/120/01` | 3,693 | 21,144 | 327 | 622 | 0 |
| 7 | `11/120/10` | 3,674 | 21,203 | 257 | 123 | 0 |
| 8 | `11/201/01` | 3,643 | 20,976 | 334 | 119 | 0 |
| 9 | `11/201/10` | 3,643 | 21,054 | 286 | 56 | 1 |
| 10 | `11/210/01` | 3,646 | 21,095 | 270 | 391 | 4 |
| 11 | `11/210/10` | 3,649 | 21,118 | 278 | 143 | 2 |
| **Total** | **12 sources** | **43,915** | **253,395** | **3,508** | **2,648** | **12 witnesses** |

The mass argument consumes graph authentication and SCC infrastructure
from its predecessors. It does not consume their modular determinant
obstruction or fitted positive-weight certificate as a premise. Importing
the module that also contains those routines does not make their
certificate outputs assumptions of the mass proof.

## 5. Independently reproducible replay and refusal controls

At a chosen exact revision of the new kernel, create a separate checkout
of the pinned source. Keep the new checker and its manifest in the kernel
checkout, and execute the old native/oracle producers in the pinned source
checkout. The dedicated workflow performs the same separation.

```bash
git worktree add --detach ../physical-mass-source 51dd090a6aefeb92210410a3f7e20d51926d7e86
source_dir=$(cd ../physical-mass-source && pwd)
replay_dir=$(mktemp -d)

(cd "$source_dir/kernel" && pixi run --locked mojo run -I . tests/test_c4_overlap_physical_mass.mojo) \
  > "$replay_dir/native-controls.log"
(cd "$source_dir/kernel" && pixi run --locked mojo run -I . c4_overlap_physical_mass.mojo) \
  > "$replay_dir/physical-native.txt"
python3 "$source_dir/oracles/python/c4_overlap_physical_mass.py" \
  > "$replay_dir/physical-oracle.txt"

python3 tools/check_physical_mass_refinement.py \
  --source "$source_dir" \
  --native "$replay_dir/physical-native.txt" \
  --oracle "$replay_dir/physical-oracle.txt" \
  --output "$replay_dir/source-receipt.json" \
  --self-test
```

Use the source's `kernel/pixi.lock`; the hosted workflow pins Pixi
`0.81.0`. A shallow clone may need to fetch the exact source commit before
adding the worktree. The two exports must be independently produced; the
checker validates their bytes and does not attest process execution from
filenames. The surrounding workflow therefore runs both commands, checks
their exit status and retains their logs, exports and receipt.

`--self-test` augments normal validation; it never substitutes fixtures for
the real supplied packet. Its eight deterministic refusal controls are:

- omit a row;
- duplicate a row while preserving the record count;
- omit a source-witness record;
- change a source's losing witness to a different declared vertex;
- change one mass byte while preserving byte count and framing;
- replace a positive mass coefficient row with the zero triple;
- disagree between native and oracle packet bytes;
- mutate tracked source content while retaining the pinned blob identity.

The checker also rejects a different source commit/tree/parent, changed
tracked content or executable modes, an inconsistent source index,
changed source summaries, altered ordering, noncanonical serialization,
and stale or unbound packet digests. Refusal produces a failed run and,
when the requested output is safe to write, a `status: refused` receipt.
It never treats a missing receipt or an exhausted producer budget as a
mathematical verdict. The original source regression includes the
mathematical controls for a conservative source with a losing sink,
incomplete root reachability and deletion of one repeated occurrence.
Quint independently models the broader adversarial inventory in the
kernel note.

The receipt hashes the same manifest snapshot that was parsed, records
the checker SHA-256 and the kernel checkout's commit/tree/dirty status,
and refuses if either the checker or manifest changes during validation.
The separately checked nested pinned-source checkout is excluded from
the kernel dirty-status calculation when it is inside the kernel worktree.

The local source-byte, oracle-packet and all eight provenance-control
checks passed; their receipt is
[`source-oracle-local.json`](../evidence/physical-mass-kernel-2026-11-08/source-oracle-local.json).
Local native startup was **blocked by automatic approval review** because
of possible telemetry containing local user metadata. It was not retried
through a workaround and is not counted as native acceptance. The clean
hosted source job supplies the fresh native/oracle replay receipt. The
historical successful run remains a distinct observation.

For a new exact revision, acceptance must separately retain the compiled
Lean axiom audit, the exact Quint execution inventory, and the source job
with this binding receipt. The source job's success proves neither that
the Lean job ran nor that the geometric obligations in section 3 were
discharged. Merge-head acceptance similarly requires receipts for the
actual merge revision rather than inference from a predecessor's green
badge.

## 6. Next condition toward the uniform strict-PIP target

The reusable theorem makes a practical next question precise: **can an
inverse source SCC of a complete, realized strict-PIP overlap carrier be
conservative?** Here conservative means every member has zero physical
deficit. An authentic positive omitted interval at any member destroys
that possibility for the mass argument and, through the source-SCC
theorem, forces the whole reachable overlap vector to vanish.

For extending the computation, the next certificate interface should
retain the complete occurrence graph, the root inventory, orbit sizes,
and a literal omitted-interval witness for each source SCC. A conservative
source must be reported as an unresolved obstruction with its actual
ordered occurrence data. It must not be removed from the carrier, replaced
by a losing sink, or converted into a loss by suppressing an edge. A
uniform theorem would have to rule out such conservative components from
strict child closure and the actual source geometry. Finiteness and
nonnegative-matrix algebra alone cannot do this: the one-vertex matrix
`T=[θ]` with positive mass is conservative and admits a nonzero vector
satisfying equality.

*Clarification, 2026-11-09.* "a complete, realized strict-PIP overlap carrier" admits the two domains named in the dated clarification of the kernel note; the twelve-source computation bears on the three-root carrier of a source only ([quantifier audit](quantifier-transfer-audit-2026-11-09.md), §12).

The reduction is independent of state count, but it supplies **no uniform
bound on carrier size, witness depth or a search budget**. A source SCC
count bounded by the number of declared roots also does not bound its
size or produce a bound uniform over all relevant substitutions. The
existing operational state and exact-sign limits are fail-closed
implementation limits, not uniform mathematical estimates.

Finally, [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
asks for an actual **one-step interior zero-return newborn** with the
appropriate `Sync_+` or `Sync_-` neighbor in an ordered strict-PIP system.
Null measure is not emptiness and does not identify an ordered cut. A
geometric reduction must show that every putative strict system yields
the represented overlap vector with the required positive component,
and then transport the contradiction to that actual newborn statement.
The written compact-measure arguments are useful inputs to this next
step; they are not a kernel-checked transport or a universal newborn
theorem. General conservative-class exclusion, the uniform geometric
bridge, C4 and PSC remain open.

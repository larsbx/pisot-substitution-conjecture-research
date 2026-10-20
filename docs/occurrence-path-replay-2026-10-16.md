# Exact occurrence path certificates (2026-10-16)

**Scope:** finite existential witnesses in the specified word-pair or swap-patch
model. No claim-ledger status is promoted. General PSC, G1, #84, #138 and #139
remain open. The preceding [stop/go gate](occurrence-path-replay-gate-2026-10-16.md)
records the primary-source boundaries. This implements the finite witness part
of the [October 15 audit](boxwalk-reachability-realizability-audit-2026-10-15.md),
not its separate universal coverage/closure obligations.

## Canonical interface

`kernel/psc/occurrence_path.mojo` exposes typed in-memory certificates. All
indices are zero-based; top/bottom orientation is retained, never normalized.
A complete witness consists of the **ordered substitution images, seed, and
ordered edge list**. An edge list without those inputs is not a certificate.
There is no permissive JSON parser or external graph-trust boundary in this
version. The executable control is `kernel/occurrence_path_replay.mojo`.

| API | Accepted conclusion |
| --- | --- |
| `matched_target(pair,q)` | For a validated balanced pair, `0 <= q < N`, equal next letters, and equal prefix Parikh vectors |
| `replay_word_path(images,seed,edges,max_steps,max_word)` | Each edge selects an actual irreducible balanced child of the preceding ordered pair's inflation |
| `certify_word_path(...)` | The replay finishes at a single equal-letter balanced child |
| `replay_overlap_path(sigma,seed,edges,max_steps)` | Each edge is an interior child occurrence of the preceding computed overlap, anchored in the specified swap patch |
| `certify_overlap_path(...)` | The replay finishes at equal tile types with exactly zero displacement |
| `search_overlap_path(sigma,seed,max_depth,max_states,max_choices)` | Deterministic bounded witness search; success is independently replayed within the module |

The word API accepts nonerasing ternary substitutions without a Pisot premise;
its conclusion is finite word combinatorics. Its supplied balanced root is not
asserted to occur in a substitution language. The overlap API rebuilds the
canonical exact PIP tables from `sigma`, inheriting the existing audited
image-length-at-most-six input domain. It does not widen the cubic screen.
Larger family parameters require a separately justified constructor/extension.
All exact-field arithmetic/sign refusals propagate as errors.

### Relationship to existing target packets

`psc.target_packets` already supplies occurrence-sensitive BPA graphs, addresses,
`verify_packet`, `replay_edge`, `replay_path`, and shortest successful paths.
Those are retained. `build_packets` requires a complete BPA automaton and
validates its complete seed closure. The missing interface filled here is a
**standalone finite witness checker without a completed BPA graph**, together
with labelled geometric overlap replay and bounded overlap witness search.
Both word layers reuse canonical balanced cuts; no second packet graph or SCC
implementation is introduced.

The integration regression in `test_target_packets.mojo` exports every success
in its existing unsynchronized fixture as an ordered `WordEdge` from the actual
parent, then independently certifies the child and tests the global matched cut.
Packet success has a stricter interior-cut condition (`q>0`), whereas the new
local predicate permits `q=0`. The packet engine's optional `synchronize=True`
mode is an eventual endpoint-synchronization predicate, not an immediate
matched-letter certificate, and is deliberately not treated as interchangeable.

### Word paths and paired read heads

A `WordEdge` contains the full ordered source pair, the top and bottom
`ImageHead(parent_index,child_index)`, an exclusive aligned end cut, and the
full claimed child pair. Each head is a **proper child occurrence** in an
image, not a terminal sentinel. Prefix image lengths determine the two start
cuts, which must agree, even when the parent indices differ. Full inflation
is budgeted before allocation. The canonical `coincidence_boundaries` checks
that the chosen start and end are consecutive balanced cuts. The actual slices
must equal the claimed child; the next edge's source must equal that child.

Induction gives a nested chain of actual balanced-child occurrences. At an
accepted singleton endpoint the local cut has zero prefix imbalance and equal
next letters. Substituting a balanced prefix preserves balance, so composing
these child selections also yields an actual matched target in an iterate of
the original root pair. There is no transfer from a vector-only walk.

`matched_target` separately checks the October 15 predicate on any specified
balanced pair. Terminal cuts return false. Unequal next letters return false,
even at an ordinary zero return. Invalid alphabet or unbalanced inputs raise.

### Overlap paths and address lifting

`SwapOccurrence(a,b,i,j)` with `0 <= a < b < 3` identifies tiles `i,j` in the
actual superposition `ab|ba`, both patches starting at zero. The checker derives
the initial tile types and displacement and verifies interior intersection.
Each `OccurrenceEdge` records source, ordered child indices and claimed target.
The entire index sequence, including the root indices, is the paired occurrence
address; it need not be duplicated as an absolute exponentially long word.

For `s = bottom_start - top_start`, replay computes exactly

```
s_child = beta*s + prefix(bottom,j) - prefix(top,i).
```

It checks index ranges, child types, target displacement and interior overlap.
The next source must equal the **computed full target**, not merely its shift.
The affine arithmetic is shared with the existing overlap child generator;
that generator retains its precomputed scaled shift and prefix loop layout.

Induction on the chosen indices constructs actual descendants of the anchored
patch tiles. An accepted endpoint has equal starts **and equal tile types**.
For this irreducible ternary entrypoint, a geometric coincidence also gives
an actual aligned matched-letter cut in the inflated full swap pair. Its two
absolute starts are Perron lengths of integer prefix-Parikh vectors. The
Perron length map on `Q^3` is injective: its rational kernel is M-invariant
since `ell M = beta ell`; a nonzero proper rational invariant subspace would
factor the irreducible characteristic cubic. Exact zero displacement therefore
implies equal prefix-Parikh vectors, hence equal prefix word lengths and one
aligned cut q. The selected tiles supply the equal next letters, so q is
nonterminal. This argument uses the entrypoint's screened irreducibility; it
is not asserted for arbitrary reducible geometric models.

The search interns full `(top,bottom,shift)` types and keeps predecessor indices.
This quotient has an explicit lifting argument: two occurrences with these
same three data differ only by common translation, and every fixed ordered
child choice has the same translated geometry. Thus keeping one ancestry per
full type preserves existential continuation. Forgetting tile types or ordered
word context has no such guarantee. Replay itself does not rely on search
completeness or on any caller-supplied graph.

## Budget and quantifier semantics

| Search status | Meaning |
| --- | --- |
| `CERTIFIED_LIFTABLE_TARGET_PATH` (0) | A particular target-reaching path was replayed; no completeness claim is needed |
| `BUDGET_EXHAUSTED` (1) | State or child-choice budget stopped search; no accepted certificate is returned |
| `DEPTH_COMPLETE_NO_CLOSURE` (2) | The explored finite prefix reached the requested depth; no absence or closure conclusion |
| `NO_MATCHED_TARGET_WITHIN_BUDGET` (3) | Queue emptied without an accepted target; deliberately no universal/tiling conclusion exposed |

Invalid limits and arithmetic failures raise. A replay exceeding its step or
word-size budget raises rather than truncating and accepting a prefix. Search
counts every ordered child choice, including non-overlaps and duplicate types.
It may refuse before processing an already enqueued target when a resource cap
is reached; that conservative false negative never becomes a certificate.
Successful paths can be replayed independently of the search with larger or
smaller sufficient budgets. No output has a Boolean `all_productive` field.

This is **there exists a path from this occurrence**. It does not say every walk
hits, every overlap is productive, or any nonproductive child-closed component
is excluded. Those need complete child enumeration, root/state coverage and the
appropriate global dictionary. Existing complete-graph SCC queries remain
separate; neither a sampled plateau nor these statuses may feed them as a
closure proof.

## Controls and reproducibility

Run from `kernel/` with the pinned toolchain:

```sh
mojo run -I . tests/test_occurrence_path.mojo
mojo run -I . occurrence_path_replay.mojo
```

The suite automatically discovers the new test and collects its contract
receipt. No new mathematical claim receipt is invented.

1. **Terminal zero:** `01|10` (the user's `12|21`) has no matched cut, including
   its terminal zero. Equal next letters at nonzero imbalance are also rejected.
2. **Projected-edge splice:** under the identity substitution let
   `A=01|10`, `C=01|01`, `D=0|0`. The actual child edges `A -> A` and
   `C -> D` each replay separately. Total-imbalance projection sends all three
   to zero, so the projected edges compose, but the anchored composition fails:
   after the first edge the word context is A, not C. Every iterate of A is A,
   with no matched target. This synthetic non-PIP fixture isolates projection
   unsoundness; it is not a Pisot counterexample. A nonzero-prefix variant uses
   `A=012|210`, `B=021|201`: both have residual `e_0-e_2` at cut 1, but only
   B returns to zero at cut 2 with a next `1/1` match. The projected walk
   splices A's cut-0-to-1 edge with B's cut-1-to-2 edge. A has no matched target
   at any cut and is fixed by the identity substitution. Both actual local
   balanced-child selections replay, but a certificate switching from A to B
   is refused. A second overlap fixture
   attempts to splice `(c,a,0)` into `(a,a,0)` as the next source and is rejected.
3. **Actual non-unit PIP control:** for `a->aaabcc,b->ab,c->a`, the anchored
   seed `swap(0,1), heads(0,1)` gives `S=(a,a,ell_b)`. Choice `(1,0)` loops
   at S. Choice `(4,2)` gives `H=(c,a,0)` and choice `(0,0)` at H gives
   `(a,a,0)`. Tests replay five loops then the exit; loop-only and half-target
   paths fail certification. The bounded search also finds a depth-two witness.
   Independent full-word inflation confirms its target at cut 20 in the
   length-30 pair `sigma^2(ab)|sigma^2(ba)`.
4. **Refusals:** wrong source, tampered target, invalid or terminal image head,
   disjoint child choice, skipped irreducible cuts, unbalanced/invalid input,
   and exhausted state/choice/depth/word/step budgets. A valid two-step word
   branch and unequal parent read heads guard against over-restrictive fixes.
5. **Canonical agreement:** labelled interior children of S, H and the target
   agree in order and multiplicity with `overlap_children`; existing graph
   size/depth regressions protect the shared affine arithmetic.

PR #271, merged during this implementation, corrects the family's status:
the entire family is already PDS by the imported mirror-Barge route. See the
October 16 correction in `nakaishi-2024-first-entry-audit-2026-10-13.md` and
the existing `BargeClassFlowPDS` / `BargeClassSymbolicPDS` claims. The local
loop/exit witness remains valid and useful as a certificate control.
Running this fixed `(3,2)` control neither reproves its whole parameter range
nor proves productivity of every overlap of even this one specimen.

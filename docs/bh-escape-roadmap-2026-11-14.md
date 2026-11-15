# BH escape roadmap and the parallel A1′ target

**Status:** planning and source reconciliation; universal BH and A1′ remain open.

**Priority: prove that every required BH source has a successful escape.**
The most concrete next theorem is uniform entry into the minus Class-A
zero-return predecessor set, [issue #452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452).
Work on the residual aligned A1′ pair should proceed in parallel. The
existing occurrence machinery already composes a supplied valid finite path;
the principal missing argument forces such a path to exist.

This is a planning and source-reconciliation note dated **November 14, 2026**.
The inspected mainline is `c9358c2d46d7b306853609e2c5a090328aff92c3`.
The proof developments below are on open draft branches. Pinned links identify
their producing revisions; this documentation imports none of their source
files into main and changes no governed claim status. The current universal
program is **ternary primitive irreducible Pisot (PIP), including nonunits**.
An all-alphabet conclusion requires a further argument.

## 1. Completed family work and newer conditional progress

For `sigma_k=(1,0 1^k 2,001)`, the family argument establishes termination
with coincidence from `01/10` for every `k>=2`. The literal primitive,
irreducible Pisot arithmetic is proved for `k>=1`; the full-factor
correspondence assembles the published spectral criterion's inputs for
`k>=2`. The [family spectral account](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/6bf0b9704501eb763cbb4323c3fd1f939d6f11c8/docs/c4-family-spectral-closure-2026-11-14.md)
applies the external Barge–Štimac–Williams implication. Its analytic and
topological spectral conclusion is not an end-to-end Lean theorem.

The following GitHub snapshot was checked on November 14 at **15:43 EST
(20:43 UTC)**. Later runs must be inspected at their own producing revisions.

| Development | Producing source | Observed acceptance on November 14 |
| --- | --- | --- |
| [#573 family spectral inputs](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/573), stacked on #572 | `6bf0b9704501eb763cbb4323c3fd1f939d6f11c8` | [Source-isolated family gate](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43630544741), [full isolated Lean library](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43630544688), and [original archived-payload import](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43630544838) passed. [Broad research checks](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43630544784) were still running. |
| [#574 BH finite reachability and A1′ tail witnesses](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/574), stacked on #573 | `fd23a6681db651762e49c9c959a9aad682fb007f` | The [dedicated source-isolated workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43638030436) passed. Its own [full isolated library workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43638030298) was still running. The parent's library receipt is not a receipt for this source. |

The newer [BHFiniteCarrier endpoint](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd23a6681db651762e49c9c959a9aad682fb007f/proof/PscVerif/PscVerif/BHFiniteCarrier.lean)
already supplies the conditional passage from a finite actual packet cover
to finite balanced-pair reachability. Its hypotheses require positive lengths
with exact substitution scaling, an actual irreducible balanced seed, seed
coverage, closure under **every** literal `InteriorStep`, and a finite path
to **zero integral displacement for every packet in that cover**. It derives
all-generation coverage and finite actual `ChildNC` reachability, including
the word-length bound needed for the latter conclusion.

Thus rebuilding this conditional bridge is no longer the next task. The
remaining work is to supply its coverage and hitting premises where needed.
Neither this bridge nor the completed `sigma_k` family proves universal BH.

## 2. The next Class-A theorem: force entry into an explicit target

For arbitrary `k,t>=0`, put

\[
n=k+t+3,\qquad d=k+2t+5,\qquad A=n+d,
\]

with literal ordered words
`x -> x y^A x`, `c -> c y^n x`, `y -> x y^(n-1) c`.
The [one-step zero-return derivation](class-a-uniform-zero-return-2026-11-02.md)
classifies all oriented literal predecessors of zero integral offset by
nine affine integer segments, together with the FIRST/FIRST zero parents.
Every legal witnessing address gives strict overlap. Its total number of
distinct oriented parent states is

\[
18n+6d+7=24k+30t+91.
\]

Exactly nine have zero parent offset. This counts the complete **literal
predecessor classification**, not seed-reachable states. Some of its states
may lie outside a chosen seed graph. The nonzero count is `24k+30t+82`.

For the actual occurrence-indexed, strict, child-closed seed graph
`Gamma_(k,t)`, let `Z_(k,t)` be its zero-offset vertices and let `H_(k,t)`
be its intersection with the **nonzero** predecessor classification. For
nonzero `v` in that graph, the existing reduction gives

\[
v\rightsquigarrow Z_{k,t}\quad\Longleftrightarrow\quad
v\rightsquigarrow H_{k,t}.
\]

The forward direction takes the predecessor of the first zero hit. The
reverse direction appends its classified literal zero-return edge; complete
child closure keeps that edge in the graph. An arbitrary curated label set
does not satisfy this premise merely by containing the endpoint names.

The proposed theorem is therefore:

> For every `k,t>=0`, each **nonzero cyclic, seed-reachable strict-zipper
> state required by the BH reduction** has a finite composable path of
> actual ordered child occurrences into `H_(k,t)`.

Zero-offset sources already satisfy BH at depth zero. A proof of this
statement closes this minus-Class-A specialization; it does not cover
arbitrary ternary substitutions or automatically discharge the nonunit
realization dictionary. The target set and final edge are known. Universal
entry into that set remains open.

## 3. Two useful forms of the missing escape argument

**A symbolic cover and a selected escape rule.** Establish a domain covering
every required source for arbitrary declared parameters. From each state
outside the target, select a genuine finite child path that either reaches
the target or decreases a well-founded rank. The rank may depend on `k,t`,
both letters, the full offset and endpoint phase. One decreasing transition
may consist of several verified child edges.

Coverage and progress are separate obligations. A proposed carrier needs
complete actual-child closure or another proved coverage argument. Escape
needs one successful choice from each covered state; it does not require
every outgoing edge to decrease. The [22-specimen certificate](completion-ledger-2026-11-02.md)
and shortest-distance witnesses can reject candidate rules and reveal cases.
Their finite parameter range does not prove the unbounded quantifiers.

**A contradiction from a closed bad component.** Work in the actual complete
finite graph and take a target-free terminal strongly connected component
arising from a hypothetical failed hit. Prove that one of its vertices has
an actual escape to zero. Closure under every child contradicts that escape.
The reduction must establish the relevant component's existence, reachability
and strict-zipper hypotheses; a cycle in a selected or incomplete graph is
insufficient. Productive graphs can contain nonzero cycles whose successful
exit is never chosen, as the [existing controls](direct-attack-frontier-2026-10-23.md#4-retired-routes-do-not-spend-cycles-here)
record.

Neither a symbolic escape rule nor the required universal component
contradiction is supplied by this roadmap.

## 4. Reuse the address and path machinery

| Existing interface | What it supplies |
| --- | --- |
| [`OccurrenceAddress.locateSubst`](../proof/PscVerif/PscVerif/OccurrenceAddress.lean) | Decomposes an actual substituted-word position into its parent and within-image occurrence. |
| [`PrefixAddress.complete_address`](../proof/PscVerif/PscVerif/PrefixAddress.lean) | Complete unique addressing under its stated fixed-prefix and cofinality hypotheses. |
| [`OccurrenceTransport.packet_path_lift`](../proof/PscVerif/PscVerif/OccurrenceTransport.lean) | Lifts supplied finite `InteriorStep` reachability from an actual marked source to a coherent chosen `AddressedPath`. |
| `AddressedPath.child_path` in the same module | Produces the actual balanced-child path after constructing the marks. |

`AddressedPath.cons` starts its tail at the exact marked target of the
previous step. Equal projected labels do not justify splicing unrelated
literal contexts. These results solve finite path lifting under their
hypotheses; they do not produce a successful path from every source. See the
[transport contract](c4-occurrence-transport-2026-11-10.md).

A useful narrower adapter would retain **originally supplied** proper
marked occurrences in `sigma^m(i)` and `sigma^m(j)`. If their prefix Parikh
vectors are `p,q` and the historical BH offset is `w`, the target equation is

\[
M^m w=p-q,\qquad w_{r+1}=Mw_r+q_r-p_r.
\]

The Lean packet convention is top minus bottom, so `delta=-w`. BH requires
zero integral displacement; terminal letters may differ. `Packet.Diagonal`
also requires equal letters and is a stronger target. Zero physical length
alone is not integral zero; #574 retains an explicit `021/120` control.

The [M-adic carry reduction](p1b-madic-carry-reduction-2026-10-01.md) and
[`OccurrenceInverse`](../proof/PscVerif/PscVerif/OccurrenceInverse.lean)
supply the address/carry background. Decode the original proper occurrences
through their ancestors, preserve their prefix recurrence, and derive strict
intermediate overlap from the common positive terminal interval. The formal
adapter must prove that this original ordered transcript is retained;
`packet_path_lift` instead chooses compatible existential digits.

Keep the production terminal policy separate: the literal `Child` relation
may inflate an already coincident block, while production graphs terminalize
typed coincidence. A depth-`m` nonterminalized transcript can be stopped at
its first zero/diagonal hit for BH, at depth at most `m`; retaining all `m`
steps is not automatically a refinement of that terminalized graph.

## 5. Take a finite maximum only after proving the required hits

Uniformity here means a theorem of the form
`forall sigma, forall required v, exists m, exists actual hitting path`.
The depth may depend on both the substitution and the source. Class-A
[run-index bounds](p1b-class-a-run-index-2026-10-21.md) already rule out a
parameter-independent hitting depth across Class A, via an explicit
plus-sign subfamily. That control is separate from the minus-Class-A target
in §2.

For a fixed substitution, once every packet in the **complete relevant
seed-overlap cover** has a hit, take the maximum of finitely many chosen
depths, `D_sigma`. The [overlap-depth argument](bpa-termination-by-overlap-depth-2026-10-02.md)
then bounds late irreducible factors in physical length by
`2 beta^D_sigma max_a ell(a)`. Positive minimum letter length gives a symbolic
bound, and finitely many earlier generations are included separately.

The graph's transient sources and all actual children must be accounted for.
A maximum over recurrent or cyclic states alone cannot be substituted for
the all-seed bound; the overlap-depth note's §7 explicitly distinguishes
these quantities. The narrowed cyclic BH theorem must be connected through
the existing obstruction reduction to whatever complete hitting premise its
consumer requires. #574's conditional endpoint requires a hit for **every**
packet in its finite cover. Graph finiteness supplies the finite maximum
only after the relevant existence and coverage obligations are proved.

## 6. Parallel A1′ work and the alternate C4 route

For [A1′ #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138),
retain the prescribed residual fixed-hub pair
`u=sigma^infinity(x)`, `v=sigma^infinity(c)`. The proximality target is

\[
\forall N\;\exists r:\quad u[r:r+N]=v[r:r+N].
\]

Both blocks start at the **same position**. The [proximality note](p1a-a1-proximality-2026-10-19.md)
records the imported Barge–Zamboni implication for primitive irreducible
Pisot fixed points, without an additional unimodularity premise. What remains
is to prove proximality from the residual hub assumptions. Growing common
blocks at different positions, or drifting under substitution, do not do so.

The newer [A1′ tail development](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd23a6681db651762e49c9c959a9aad682fb007f/docs/p1a-minimal-z3-tail-stop-go-2026-11-14.md)
settles specified positive four-run/three-run residues using literal witnesses:
the two `Z=3` layers and three `Z=4` word patterns. The common-depth Lean
witnesses are scoped to those words; the overall run-shape reduction also
uses earlier manuscript lemmas. This is further family progress, not
universal residual-hub proximality or A1′ closure.

Universal BH and one-sided A1′ feed the existing
[#84 assembly](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/84).
The alternative [C4 target #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
still needs uniform exclusion on complete strict systems and a separate
finite-carrier extraction argument where the termination consumer requires it.
The [universal closure review](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/6bf0b9704501eb763cbb4323c3fd1f939d6f11c8/docs/psc-universal-closure-review-2026-11-14.md)
keeps these premises explicit. Its productive but infinite-carrier binary
control is non-Pisot and establishes no counterexample inside PIP.

## 7. Acceptance of the next mathematical increment

The next deliverable should prove uniform occurrence-compatible entry into
the Class-A predecessor target, with an explicit extension boundary. Require:

1. A symbolic proof for all declared parameters and coverage of every
   required source, with transient/complete-cover obligations discharged
   wherever the downstream theorem needs them.
2. Actual ordered occurrence witnesses, strict overlap, correct orientation
   and a zero **integral** endpoint. Preserve RUN/LAST distinctions and the
   production stopping rule.
3. Lean endpoint and axiom auditing at the producing source; canonical Mojo
   and independent oracle evidence for any executable certificate. A finite
   sample or a successful workflow does not replace the symbolic argument.
4. Retained controls for productive cycles, missing child coverage, equal
   labels with different contexts, physical versus integral zero, and scoped
   family results mistaken for universal conclusions.
5. Separate records for source proof, replay, hosted acceptance, integration
   and independent review. Keep the full nonunit representation and the
   extension to arbitrary ternary PIP substitutions explicit.

Follow [AGENTS.md](../AGENTS.md#review-gate) before new theorem-facing machinery.
Independent human review remains final validation debt; it does not block
continued research using correctly scoped accepted dependencies. Universal
BH, A1′, C4, G1 and PSC remain open until their own missing premises are proved.

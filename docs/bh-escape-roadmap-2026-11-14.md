# BH escape roadmap and the parallel A1′ target

**Status:** planning and source reconciliation; universal BH and A1′ remain open.

## November 27: upper plus Lean assembly and higher-determinant bands

This section supersedes the active-work paragraph of the November 21
snapshot below, which is retained as history.

**Upper plus Class A is formalized.** #655 merged the
[central completion](class-a-plus-upper-central-completion-2026-11-23.md).
`Psc.ClassAPlusUpperCentralCompletion.exists_root_all_source_completion`
proves, for every `n>=7`, `n+5<=d<=2n+11`, a bracketed cubic root,
positive literal eigenlengths and a finite original-occurrence path from
every strict integral typed source to typed `y/y` zero. Its only outer
premises are the three parameter inequalities. The merge record states
that the accepted head passed the hosted Lean build and axiom audit. The 70
small members `n<=6` keep their complete swap-seed certificate scope; their
Mojo and pytest checks run in main's hosted research checks, which passed
at `ffd3f9b` (run 45442126274). Independent human review remains pending.

**Higher-determinant family (#656).** For `σ_{k,r}=(1,01^k2,0^r1)`:

| Scope | Result | Verification boundary |
| --- | --- | --- |
| `r>=12`, `k=r+1,r+2` | [Written all-source exit](bh-near-diagonal-exit-2026-11-24.md) to `1/1` at full integral displacement zero | Lean checks the quadratic descent and its literal realization in the central window; the third-level mark entry is written only |
| `r>=12`, `k=r` | [Sufficient region](bh-diagonal-run-reduction-2026-11-24.md): run window with `max(\|y\|,\|z\|)<=⌊(r-2)/3⌋` | The uniform exit from the remaining run-window packets is open |
| Both bands and `k=r` | [Three-window entry](bh-third-level-windows-2026-11-24.md) on the original occurrence tracks | Written construction with exact literal replay |
| 24 members | [Bounded-factor bridge](bh-higher-determinant-carrier-2026-11-24.md): finite actual factor bound implies literal zero hits | Lean implications checked locally; a proof uniform in the remaining parameters is open |

**Active BH work.** Bind the minus-Class-A paths to Lean (#442). Give the
`k=r` band a uniform exit and formalize the third-level mark entry. Then
extend source coverage and actual zero-hit paths to the remaining BH
domains in the full nonunit representation. No residual A1′ (#138)
result has merged since November 21. #624 adds a Lean
[correspondence](barge-diamond-correspondence-2026-11-19.md) between the
Barge–Diamond word conclusion and vertex coincidence. It is an interface
only; Barge–Diamond Theorem 1's existence proof remains external.

## November 21: current family boundary and universal work

At main
[`e7e6e330b80b560be70c2a5346e217f415fe4711`](https://github.com/larsbx/pisot-substitution-conjecture-research/commit/e7e6e330b80b560be70c2a5346e217f415fe4711),
the [current research roadmap](research-roadmap-2026-09-21.md#2026-11-21-current-priorities-family-spectral-endpoint-and-universal-coincidence)
integrates the [research review](psc-sigma-k-research-review-2026-11-20.md)
and the subsequent #639–#641 proof developments. The following dated
snapshots preserve their original scopes and acceptance observations; their
old draft status and already-completed implementation targets are historical.

The `σₖ` arithmetic and full-factor coincidence theorem for every `k>=2`
were integrated through #574; #572 and #573 are closed predecessors. The
[literal family hull](c4-family-tiling-2026-11-21.md) now supplies the geometric
substitution, aperiodicity, finite local complexity and continuous translation
action for `k>=1`, and dense periodic-swap coincidence for `k>=2`.
The [legal-patch transfer](c4-family-legal-coincidence-2026-11-21.md) supplies
dense eventual coincidence on the open overlap of legal patches sharing a
tile, and the periodic-partner closed-origin argument. The conditional
`periodic_fibre_common_tiles` endpoint gives one nonempty factor fibre with
pairwise common tiles; it still requires injective inflation, semiconjugacy,
finite fibres, and same-fibre closed-origin witnesses. Instantiate these for
the actual maximal equicontinuous factor, then prove the measured spectral
implication. The published Barge–Štimac–Williams criterion already gives
the paper-level family conclusion. Universal BH and C4 are not prerequisites
for completing this family formalization.

The active BH work remains the original-occurrence Lean assembly of the
written upper plus-Class-A paths and extension to uncovered source domains.
Retain the 70 small upper plus certificates at complete swap-seed scope and
their separately recorded acceptance status. For residual A1′, prove one-sided
coincidence for the prescribed fixed-hub pair; neither the family endpoint
nor the new legal-patch theorem supplies that universal assertion. The broader
C4 rank-two residue is `K₂,₂` with non-injective endpoint maps and incidence
nilpotent modulo two under the named geometric inputs. The roadmap separates
that written reduction, the new finite parity/graph/marker Lean results, and
the remaining geometric and witness-existence obligations.

The literature assessment found **no new external result in its checked
14–20 November window that closes these gaps**. Creutz–Pavlov's revised
preprint is a material correction, but its complexity hypothesis fails for
the literal σₖ coding. Published address-automata constructions can support
exact certificates; they do not force a productive path. The research
roadmap records publication status, hypothesis mismatches and specific next
deliverables without promoting a governed claim.

## Dated progress and acceptance history

**November 20, upper small members.** The 70 upper plus members
`n<=6,n+5<=d<=2n+11` now have
[complete swap-seed certificates](class-a-plus-upper-small-members-2026-11-20.md)
at seed scope, with canonical Mojo and independent replay; hosted acceptance
is pending. No member with `d>=2n+12` is PIP, since `chi(-1)=-(2n+12-d)`. At
their stated scopes, the existing parts and these certificates cover every PIP
plus-Class-A member. Lean binding of the written `n>=7` entry path remains the
open obligation on this family.

**November 19, acceptance reconciliation.** The mathematical entry target of
[#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452)
on `n+2<=d<=2n-1` is repository-proved and accepted for progression. The
[written proof](class-a-central-entry-2026-11-14.md), originating in #578,
was integrated through #577 at `59adf93f61ea5b7cecc78526b2099fa410c36bc0`
and merged as `75ebe17cea95fcce35df4be333d55aa77f3c8f8e`. At that exact
integrated head, the [central-entry replay](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43864432132),
[literal Lean interfaces](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43864432245)
and [PSC research checks, including the full Lean bank](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43864432043)
all succeeded. The [earlier Python integration failure](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43749586092)
at `210354853ba816a3d2d5639319cf1982fd4e4b06` remains historical evidence.
For `n>=6` the written theorem covers every strict integral source; the six
`n<6` members retain their complete S18 seed-graph scope. This acceptance
does not enlarge either quantifier. Full all-source geometric entry and
occurrence assembly in Lean, independent human review, and the remaining
BH domains are separate work. The earlier #452 priority below is historical.

**November 16, integration update.** Main now has the [upper plus all-source
entry theorem](class-a-plus-upper-all-source-entry-2026-11-16.md) for
`n>=7,n+5<=d<=2n+11`. It enters the
[central-source escape](class-a-plus-upper-central-recurrence-2026-11-15.md),
including all eight alternating-cycle exits. The smaller upper plus members and
the end-to-end Lean binding remain separate obligations. The [whole minus-chamber
registry record](ledger-index.md) now carries the November 19 acceptance
reconciliation above. The dated November 14 notes below retain their original scopes.

**November 14, plus-Class-A continuation.** The new
[constant-entry theorem](class-a-plus-constant-entry-2026-11-14.md) proves
typed coincidence from every strict integral overlap for
`n>=6,5<=d<=n+4` in the literal plus family
`x -> x y^(n+d) x`, `c -> c y^n x`, `y -> x y^(n+1) c`.
One-level density forces central entry, the signed nearest recurrence
has a constant tail, and three genuine RUN edges decrease its height.
The composed original prefixes satisfy `M^m w=P-Q`.
Five complete small S18 certificates, together with the inherited
low-gap and four Class-A seam-line results, complete the mathematical
canonical swap-seed cover `n>=0,1<=d<=n+4`. Only the new chamber has
the all-strict-source quantifier; inherited and finite cases retain
their seed scopes. The [evidence packet](../evidence/class-a-plus-constant-entry-2026-11-14/README.md)
records passing canonical, independent and cached formal checks;
fresh-source, full-library and exact-head hosted acceptance remain
pending for the plus source.

The next uniform Class-A target is the upper plus strip
`n+5<=d<=2n+11`. The [upper-target memo](class-a-plus-upper-entry-target-2026-11-14.md)
records a proposed parity-transformed recurrence, a three-RUN exit
when `JH>=5`, and the eight low-product cases still needing actual
occurrence exits. This proposal is unexecuted, unformalized and
unpromoted; all-source entry and small parameter members remain
separate obligations. Arbitrary-ternary BH, residual A1′ and the
all-alphabet extension remain open.

**Acceptance update, November 14 at 19:20 EST.** At `110e7e9e`,
[#579's whole-library source-isolated Lean run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43653036135)
has passed with `PSC_AUDIT_COMPLETE 6851 5041`.
Its [dedicated constant-entry workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43653036318)
was still queued. At `34ff471c`, #578's
[dedicated native and seven-endpoint gate](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43646986738)
and [whole-library audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43646986471)
have passed. These receipts belong to those exact sources; they do
not accept the new plus module. Earlier pending and failed records
below and in their original packets are retained as history.

**November 14, lower-chamber continuation.** The
[constant-entry theorem](class-a-minus-constant-entry-2026-11-14.md) proves
typed coincidence from every strict integral overlap for `d>=5,n>=d+1`,
including the former residual strip `d+1<=n<5d`. One-level word counts
force central entry; a positive-coefficient recurrence is eventually
constant; three actual RUN edges lower any nonzero constant height.
Every original prefix address is retained through `M^m w=P-Q`.
Together with the preceding upper chamber and the inherited `d<=4` and
`d=n,n+1` certificates, the source-scoped mathematical parameter cover
now spans the complete **minus-Class-A swap-seed domain**
`n>=1,1<=d<=2n-1`. The inherited certificates retain their seed scopes
and their original validation records. The new
[evidence packet](../evidence/class-a-minus-constant-entry-2026-11-14/README.md)
separates passing canonical and cached formal checks from the local
source-isolated gate blocked by upstream Mathlib HTTP 403, and from
pending exact-head hosted acceptance. The next mathematical extension
is to the unresolved plus-Class-A and other BH domains. Universal BH,
arbitrary-ternary A1′ and the all-alphabet extension remain open.

**November 14 continuation.** The [central-entry proof](class-a-central-entry-2026-11-14.md)
now supplies a written solution of the mathematical entry target of #452
for its stated minus-Class-A chamber `n+2<=d<=2n-1`. For `n>=6`, it
constructs typed coincidence from every strict integral source; complete
S18 certificates cover the six remaining parameters. Its original-address
and seed-domain arguments are part of the proof, and its
[evidence packet](../evidence/class-a-central-entry-2026-11-14/README.md)
separates exact replay, the formal recurrence subset, and pending hosted
acceptance. The earlier planning snapshot below is retained as history.
The next mathematical extension is beyond this chamber: establish the
corresponding actual-entry and cycle-exit mechanisms on the remaining BH
domains. The arbitrary-ternary A1′ problem remains separate; the stronger
construction supplies aligned coincidence within this chamber itself.

**Earlier planning snapshot, retained below.** The following priority
and Sections 1–3 describe the target before the three Class-A entry
developments above. Their universal BH and A1′ obligations remain
current; the minus-Class-A entry question is now mathematically
discharged at the stated scopes and acceptance boundaries.

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

## 2. Historical Class-A target: force entry into an explicit target

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

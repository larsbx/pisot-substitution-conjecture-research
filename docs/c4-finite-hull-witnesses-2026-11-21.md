# Finite automaton chains in the actual sigma-k hull

## Source decision before implementation

Proceed with the actual-hull interpretation of the finite signed automaton
merged in PR #647. The inspected baseline is main
`fbaa2ef1867e191f160cc3dbf9b8e26e10af45a7`, whose tree is
`a62791d03d8779370cb627937ea052d0c978b991`. The proposed endpoint is:
for every `k >= 2`, every pair of actual legal tilings over the full zero
solenoid history shares a labelled tile and admits the exact common-shift
windows required by the existing zero-fibre witness interface.

The following pre-code decision is retained as the record of the proposed
claim. The implemented theorem and its acceptance are described below.
The increment does not assert an invariant-measure spectral conclusion.

### Primary-source check

1. Barge, Stimac and Williams, *Pure discrete spectrum in substitution
   tiling spaces*, DCDS 33 (2013), 579--597,
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   proof of Theorem 3.1. The relevant established mechanism is transfer
   from shared legal tiles to dense eventual coincidence, followed by
   periodicity at the two final endpoints. The finite-chain step below
   specializes that mechanism; it is not a new general spectral criterion.
2. Baker, Barge and Kwapisz, *Geometric realization and coincidence for
   reducible non-unimodular Pisot tiling spaces*, Ann. Inst. Fourier 56
   (2006), 2213--2248,
   [published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf),
   Theorem 4.2 and Proposition 6.4. Integer translates and transitivity of
   coincidence must refer to realized strands or tilings. A formal walk
   alone does not provide that interpretation. Their almost-everywhere
   multiplicity conclusion remains a separate formalization obligation.
3. Barge and Kellendonk, *Proximality and pure point spectrum for tiling
   dynamical systems*, Michigan Math. J. 62 (2013), 793--822,
   [author preprint](https://arxiv.org/pdf/1108.4065), Sections 2 and 3.
   General proximality is not automatically transitive, and the spectral
   theorem retains its full-measure fibre-distality hypothesis. This
   construction uses the already proved pointwise eventual-coincidence
   relation and finite intersections of its open dense sets instead.

### Exact finite reduction

Interpret an integer output `v` by the existing length functional
`length(v) = sum_i ell(i) * v(i)`. For a signed edge `e` and arbitrary
real placement `x`, construct an actual legal hull member containing
`(source(e), x)` and `(target(e), x + length(edgeOutput(e)))`.
The forward edge uses its existing literal adjacent occurrence; a reverse
edge uses the same two tiles in the opposite order. Existence is obtained
by finite inflation and translation of an existing legal hull tiling.

An accepted finite walk can then be followed through finitely many actual
hull members. Consecutive members share the tile marking the current
control label and accumulated output. The members can differ from edge
to edge: the edge word is not asserted to be one legal substitution word.
The existing shared-tile theorem gives dense eventual coincidence for
each link. Finite induction combines these dense open sets using the
existing transitivity theorem. Intermediate members need neither zero
realization nor inflation periodicity.

The existing zero-fibre characterization gives an origin tile of type `b`
at `-length(z)` for an integer vector `z`, and gives a positive inflation
period. The automaton certificate for `(-z,b)` starts at the known seam
anchor tile `(1,0)`. Apply the chain result to those endpoints. Their
periods turn eventual coincidence into an actual common tile. Existing
zero-fibre equivalences then give every requested common-shift window.
This argument introduces no sequence limit or new compactness step;
the previously proved hull and density results remain explicit inputs.

### Controls and non-claims

- Reversed traversal is not reversal of a legal word. Check the negative
  output and translated tile positions against the same forward witness.
- Connectivity alone is insufficient: the merged deletion control for
  `00` and its inverse still forces `v(0)=v(2)` on anchor loops.
- Neither zero realization nor a shared-tile chain implies direct
  agreement at the origin. Retain the actual seam and interior controls.
- Do not require intermediate chain members to lie over zero or be
  inflation-periodic; those stronger assertions are not established.
- Keep a finite chain distinct from a single tiling containing all its
  marked tiles, and from a bounded enumeration of every zero-fibre member.
- The invariant-measure `L2` conclusion and the general PSC/BH/A1'/C4
  conjectures are outside this increment's proof target.

## Implemented finite certificate interpretation

The construction has two new Lean modules:

| Module | Proved interface |
| --- | --- |
| `C4FamilyTileAutomatonHull` | `lengthOutput`, actual-hull embedding of every finite supertile, literal adjacent occurrence realization, and the exact signed-edge hull bridge. |
| `C4FamilyFiniteZeroFibre` | Finite Walk/replay transfer, arbitrary integer displacement between arbitrary labels, universal zero-fibre coincidence and exact windows, and dense eventual coincidence for equal torus or full solenoid images. |

### Realizing an edge

Start with the existing legal seam tiling. Every letter occurs after two
inflations. Select an occurrence of the parent letter, translate it to
coordinate zero, and inflate finitely many more times. This embeds the
complete requested supertile at its original coordinates in an actual
legal hull member. The known prefix/suffix decomposition of each bigram
then supplies the two marked tiles. Translating that hull puts the first
mark at any requested `x`.

For an inverse edge, place the forward witness at the other end and swap
the two marked tiles. The exact negative output accounts for the reversed
displacement. The proof never asserts that a reversed substitution word
is legal.

### Interpreting every finite replay

`dense_eventual_of_replay` preserves the full replay contract:

```text
replay a w = some (b,v)
(a,x) in T
(b,x+lengthOutput(v)) in U
    implies Dense(eventual T U).
```

The empty word uses the shared tile. For a first edge, its realized hull
shares the initial tile with `T` and carries the next marked tile. Apply
the induction hypothesis to the rest of the word. Composition uses
`dense_eventual_trans`: the intersection of two open dense eventual sets
is dense, and their common middle tiling supplies pointwise transitivity.
Only a finite induction is involved. This does not assume transitivity
of general proximality.

For arbitrary start label `a`, the exact certificate word is

```text
reverseWord(terminalWord(a)) ++ certificate(v,b).
```

The reversed terminal word has zero output and takes `a` to the anchor
control `1`; the existing certificate then produces exactly `v` and ends
at `b`. The native `entry_word` and `walk_output_from` functions replay
this same interpretation using the vendored DFA. The native check covers
all nine source/target pairs as well as the empty-path starting-label and
reversed-edge controls.

### Closing every zero-fibre pair

The implementation uses arbitrary start labels, so it does not need to
choose a distinguished seam endpoint. Given two zero-fibre tilings,
the existing realization theorem supplies integer vectors `zT,zU` with
origin starts `xT=-lengthOutput(zT)` and `xU=-lengthOutput(zU)`. The finite
certificate displacement is `zT-zU`, since

```text
xT + lengthOutput(zT-zU) = xU.
```

The actual origin tiles are therefore endpoints of the interpreted
certificate. This proves dense eventual coincidence. The existing
zero-fibre periodicity theorem gives positive periods `m,n`. Inflate a
coincidence to a depth divisible by `m*n`; both original tilings return,
so the coincidence is a tile shared by the original pair.

For every `k>=2`, the resulting public endpoints are:

- `zero_fibre_common_tile`: any two actual tilings over the full zero
  history share a labelled tile at an identical position.
- `zero_fibre_exactProximal`: for every positive radius there is a common
  translation giving exact agreement on that window.
- `zero_fibre_windowWitnesses`: the original three-agreement interface,
  at every positive radius, with actual auxiliary hull members.
- `zero_fibre_closedOriginWitnesses` and
  `zero_fibre_stronglyRegionallyProximal`: the equivalent published-style
  witness interfaces, now supplied rather than assumed.

### Equal general fibres

Equality of the actual zeroth torus coordinates means that
`realVec(T)-realVec(U)` lies in the integer lattice. Its length is exactly
`xU-xT`, by the existing `dot_realVec` theorem. The same finite certificate
therefore proves `dense_eventual_of_torusRealize_eq`. Projecting equal full
solenoid histories to their zeroth coordinate gives
`same_fibre_dense_eventual`.

These two results conclude dense eventual coincidence. They do not add
periodicity to general fibres or promote their conclusion to a shared
tile, exact proximality, or almost-everywhere singleton fibres.

## Relationship to concurrent work

[PR #648](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/648)
was inspected at `b4d8e849bdcec622795e37de16c5a4e71b9e999a` while this
increment was being developed. It gives a separate return-group proof
of the zero-fibre and general dense-eventual targets. This increment is
an independent certificate interpretation of the merged finite automaton;
it does not import that PR or claim to be the first proof of those
mathematical conclusions. Existing unpublished local closure work is
also not a dependency. Every imported project source in the acceptance
manifest is present on the stated main baseline or in this increment.

## Acceptance and replay

The final two new modules compile under pinned Lean `4.34.0-rc2`, with
`autoImplicit=false` and `pp.unicode.fun=true`. The independent audit
checks **26 owned declarations, 25 theorem constants, 22 source-named
proofs, 20 separately specified endpoint types and owners, and 48
refusal controls**. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted in recursive axiom closure. The semantic refusals detect
changed contracts; they are not proofs that every changed proposition
is false. The existing actual seam and interior-origin counterexamples
are separately retained and checked.

The final local acceptance freshly compiles **60 project modules** in
the targeted closure and replays all four audit fixtures. Only external
dependency artifacts are reused, with all nine source revisions verified.
The new modules compile without warnings; inherited baseline warnings and
the corrected initial audit-dependency omission are preserved in the
evidence. This is source-bound local acceptance, not a hosted result or
a full-repository build claim.

The native check retains all 40 control and 30 output entries, the
unimodular generator identity, the reduced-graph obstruction, and 151-bit
exact integer recipes. It adds all nine source/target combinations,
three inverse entry words, and starting-label/orientation refusals.

Replay the native certificate from `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_family_tile_automaton.mojo
```

Replay the formal endpoints from `proof/PscVerif/`:

```sh
lake --no-cache build PscVerif.C4FamilyFiniteZeroFibre
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true C4FiniteHullWitnessAudit.lean
```

The complete repository family gate is `tools/check_c4_parameter_family.sh`.
It builds these modules from isolated sources and checks the exact audit
receipt and refusal count. Source-bound local evidence is archived under
[`evidence/c4-finite-hull-witnesses-2026-11-21/`](../evidence/c4-finite-hull-witnesses-2026-11-21/README.md).
Hosted acceptance remains a distinct observation at the published revision.

## Remaining formal boundary

The automaton interpretation and universal zero-fibre witness existence
are no longer missing premises of this route. The ordinary-proximality
and coincidence-rank interpretation for general fibres, intrinsic
maximal-factor identification, almost-everywhere singleton-fibre result,
and invariant-measure `L2` conclusion retain their own formal obligations.
Concurrent work on them must be credited at its own revision and scope.
The present result changes no universal PSC, BH, residual A1', or C4
claim status.

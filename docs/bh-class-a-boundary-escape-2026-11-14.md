# Class-A boundary escape by physical overlap width

This Lean development complements the broader written coverage in
[#578](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/578)
and [#579](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/579).
It is integrated on #579 at `110e7e9ef8243bc24adf80d6e8a375add586d850`.
The residual box below describes the remaining Lean obligation on this
proof route. The larger published-proof interfaces in those PRs have
their own acceptance and formalization scope.

## Stop/go

Proceed from the run-gap theorem at `5bb93df70c247f9cdf8b5ca3b085a69ffef499d8`
for [#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452).
Test a stronger geometric entry statement. Starting from any strict packet,
select an actual child whose common interval is wide enough to reach the
run gap. Use the previous run-gap theorem only after a strict packet enters.

- [Akiyama–Lee, Definition 2.4 and Theorem 2.5](https://arxiv.org/pdf/1003.2898)
  describe overlap coincidence for realized tilings with the Meyer-set
  hypothesis. Here the goal is an explicit ordered occurrence path from
  each formal strict packet and the proof uses literal word inflation.
- [Akiyama, Theorem 3.2](https://arxiv.org/pdf/1509.04471) requires sufficiently
  many choices of control points for the multiple-strong-coincidence bridge.
  Keep that spectral bridge separate from the width argument.
- [Minervino–Thuswaldner, §§8–9](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf)
  include finite places in nonunit Pisot realization. The real overlap
  argument does not supply an adelic dictionary.

Reuse the repository's interval mass and literal marks. A wider descendant
requires a selected choice. The previous constant-radius cycle remains a
control against decrease along every edge. A small overlap can split into
three atoms even when each tile has length one. Half-tile capture should
therefore depend on the inflated width, and touching endpoints need to
remain excluded from the actual strict edge relation.

## Work shown

### Assumptions and hypotheses

Use `x → xy^(n+d)x`, `c → cy^n x`, `y → xy^(n−1)c`, with
`n=k+t+3`, `d=k+2t+5` and `K=k+1`. The length convention is
`L_y=1`, `L_c=1+h`, `L_x=2+α−h`. Exact scaling gives `β=n+2+α`,
`βh=1`, `βα=t+3−2h` and `(1−α−2h)(β+1)=K`.
Lean constructs positive exact lengths from the positive cubic root.
For `n≥7` we have `β≥9`, `0≤α<1`, `L_x≥2`, and all three lengths lie
in `[1,3)`, with `L_c≤L_x`.

### Derivation / reduction

**A half tile of overlap.** Let the width of a strict common interval
be `W`, with all tile lengths at least one. After inflation its width
is `βW`. For `0<m≤1/2` and `βW≥3m`, select a point within `m` of the
left edge, away from both finite sets of literal cuts. Take the two
actual marks containing the point. If their common interval has width
at least `m`, these marks suffice. Otherwise the tile that starts
first must also end first, since both tiles have length at least one.
Its end is less than `2m` from the common left edge. There is at least
`m` of room in the inflated common interval to its right, so the
next literal tile on that track exists. The other mark extends at
least `1−m≥m` past the first tile's end. The next tile and that other
mark therefore overlap by at least `m`. This proves the selected
successor bound `min(βW/3,1/2)`. If half-tile width has not been reached,
choosing these successors gives growth by at least `β/3>1`. An
Archimedean argument gives finite entry to width at least `1/2`.

**Boundary entry from a half tile.** For an upper-boundary source, let
`D` be the signed difference of the two inflated run starts and let
`X=D−R_top>−1`. The top LAST tile starts at relative coordinate zero
and has length `E`. The bottom FIRST tile ends at `X` and has length
`F`. The inflated common interval has width at most `F+E−X`. If the
parent width is at least `1/2`, the inflated width is at least `β/2`.
A `c` at either endpoint would give `F+E−X<L_x+L_c+1=4+α≤β/2`.
Thus both endpoint letters are `x`, so `E≥2`. Also `β/2>F+1`, giving
`X<E−1`. If `X≥0`, the first bottom RUN tile lies wholly in top LAST.
If `X<0`, use the second bottom RUN tile, whose start lies in `(0,1)`.
These are actual words and marks. Each chosen child has width at
least one. Exchanging tracks proves the lower-boundary result.

An out-of-gap source has inflated width less than `F+E+1<7` on either
side. A unit-width child inflates to width at least `9`, so it lies
in the run gap. This proves **entry from every strict packet whenever
`n≥7`**, including `k<4` in that range.

**Residual strip and coincidence.** Apply the preceding central RUN
rounding theorem after entering the gap. It reaches `K·M≤5`, sharpened
to `K·M≤4` for `K≥3`, where `M=max(|p|,|b|)` is the integer radius
in coordinates `(p,q,b−2p−q)`. A further rounded edge preserves the
radius and sets the third slot `q` to the old `b−2p`. Thus the reached
packet has `|q|≤15`, and it still has the same radius bounds and strict
central clipping. This gives a fixed finite box for the possible
remaining targets at every parameter with `n≥7`. When `k≥4`, the
prior radius descent reaches a typed `y/y` coincidence at zero.

For an actual marked source the occurrence lifting theorem gives a
coherent path of irreducible balanced factors. In every nonempty
irreducible balanced pair, the first two letter occurrences start
at the same coordinate and overlap strictly. Applying the lift there
and stopping at the first coincidence proves the unconditional
`ChildNC` productivity theorem for **every irreducible block**, with
no restriction on its seed, when `k≥4`.

### Evidence and replay

[OccurrenceWidth.lean](../proof/PscVerif/PscVerif/OccurrenceWidth.lean)
uses the existing finite prefix-cut avoidance, indexed marks, and exact
`packetMass` transport. [ClassABoundaryEscape.lean](../proof/PscVerif/PscVerif/ClassABoundaryEscape.lean)
proves the boundary width estimates, both orientations, the whole-domain
entry, the residual box, the strict path, the root existence, and the
unconditional literal-block endpoint. The
[focused audit](../proof/PscVerif/ClassABoundaryEscapeAudit.lean) pins the
principal types to independent spellings of the words and incidence-free
hypotheses, and checks the transitive axiom closures.

```sh
cd proof/PscVerif
lake build PscVerif.ClassABoundaryEscape
lake env lean ClassABoundaryEscapeAudit.lean
lake env lean ClassARunDescentAudit.lean
```

From the repository root, `./tools/check_class_a_zero_defect.sh` runs
the three focused Class-A audits with the repository's isolated source
and pinned dependency policy.

The focused local build uses pinned Lean 4.34.0-rc2 and prepared
transitive dependency objects. It compiles the changed modules and
checks the focused audits. The complete library replay and hosted
acceptance remain separate. This increment adds Lean proofs over the
existing occurrence implementation, without a new executable census.

### Negative controls

Two doubled unit tiles displaced by half a unit have common inflated
width `3/2`. Three ordered child pairs have width `1/2`, and the
remaining pair has zero width. The audit uses a third letter of
length `5/4` to encode the uninflated displacement by an exact integer
packet. A larger general threshold from the same `3/2` premise fails.

For `(k,t)=(4,0)`, the `x/x` packet with bottom-minus-top offset
`(1,−5,5)` has width `5h≥1/2` and run-start difference
`15+2α−2h>15`. It lies strictly outside the old run-gap theorem.
The checked boundary rule supplies a literal full-width child.
The inherited constant-radius cycle remains a control on the scope
of the selected rounding descent.

### Non-claims / remaining gaps

The strict-zipper escape obligation of #452 is discharged for the
subfamily `k≥4`. For `k≤3` and `n≥7`, it reduces to productive exits
from the bounded residual `y/y` box. Each of the ten pairs with `n≤6`
has `k+t≤3` and already appears in the exact finite
[S18 certificates](../evidence/class-a-finite-certificates-2026-11-02/README.md).
Those certificates cover the full closure of their eighteen specified
seeds. General BH, A1′, the nonunit adelic dictionary and the universal
Pisot substitution conjecture remain separate.

## Published spectral bridge for the `k≥4` subfamily

The following finite-carrier and spectral argument is written
mathematics. The Lean endpoint supplies the actual paths and positive
length equations. The finite-carrier extraction and the imported
spectral theorems remain outside this candidate's formal verification.

1. **Exact arithmetic.** The incidence matrix, in `(x,c,y)` order, is
   `[[2,1,1],[0,1,1],[n+d,n,n−1]]`. Its characteristic polynomial is
   `f(z)=z³−(n+2)z²−(t+3)z+2`. Its three real roots lie in `(-1,0)`,
   `(0,1)`, and `(n+2,n+3)`, by the strict endpoint signs. The four
   possible rational roots `±1,±2` all give negative values. Explicitly
   `f(-1)=−K`, `f(1)=−n−t−2`, `f(2)=−4n−2t−4` and
   `f(-2)=−4n+2t−8`. Thus the polynomial is irreducible, the Perron
   root is Pisot, and the determinant is `−2`. The directed letter graph
   contains `x→y→c→x` and an `x` loop, so the substitution is primitive.
   A periodic primitive shift would have rational letter frequencies.
   Substituting a nonzero rational frequency vector in the incidence
   eigenvector equation would make the Perron root rational. Thus the
   primitive shift is aperiodic. The arithmetic agrees with the prior
   [Class-A domain calculation](p1b-class-a-run-index-2026-10-21.md).
2. **A finite actual packet cover for each fixed substitution and seed.**
   Take the strict marked pairs in the ordered seed `xy/yx` and all
   their strict packet descendants by literal edges. The offset evolves
   as `v′=Mv+c` with a finite set of literal prefix corrections `c`.
   The Perron coordinate is bounded by the two overlapping tile lengths.
   For either contracting eigenvalue `λ`, the absolute value of the
   corresponding left-eigenvector coordinate is bounded throughout by
   its maximum initial value plus the largest absolute projected
   correction divided by `1−|λ|`. The three eigenvalues are distinct,
   hence the three independent left eigenvectors bound `v` in an
   ordinary bounded real box. The integer offsets and the two letters
   give a finite set. It contains every strict packet of each full word
   iterate by restriction to the actual parent tiles and backward
   scaling of their common interiors. By construction the cover is
   closed under every strict literal child.
3. **Finiteness of full balanced factors.** Choose a finite successful
   path from each packet in the cover and take the maximum depth `D`.
   A typed zero hit persists to depth `D` under the common image of
   the coinciding tile. In any factor at generation at least `D`
   having length greater than `2β^D·max L`, choose a point with margin
   greater than `β^D·max L` on both sides, away from parent cuts.
   At the ancestor generation `D` steps earlier the point lies in a
   strict packet of the cover. Its chosen zero hit supplies an equal
   Parikh prefix cut at generation `D` inside the inflation of those
   two ancestor tiles. Both inflated tiles have length at most
   `β^D·max L`, so the cut lies strictly inside the proposed factor.
   This contradicts irreducibility. Thus the factors have bounded
   length, using `min L=1`, and the finitely many earlier generations
   add only finitely many factors. This is also the premise-level
   construction for [#574's finite-carrier consumer](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd23a6681db651762e49c9c959a9aad682fb007f/proof/PscVerif/PscVerif/BHFiniteCarrier.lean).
4. **Apply published mathematics.** The ordered swap seed uses distinct
   letters. Its full factor inventory is finite by step 3, and every
   factor has a singleton coincidence descendant by the Lean endpoint.
   Together with step 1 these discharge the written hypotheses of
   [Barge–Štimac–Williams, Corollary 2](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   yielding pure discrete spectrum for the substitution tiling flow
   if that published implication is imported. The symbolic consequence
   additionally uses [Sirvent–Solomyak, Corollary 5.2](https://doi.org/10.4153/CMB-2002-062-3)
   for primitive Pisot substitutions. Neither spectral implication is a
   theorem of the Lean candidate.

The trace is `n+2≥9` in the proved subfamily, outside the trace-at-most-two
coverage of [Akiyama–Gähler–Lee](https://dmtcs.episciences.org/en/articles/2089).
The initial letter map is `(x,c,x)` and the terminal map is `(x,x,c)`.
Their positive powers retain the failure of injectivity, including after
reversal. This excludes the immediate endpoint-map application of
[Barge's 2016 theorem](https://doi.org/10.3934/dcds.2016.36.1159). The
repository records earlier certified infinite Class-A lines and finite
specimens. No priority claim or classification of conjugacies is made.

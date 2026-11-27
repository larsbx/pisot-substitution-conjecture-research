# Literal third-level entry: completed Lean binding

## Result and scope

`PscVerif/BHThirdLevelEntry.lean` completes the actual-occurrence entry
argument written in
[`bh-third-level-windows-2026-11-24.md`](bh-third-level-windows-2026-11-24.md).
It proves that **every strict source packet**, retaining its two arbitrary
letter labels and its entire integral displacement vector, reaches the
type-1/type-1 run window under the following explicit hypotheses:

\[
\sigma(0)=1,\qquad \sigma(1)=01^k2,\qquad \sigma(2)=0^r1,
\]

\[
0<k,\quad k<\beta,\quad
\beta^3=k\beta^2+2\beta+r,\quad
12<\beta,\quad r<\beta,\quad \frac{3\beta}{4}<k-1.
\]

The exact length vector is

\[
\ell=(1,\beta,1+r/\beta).
\]

The first three hypotheses are the existing `RunFamily r k β` structure.
The other three are scalar coefficient bounds. None asserts entry,
termination, existence of a suitable mark, a clean window, or a finite
carrier. The diagonal `k=r≥12` and the adjacent bands `k=r+1,r+2` with the
specified real root satisfy these bounds; the family wrappers are kept
separate from the shared literal entry theorem.

The principal endpoint is:

```lean
theorem run_family_entry {r k : ℕ} {β : ℝ} (h : RunFamily r k β)
    (hβ : 12 < β) (hrβ : (r : ℝ) < β)
    (hwindow : 3 * β / 4 < (k : ℝ) - 1)
    (p : Packet) (hp : p.Interior (lengths r β)) :
    ∃ q, Relation.ReflTransGen
      (InteriorStep (sigma r k) (lengths r β)) p q ∧
      Central r k β q
```

Here `Central r k β q` means exactly
`q.top = 1`, `q.bottom = 1`, and
`|offset (lengths r β) q.delta| ≤ k-1`.
The stronger `run_family_entry_ordered` supplies a single
`OrderedInteriorPath` with the same source, endpoint, and complete list of
original top/bottom occurrence ordinals. Every intermediate packet is
strict, including the source of an empty preliminary path.

## Source decision

This is a direct formalization of the mechanism already approved for
development by
[`bh-third-level-and-diagonal-stop-go-2026-11-24.md`](bh-third-level-and-diagonal-stop-go-2026-11-24.md).
It does not introduce a different selector, a new termination conjecture,
or a stronger general Pisot hypothesis. The prior source decision records
the overlap framework of Sirvent–Solomyak and the actual-letter and
abelianized-prefix framework of Barge–Diamond, with the limits of the
shift-radix analogy. The contribution here is the completed Lean binding
to this literal family, including the previously missing mark-location
and ancestry obligations.

## Work shown

### Assumptions and hypotheses

The packet displacement is an arbitrary vector in `Fin 3 → ℤ`. No
coordinate bound, source realization in a finite carrier, central-source
assumption, or prescribed source-label pair is introduced. Physical
offsets use the repository's top-minus-bottom convention. Therefore a
bottom track at depth three begins at

\[
S=-\beta^3\operatorname{offset}_\ell(p.\delta).
\]

`run_lengths_scale` proves exact scaling
`physicalLength ℓ (sigma r k a) = β * ℓ a` for all three letters directly
from `RunFamily`. In particular, this proof does not use the
off-diagonal quadratic descent window, which fails on the diagonal.
Existing `RunFamily.lengths_ge_one` supplies the unit lower bound on all
tile lengths.

The geometric bounds have distinct roles. `r<β` gives
`ℓ 2 = 1+r/β < 2`, so a final type-2 tile has length less than two.
`β>12` provides enough room for three windows and the midpoint locators.
`3β/4<k-1` converts their final start-distance estimate into the desired
run-window inequality. No arithmetic independence is required merely to
transport or locate these literal occurrences.

### Derivation / reduction

#### 1. A genuine preliminary path reaches a half-unit overlap

`run_reaches_half_mass` specializes the already complete generic theorem
`OccurrenceWidth.reaches_half_mass`. From any strict packet it obtains a
finite sequence of actual strict occurrence edges to a packet of overlap
mass at least `1/2`. Both labels and all displacement coordinates remain
part of every vertex of this path.

`BHThirdLevelTransport.half_mass_common_interval` scales that overlap
three times. With `L=max(0,S)`, both original depth-three words contain the
common interval from `L` through `L+18β`. This uses
`β³/2≥18β`, established from `β>12`, and exact interval-mass scaling.

#### 2. Obstruction spacing follows from literal parent marks

`two_digit_structure` proves that a selected letter 2 in any image must
be the unique final 2 in `sigma(1)`. Its actual prefix is exactly
`0 :: replicate k 1`, and its suffix is empty.

`two_mark_parent` then uninflates an arbitrary selected type-2 occurrence
in an inflated word. It recovers an actual parent-1 occurrence and the
full prefix equality

\[
\text{child.before}=\sigma(\text{parent.before})\,01^k.
\]

Its physical start is consequently

\[
\beta\,\operatorname{length}_\ell(\text{parent.before})+1+k\beta.
\]

Two distinct type-2 child marks have different original parent-1 marks:
the exact prefix equality would otherwise identify their indices and
their entire marks. Distinct parent-1 occurrences are separated by at
least their length `β`. Thus `two_mark_separation` proves that the two
child starts differ by at least `β²`. One more inflation proves
`badStarts_separated`: starts of the images of second-level type-2 parent
marks differ by at least `β³`.

The set `badStarts` is defined from these actual parent marks. It is not
an independently assumed obstruction set. An arbitrary external track
origin is retained in its definition and cancels in the separation
calculation.

#### 3. A shared clean window is selected on both tracks

`BHThirdLevelGeometry.exists_clean_window` considers the three windows
of length `4β` starting at `L`, `L+7β`, and `L+14β`. Each actual bad block
is conservatively enclosed in an interval of length `2β`.

Starts separated by `β³>20β` imply that at most one relevant bad interval
occurs on each track. The gaps of `3β` prevent one such interval from
meeting the interiors of two windows. The existing finite theorem
`BHWindowChoice.exists_clean_slot` then selects a window common to both
tracks. Endpoint contact is allowed: the conclusion uses
`b+2β≤a ∨ a+4β≤b`. The subsequent locators use points strictly inside the
window and preserve this endpoint convention.

#### 4. The clean-window locator constructs original type-1 marks

`clean_window_locator` starts from an actual half-open containing parent
mark, even when the chosen point lies on a tile boundary. A parent-2
block is excluded by the derived clean-window property. There are then
two possible parent labels:

* The image of parent 0 is the single type-1 tile, giving the desired
  mark immediately.
* In the image of parent 1, a point in the initial zero is followed by an
  actual type-1 digit within one unit. A point in the run `1^k` is located
  by an actual mark of that replicate word and inflated into its original
  parent. A point in the final 2 lies less than two units before the next
  parent block.

The final case explicitly proves that a next parent exists, using the
three units of room before the end of the original word. `next_parent`
has the exact prefix `m.before ++ [m.letter]`. Its inflated start is
proved equal to the preceding parent's end. Because that start is
strictly inside the same clean window, this next parent is also not 2.
Its first type-1 tile begins after distance zero or one. Thus the desired
type-1 mark is at most three units to the right of the chosen point.

For a point `x`, the output start `c` satisfies

\[
c\le x+3,\qquad x\le c+\beta.
\]

The output is an actual mark in the once-inflated original word, with
its full prefix, selected letter, and suffix. This is not a statement
about a nearest point in an abstract set of tile starts.

#### 5. Two locators give the run-window bound

`third_level_marks` applies the top locator at `x=a+3β/2`. Its returned
start `c` lies between `a+β/2` and `a+3β/2+3`. The bottom locator is then
applied at `c+β/2`, a point whose three-unit continuation remains strictly
inside the same clean window. If `d` is its physical start, including the
bottom origin `S`, then

\[
c-\beta/2\le d\le c+\beta/2+3.
\]

Since `β>12`, this gives `|d-c|≤3β/4<k-1`. Both selected letters are 1.

#### 6. Exact original-mark assembly supplies the strict path

`BHThirdLevelTransport.assembled_has_ordered_path` uninflates both
selected depth-three marks until their original source letters. Its
terminal packet is exactly

\[
\bigl(1,1,\ M^3p.\delta+
  \operatorname{Parikh}(\text{top.before})-
  \operatorname{Parikh}(\text{bottom.before})\bigr).
\]

There is no deletion of a displacement coordinate and no replacement by
an equal physical projection. `assembled_offset` verifies the sign of
its physical displacement against the positioned starts. The strict
terminal overlap then pulls back along that very ordinal transcript via
`ordered_path_indexed_interior`.

`half_mass_entry` records exactly three strict edges after the half-unit
stage. `run_family_entry` concatenates those edges with the actual
preliminary path. `run_family_entry_ordered` retains the original
top/bottom ordinal pairs for the complete concatenated path, so the
existing `ordered_path_traced_original_prefixes` theorem can recover the
full original prefix and suffix traces at its endpoint.

### Evidence and replay

The following targeted build completed successfully with the repository's
pinned Lean `4.34.0-rc2` toolchain on 2026-11-27:

```sh
cd proof/PscVerif
lake build PscVerif.BHThirdLevelEntry
```

The final entry module compiled in 7.3 seconds in the recorded local run;
the dependency closure contained 2,210 build jobs, most already cached.
The entry module itself emitted no warnings. Pre-existing dependency
linter warnings do not affect the proof terms. No new executable census
or finite-domain test is used to justify this universal entry result.

The implementation is divided into three acyclic modules:

| Module | Discharged obligation |
| --- | --- |
| `BHThirdLevelGeometry` | Two separated obstruction sets leave a common clean window |
| `BHThirdLevelTransport` | Actual original marks assemble to full strict indexed paths; exact image and overlap scaling |
| `BHThirdLevelEntry` | Literal obstruction ancestry, the actual type-1 locator, both-track selection, and entry from every strict packet |

### Negative controls

The proof interfaces keep the conditions whose removal would invalidate
the written argument:

* The locator receives actual marks in the original words. Its final-2
  branch must construct an actual next parent; an abstract available
  digit cannot discharge that branch.
* Both tracks share the same clean window. A clean choice for one track
  does not supply the second locator's premise.
* The external bottom origin is carried through every bound and enters
  the final expression with sign `-β³ * offset`.
* The three-edge terminal packet retains `M³ * p.delta` and the full
  prefix residual. Equality of physical offsets or equality of word
  lengths does not replace this equation.
* Strictness is attached to each edge of the same ordinal transcript.
  Endpoint-only overlap is not substituted for a strict path.
* The scalar bounds `β>12`, `r<β`, and `3β/4<k-1` remain explicit. The
  module does not export the construction for unsupported parameters.

These are proof-contract controls, rather than additional finite samples.
The existing prefix-assembly module also retains its independent
counterexample showing that equal prefix word lengths and equal terminal
letters do not imply equality of full integral prefix vectors.

### Non-claims / remaining gaps

The actual-occurrence entry obligation for these coefficient bounds is
complete. No postulated entry predicate remains in `run_family_entry`.
The three-step bound starts only after the half-unit overlap stage; this
file does not assert a uniform total entry-depth bound independent of the
strict source packet.

This module supplies entry into the run window. Termination from that
window, literal zero-endpoint or coincidence assembly, and any transfer
to the global Pisot substitution conjecture belong to their separate
theorems and hypothesis checks. In particular, this family-specific
entry result does not by itself establish the general PSC. Independent
human review remains validation debt, not an omitted mathematical
premise or a reason to stop using the mechanically certified entry
theorem at its exact scope.

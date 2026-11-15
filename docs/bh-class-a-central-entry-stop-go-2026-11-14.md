# BH Class-A central entry: pre-code source and hypothesis gate

Date: November 14, 2026. Starting source:
`01c4e376a652fd93e981e7b302e989c65774a0de` (draft PR #577).

## Proposed claim and decision

**Proceed with the following exact, scoped theorem and implementation.**
For the literal minus-Class-A words

```text
x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n-1) c,
n=k+t+3, d=k+2t+5, k,t>=0,
```

investigate and verify that **every strict integral overlap reaches full
integral offset zero when `n>=6`**. The proposed proof forces a `y/y`
overlap of width at least one half by counting actual tile centers in
inflated image words. A selected nearest RUN child then gives a bounded
two-coordinate integer recurrence. Its nonzero periodic possibilities
are explicit alternating states; their actual ordered-occurrence exits
are proved separately. The prefix addresses must be retained through
the initial deep occurrence and every later selected edge.

This is a narrowed family theorem, not a universal ternary or all-alphabet
PSC theorem. The six parameter pairs with `n<6` require their own exact
source-coverage evidence. A result on those six S18 graphs must retain the
S18 seed definition, terminal policy and complete-child-closure contract.

## Primary sources inspected before new implementation

1. Kirschenhofer and Thuswaldner, *Shift Radix Systems — A Survey*, RIMS
   Kokyuroku Bessatsu B46 (2014), 1–59,
   [publisher PDF](https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B46/pdf/B46_001.pdf),
   especially the distinction between ultimate periodicity and the
   finiteness property, and the discussion of symmetric SRS near the end.
   Integer recurrences obtained by rounding contracting maps are established
   prior art. Their boundedness does not exclude nonzero cycles.
2. Kirschenhofer, Petho, Surer and Thuswaldner, *Finite and periodic orbits
   of shift radix systems*, Journal de Theorie des Nombres de Bordeaux 22
   (2010), 421–448,
   [author PDF](https://www.math.tugraz.at/~tichy/publications/finitev8.pdf),
   introduction and Section 2. Contractive linear parts imply eventual
   periodicity for the standard floor map, not necessarily zero hitting.
   Here the exact nearest-integer recurrence and its periodic states will
   be proved directly, rather than imported from a different rounding rule.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   Annales de l'Institut Fourier 64 (2014), 1373–1417,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf),
   Sections 2, 4 and 9. The prefix automaton records actual marked words;
   nonunit representation spaces have finite-place factors. No claim that
   an arbitrary rounded coordinate transition is an occurrence is allowed.
   This proof instead checks every RUN/FIRST/LAST index in the original
   substitution, and uses no unit-only tiling theorem or inverse-integrality
   assertion.
4. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, [author source](https://arxiv.org/abs/1003.2898). Complete overlap
   reachability is established methodology. This investigation does not
   import pure discreteness from an incomplete graph or from one productive
   selected cycle. Any finite exceptional-case certificate must be complete
   at its stated source scope.

The initial density proposal used ordinary Perron–Frobenius convergence.
Before implementation, it was strengthened to an elementary **fixed-depth
two-supertiling argument**, avoiding that convergence premise entirely.
For one-level blocks the y-density is at least `5/beta`, and the x- and
c-densities are each at most `1/beta`; the x-parent block makes all three
inequalities strict in the needed direction. Every original image contains
x, so every depth-two block has y-density strictly larger than `5/beta`
and both other densities strictly smaller than `1/beta`. Taking minima
and maxima over the three literal blocks leaves a strict gap. The actual
overlap interval has at most two partial depth-two blocks on each track.
No frequency-limit, ergodic, spectral or tiling theorem is needed for this
finite-block version.

## Existing evidence and negative controls

The append-only side-notes ledger, the #577 entry stop/go, the zero-defect
proof, the old signed-strip/transfer-plane guards and the original complete
22-member certificate were inspected before this mechanism.

The earlier proposed three-step decrease of
`|p-delta|+|p+q+r|` is only a finite observation on those 22 graphs. At
`k=t=0`, the cyclic seed-reachable source `(y,c,1,3,-5)` requires three
steps to decrease that rank and must increase it first. The strict formal
source `(x,x,-1,-5,6)` needs four steps; it is outside the archived seed
closure. Simple clipped coordinate bands also fail actual child closure.
These controls rule out using the finite rank observation or an empirical
rectangle as a source-coverage theorem.

The new construction instead needs negative controls for: a noncentral
source presented to the central RUN selector; the short-word `n<6` face;
a wrong sign or rounding interval; a nonexistent RUN treated as LAST or
vice versa; an altered full offset; a selected nonzero two-cycle mistaken
for a zero hit; a capped search mistaken for a proof; and omission of a
required child or root from a small complete graph.

## Acceptance boundary

Record a written proof, canonical checked-arithmetic Mojo, independent
literal-word/exact-field replay, and proof-producing Lean endpoints where
implemented. Keep the written theorem, executable algorithm, finite
exceptional certificates and formalized subset distinct. The full original
prefix equality and composability are part of the mathematical conclusion;
zero physical displacement alone is not the target. Stop a production path
at its first full integral-zero hit. No general BH, A1-prime, C4, G1, PDS or
PSC claim status is changed by this pre-code decision.

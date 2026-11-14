# Minus-Class-A constant entry: pre-code source and hypothesis gate

Date: November 14, 2026. Starting source:
`34ff471c24960729527ae5f090e96c7c16ae4584` (draft PR #578).

## Proposed claim and decision

**Proceed with this exact, scoped theorem and implementation.** For the
literal minus-Class-A words

```text
x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n-1) c,
d >= 5, n >= d+1,
```

investigate and verify that every strict integral overlap reaches typed
coincidence through actual original child occurrences. The initial target
was the residual wedge `d+1 <= n < 5d`. The hand-derived three-RUN descent
below has no upper bound on `n`; the proposed theorem therefore includes
the full lower chamber `d <= n-1`.

Normalize `Ly=1`, let `beta` be the Perron root, and put
`h=1/beta`, `alpha=beta-(n+2)`, `delta=d/(beta-1)`. Here
`n+1 < beta < n+2`, `alpha<0`, `1<Lc<Lx<2`, and
`2h-alpha=1-delta<1`. One-level literal-word density bounds should force
entry into a central `y/y` overlap. The legal nearest RUN selector gives
the positive-coefficient recurrence
`z[j+2]=nearest(2h*z[j]-alpha*z[j+1])`.
Boundedness gives a periodic tail; the extra inequality `2h<1/2` forces
each periodic tail to be constant. A constant of height `H` represents
the full integral offset `U_H=(y,y,H,-H,0)`.

For `H>=1` and `2dH<=n`, the proposed original RUN index pairs are

```text
(dH+2, 1),
(1, n+2-dH),
(1+max(d(H-1)-2,0), 1+max(2-d(H-1),0)).
```

The full intermediate offsets are `(H,-H,-1)`, `(H-1,-H-1,2)`, and
`(H-1,-H+1,0)`. Thus each three-edge segment lowers the height by one;
reversal handles negative heights. These are proposals at this gate,
to be checked symbolically, against literal words, and in the formalized
algebraic subset. Retain the full composed prefix equality `M^m w=P-Q`.

## Primary sources inspected before new implementation

1. Kirschenhofer and Thuswaldner, *Shift Radix Systems — A Survey*, RIMS
   Kokyuroku Bessatsu B46 (2014), 1–59,
   [publisher PDF](https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B46/pdf/B46_001.pdf).
   Its introduction and symmetric-SRS discussion distinguish eventual
   periodicity from the finiteness property. Rounding a contracting linear
   map does not by itself establish zero hitting. Here constant cycles
   require separate actual-occurrence exits.
2. Kirschenhofer, Petho, Surer and Thuswaldner, *Finite and periodic orbits
   of shift radix systems*, JTNB 22 (2010), 421–448,
   [author PDF](https://www.math.tugraz.at/~tichy/publications/finitev8.pdf).
   The introduction and contractive-orbit discussion concern the standard
   floor map. The nearest-integer recurrence, its finite pair bound and
   its constant-cycle classification must be proved for the present signs
   and hypotheses rather than imported from that different rounding map.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   AIF 64 (2014), 1373–1417,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf).
   The marked prefix automaton and the nonunit representation space
   motivate retaining the actual original letters and prefix words.
   This determinant-minus-two family needs no inverse-integrality premise
   and no unit-only spectral theorem for the proposed path construction.
4. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, [author source](https://arxiv.org/abs/1003.2898).
   The complete-overlap reachability framework is prior art. The proposed
   result supplies composable paths at its declared source scope; it does
   not infer a finite carrier from sampled paths or import spectral
   conclusions into an unformalized tiling or shift system.

The prior #578 stop/go, its exact-source proof and the append-only
side-notes ledger were also read. Its upper-chamber binder enforces
`d>=n+2`; it must not be weakened or bypassed to admit this new chamber.
Use the shared exact arithmetic, literal prefix and geometric overlap
engines with a new literal-family parameter binding instead.

## Required negative controls and acceptance boundary

Retain the previous failures of coordinate-only ranks and empirical
clipped carriers. New checks must reject a wrong family or field binding,
an out-of-domain parameter, a noncentral source at the central selector,
an out-of-range original RUN index, an altered full integral offset, a
positive constant cycle mistaken for zero, and a truncated or capped
search mistaken for a mathematical conclusion. Check first-integral-zero
termination and typed-zero termination separately at the entry adapter.

The written theorem must prove entry from every strict integral source;
finite source fixtures alone cannot provide that quantifier. The native
algorithm must use checked arithmetic and retain all actual edge indices.
An independent exact-field/literal-word oracle must replay complete
prefix certificates, including long and negative-height paths. Symbolic
inequalities must cover the unbounded chamber, and Lean endpoints must
state their formalized subset accurately. A source-isolated Lean gate
must bind its precise input files and fail if it cannot decide.

Assembly with earlier minus-Class-A results must cite the separate
`d<=4` regions and the two seam lines `d=n,n+1`; neither is included in
this new chamber. No universal BH, plus-Class-A, A1-prime, C4, G1, PDS,
PSC or all-alphabet status is promoted by this pre-code decision. Human
review and exact-head hosted acceptance remain distinct obligations.

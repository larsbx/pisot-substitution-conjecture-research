# Exact class-A full-Parikh to cubic-Perron field bridge

**Status:** scoped algebraic arithmetic theorem for the *minus class-A* normal form, with a Mojo-first checked-in contract and an independently executed exact Python reference. Native Mojo CI and independent review pending. Not all-descendant productivity, BH/#139, G1, PDS or PSC.

## Why this is the needed interface

Recent research PRs #428–#435 represent oriented overlaps as
`(top,bottom,p,q,r)`, with **full integer bottom-minus-top Parikh offsets**. The canonical native overlap graph stores
`OverlapState(top,bottom,shift:CubicElt)` in the power basis
`1,beta,beta^2`. Merely comparing an integer five-tuple to a
cubic-field state without an explicit normalization would be unsound.
The native eigenvector constructor can choose a different positive
overall scale, so this bridge must be used with its own canonical
normalized length vector or a separately verified scale conversion.

For k,t>=0 set n=k+t+3, d=k+2t+5, A=n+d, and use
x->xy^A x, c->cy^n x, y->xy^(n-1)c.
The incidence matrix in (x,c,y) coordinates is

    [ 2  1   1 ]
    [ 0  1   1 ]
    [ A  n  n-1]

with characteristic polynomial exactly

    χ(B)=B^3-(n+2)B^2+(n-d-1)B+2.

The native verifier also checks that a proposed pair (n,d)
actually belongs to this two-parameter integer chamber, not merely
that n>=3 and d>=5. The inverse parameter formulas are

    t=d-n-2,     k=2n-d-1.

Both must be nonnegative integers. A matching formal cubic at an
off-chamber (n,d) is explicitly **refused**, rather than credited
with an unproved admissibility hypothesis.

**No floating root or analysis is used.** The existing exact irreducible
Pisot cubic certificate supplies the distinguished real embedding.

## The integer-linear bridge, proved by coefficients

Choose the common *positive* normalization factor beta(beta-1)
from the existing minus-class-A exact geometry. The three tile
lengths in the integral cubic power basis are

    Lx = (-1,d,1),  Lc=(-1,0,1),  Ly=(0,-1,1).

An oriented full Parikh displacement (p,q,r) therefore has the
exact cubic coefficient triple

    S_d(p,q,r) = (-p-q, d*p-r, p+q+r).

The coefficient matrix with columns Lx,Lc,Ly has determinant **d**.
Since d=k+2t+5 >=5, this map is injective over the integers
(and over the rational coefficients of the irreducible cubic field).
This is a **derived scoped independence fact**, not an
assumed globally valid tile-length Z-independence hypothesis.
No such assertion is imported for a different substitution family
or an unverified native field normalization.

More strongly, the exact image sublattice in the chosen cubic
power basis has index d. For an arbitrary cubic triple (u,v,w),
membership in the full-Parikh length lattice is precisely

    d divides (u+v+w).

When divisible, the unique full Parikh coordinates are

    p=(u+v+w)/d,   q=-u-p,   r=u+w.

The native decoder **refuses**, rather than rounds, if divisibility
fails. In particular, S_d(p,q,r)=0 implies p=q=r=0.
Therefore for a fixed *equal-type* overlap in this normalized
irreducible cubic class, **native cubic shift zero is equivalent
to the full integer Parikh offset being zero**. This bridges
the different typed-coincidence predicates without silently
equating untyped offset-zero states with coincidences.

## Commuting child transport

With the full incidence action

    M(p,q,r)=(2p+q+r,q+r,A*p+n*q+(n-1)*r),

the exact cubic characteristic relation yields

    S_d(Mw) = beta * S_d(w)

coefficientwise in the cubic quotient ring. This is checked using
`cubic_mul_beta`, not a numerical eigenvalue.

For genuine ordered word occurrences i,j with actual proper
prefix Parikh vectors Ptop(i), Pbottom(j),

    w' = Mw + Pbottom(j)-Ptop(i)

implies

    S_d(w') = beta*S_d(w)
              + S_d(Pbottom(j)-Ptop(i)).

The new native entry point verifies all coefficients using
checked Int operations and rejects an invalid characteristic
polynomial, an off-lattice shift, a forged child Parikh vector,
negative proper-prefix counts and arithmetic overflow.
The exact typed occurrence addresses themselves must be
validated against the real substitution word separately.
The checker does not invent a RUN/LAST classification.

## Evidence and boundary

- Canonical `kernel/psc/class_a_parikh_field_bridge.mojo`:
  checked cubic-field normalization, full-Parikh encoder,
  exact sublattice decoder, beta-intertwiner and child equation.
- Native `kernel/tests/test_class_a_parikh_field_bridge.mojo`:
  sample field parameters, all basis lengths, numerous signed
  Parikh triples, the actual X(d+1,0)->Q child, off-lattice
  refusal, wrong-field refusal and corrupt-child refusal.
- Independently written
  `reference/psc_research/class_a_parikh_field_bridge.py`
  plus `tests/test_class_a_parikh_field_bridge.py`:
  **5 tests passed locally** using arbitrary-precision
  integers and actual literal substitution-word prefixes.
  They check 7,020 coefficientwise intertwining cases
  across 117 parameter specimens, every actual ordered
  occurrence for five canonical class-A source labels on
  a 5x5 grid, true reversal covariance, the exact inverse
  lattice formula and off-lattice refusals.

The arithmetic identities are **universal hand-coefficient proofs**
with executable finite implementation replays. Native Mojo compilation
is **not** claimed in this environment; only fresh exact-head hosted
locked-Mojo CI can supply that receipt. The independent reference is
secondary and cannot replace the canonical native kernel.

This bridge removes a representation mismatch in future
proof-carrying X-quotient certificates; it does **not**
supply a symbolic complete overlap carrier, a universal
rank, a seed-to-literature realization transfer, or PSC.
See Akiyama–Lee (2011), *Algorithm for determining pure
pointedness of self-affine tilings*, for the established
overlap-coincidence framework. The new contribution is
the precise class-A integer coefficient conversion and
its fail-closed executable verification contract.

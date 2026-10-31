# Exact native class-A Perron normalization: closing the representation gap

**Status:** scoped all-parameter coefficient identities plus a fail-closed,
Mojo-first **actual native table** contract, stacked on the original
research-normalized Parikh/cubic map in PR #438. The independent Python
reference and its four tests have passed locally; **the repaired native Mojo
tests also pass locally; hosted exact-head acceptance remains pending**. No global integer-independence
assumption, all-X-descendant productivity, BH/#139, G1 or PSC is claimed.

## Targeted prior-work boundary

Perron-Frobenius uniqueness of a positive left eigenvector up to a
positive factor is standard. The use of exact tile-overlap coincidence
in primitive substitution tilings is also standard; see Akiyama–Lee,
*Algorithm for determining pure pointedness of self-affine tilings*
(2011), Advances in Mathematics 226, 2855–2883.

The new scope is not that literature result: it is the explicit *integer
cubic-power-basis normalization* **actually returned by the repository's
native `perron_tile_lengths_in` algorithm**, with exact checked inverse,
literal-word child compatibility, and refusal of an unverified
normalization.

## All-parameter minus class-A derivation

For k,t>=0 let n=k+t+3,d=k+2t+5,A=n+d and

    x -> x y^A x
    c -> c y^n x
    y -> x y^(n-1) c.

The full incidence matrix in the (x,c,y) basis is

    M = [[2,1,1],[0,1,1],[A,n,n-1]]

and its irreducible cubic in the standing regime is

    chi(B)=B^3-(n+2)B^2+(n-d-1)B+2.

The parent PR #438 uses **research-normalized** positive length
vectors in the basis (1,B,B^2):

    Lx=(-1,d,1), Lc=(-1,0,1), Ly=(0,-1,1).

These correspond to a common positive length factor B(B-1).

However, the repository's actual `perron_tile_lengths_in`
algorithm takes the first nonzero row cross product of
`M^T-B*I`. In the class-A family, the first two rows are

    (2-B, 0, A),     (1, 1-B, n).

Their cross product is already nonzero and positive, and has
**native actual lengths**

    Nx=(-A,A,0),    Nc=(d-n,n,0),    Ny=(2,-3,1).

These are **not equal** to the research-normalized lengths.
The exact common factor is

    gamma = (B-2)/B
          = B^2-(n+2)B+(n-d)
          = (n-d,-n-2,1).

Since B>n+2>=5, this factor is positive. Direct coefficient
reduction modulo chi yields

    Nx=gamma*Lx,  Nc=gamma*Lc,  Ny=gamma*Ly

**as exact cubic-field identities**.

The new Mojo gate calls the actual constructed `SeedOverlapTables`,
checks their exact characteristic polynomial and literal image
ordering, verifies `gamma>0` at the distinguished Perron embedding,
and requires coefficientwise equality of **all three actual
`tables.lengths`** with the checked native cofactor lengths.
An alternate eigenvector normalization, even if positive and
spectrally proportional, is rejected until a separate scale
certificate is supplied. Merely matching a characteristic
polynomial or the weaker positive-eigenvector uniqueness fact is
not considered enough to equate source representations.

## The second, native-indexed integer displacement lattice

For full bottom-minus-top integer Parikh offset (p,q,r), the
**native** cubic displacement is

    N_(n,d)(p,q,r)
       = ( -A*p+(d-n)*q+2*r,  A*p+n*q-3*r,  r ).

Its coefficient matrix has determinant

    det = -d*A = -d*(n+d) != 0.

Thus the *native* cubic integral lattice of full-Parikh shifts
has index **d(n+d)** in Z^3, not d as in the research scale.

For a native cubic shift (u,v,w), the unique Parikh inverse
exists precisely when **both integer divisibility guards** hold:

    q = (u+v+w)/d               requires d | u+v+w
    p = (v-n*q+3*w)/(n+d)       requires (n+d) | v-n*q+3*w
    r = w.

The native decoder checks both congruences, re-encodes the
result, and refuses all off-lattice shifts. In particular,
native shift zero iff the full three-coordinate Parikh offset
is zero in the standing irreducible class-A cubic. A genuine
typed coincidence additionally requires **top=bottom**.

## Genuine literal occurrence child compatibility

The affine full Parikh action is

    M(p,q,r)=(2p+q+r,q+r,A*p+n*q+(n-1)*r),

and exact cubic multiplication by B satisfies

    N_(n,d)(M z)=B*N_(n,d)(z).

For genuine ordered occurrences (i,j) in the **actual**
parent substitution words, let P_top(i),P_bottom(j) be their
integer proper-prefix counts. Then

    N_(n,d)(Mz+Pbottom(j)-Ptop(i))
       = B*N_(n,d)(z)+N_(n,d)(Pbottom(j)-Ptop(i)).

`verify_native_indexed_child` uses the original native
`selected_overlap_child` to compute that exact cubic child,
validates the parent and child strict Perron overlap, and
independently computes the actual prefix counts and all
three child Parikh coordinates. It compares the full native
`OverlapState` against the exact native-encoded Parikh
target **and decodes it back**. Nonexistent RUN/LAST indices,
wrong types, off-lattice shifts or an incorrect native scale
cause refusal.

## Evidence and acceptance boundary

- Canonical implementation:
  `kernel/psc/class_a_native_length_contract.mojo`
- Native tests:
  `kernel/tests/test_class_a_native_length_contract.mojo`
- Independent Python:
  `reference/psc_research/class_a_native_normalization.py`,
  `tests/test_class_a_native_normalization.py`

**Four independent Python tests passed locally in 0.59s**,
using integer-only polynomial multiplication. They verify
the actual first-two-row cross product, native-versus-research
scale, native sublattice and two congruences, all-parameter
cubic beta intertwining across 117 member specimens,
and every literal ordered occurrence for four named class-A
source types on a 5x5 parameter grid. They also check true
reversal covariance and reject malformed source indices
and off-chamber parameters.

The native tests independently construct real
`build_seed_overlap_tables_screened` tables for small
member parameters, verify the actual native positive
cross-product normalization, test signed Parikh vectors
and actual indexed X->Q->C, Y0->CY, and E6 children.
They explicitly reject a research-scale table
masquerading as the native scale and a changed
literal substitution order. The original submission had no local native
compiler receipt. The acceptance repair now records a locked-Mojo
1.1.0.dev2026090805 compile/run pass: 2,500 signed native-lattice cases,
selected strict children, both congruence refusals, wrong scale/order
refusals, nonexistent/negative occurrence indices and a nonstrict selected
child. Both the parent test and native test reach their post-assertion
contract receipts. Evidence: `evidence/class-a-native-acceptance-2026-10-31/`.
Fresh hosted exact-head acceptance remains required before integration.

The original #438 `S_d` map remains correct for its
specified normalization. This PR makes the change of
normalization explicit rather than silently using
`S_d` as though it were the native shift.
It is a necessary representation interface for
future export of the #435 quotient rank witnesses to
#437's native exact overlap verifier, but it does
**not** itself establish a complete all-k,t carrier,
universal ranks or the seed-to-literature coverage bridge.

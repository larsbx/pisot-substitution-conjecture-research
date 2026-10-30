# Class-C R/T/U: a translated star and its strict-guard obstruction

**Status:** scoped hand proof; independent human review pending. Finite
exact replays support the proof. No completion-ledger claim is promoted.
The [targeted decision](class-c-r-transfer-stopgo-2026-10-30.md) precedes
implementation. This continues the twelve interfaces of PR #406 at
5cdc00b3122ddd55d884ea143ab1a4a05d1e95fc without changing that PR's branch.

## Work shown

### Assumptions and hypotheses

Integers d>=7, plus c=0, n=2d-5, p=3d-5, r=d-4. Use Theorems P_C,
R_C and the preceding plus-boundary interface proofs. Normalize ell_y=1,
a=ell_x, b=ell_c. Put u=1/beta, rho=1/(beta*(beta+1)); then

    beta=d+2rho, 0<u<1/7, 0<rho<u/8,
    a=3+u+2rho, b=2+rho, [I,U,R]=I+U*u+R*rho.

The substitutions are x -> x y^p x, c -> c y^n x, y -> c y^r c.
Displacement is bottom-start minus top-start; strict overlap means
-ell_bottom<w<ell_top. No tile-length independence or return-vector
realization assumption is added.

### Derivation / reduction

#### A further forced step and the complete T star

The preceding X_7=(x,y,-4a+11b-7) has the actual L/F child

    R=(x,c,2a-3b-2)=(x,c,[-2,2,1])

at word indices (p+1,0). Inflation of R gives [-2d+2,1,-5]. The bottom
final x starts at

    [-2d+2,1,-5]+b+n=[-1,1,-4]=V.

Since -1<V=-1+u-4rho<0 and a>3, its end V+a is between zero and a.
The bottom first tile and run end at or before V<0. Thus only the top
first x and bottom final x intersect. The complete star is

    children(R)={T}, T=(x,x,V)=(x,x,a-6b+8),

with the unique actual occurrence pair (0,n+1).

For T, inflation gives S=[-d+1,-4,2]. The bottom first x ends at S+a<0;
the whole bottom word ends before the top final x starts because its end
minus (a+p) is S+a<0. The bottom final x starts at S+a+p>a. These
three inequalities exclude all six absent segment kinds. Exactly F/R,
R/R and R/L remain:

| Kind | Child | Exact run window |
|---|---|---|
| F/R | (x,y,[-d+4+j,-3,4]) | d-4<=j<=d-1 |
| R/R | (y,y,[-d+1+ell,-4,2]) | ell=d-1,d |
| R/L | (y,x,[2d-4-i,-4,2]) | 2d-5<=i<=2d-2 |

For F/R, C=S+a=[-d+4,-3,4]; the strict inequalities are
d-5+3u-4rho<j<d-1+4u-2rho, giving the first window. For R/L,
C=S+p=[2d-4,-4,2]; C-1<i<C+a gives the last window. For R/R,
-S-1<ell<1-S gives d-1,d. All these bounds lie in the actual runs
0..p-1, and for R/R i=0,j=ell is an actual witness.

The distinct set is therefore

    (x,y,[s,-3,4]), s=0..3;
    (y,y,[s,-4,2]), s=0,1;
    (y,x,[s,-4,2]), s=-2..1.

Different rows have different ordered letters; different s differ by a
nonzero integer. Each R/R difference has p-ell occurrence witnesses.
There are exactly ten distinct states, 4+(2p-2d+1)+4=4d-1 occurrence
pairs, and 4d-11 duplicate pairs. This is a complete star, not a subset.

#### An exact translated-star identity

Let kappa=a-b-1=u+rho. Comparison with Q's three strips gives exactly

    children(T)={(A,B,w+kappa):(A,B,w) in children(Q)}.

This is a bijection of complete distinct child sets, preserving letters.
It relates two different parent types and is a reusable local interface
identity. It does not assert that translation commutes with further inflation.

#### Complete U star and a uniform obstruction to recursive translation

The T child U=(x,y,[3,-3,4]) is realized by actual word indices (0,d).
It is X_7 shifted by kappa. Its inflated displacement is
S_U=[3d-3,4,2]. Relative to the top last start f_A=a+p,

    S_U-f_A=-1+3u<0, S_U+b-f_A=1+3u+rho>0.

The bottom starts beyond the top first tile. Its run begins after the top
run ends, and the bottom final starts beyond the whole top word: the last
claim has margin d-6+2u-rho>0. These inequalities leave only L/F,L/R,R/F.

| Kind | Complete child | Actual word-index witness |
|---|---|---|
| L/F | (x,c,[-1,3,0]) | (p+1,0) |
| L/R | (x,y,[1,3,1]) | (p+1,1) |
| L/R | (x,y,[2,3,1]) | (p+1,2) |
| R/F | (y,c,[0,3,0]) | (p,0) |

For L/R, C=S_U+b-f_A=[1,3,1], and -C-1<j<a-C gives precisely
j=0,1 after actual-run clipping. For R/F, C=S_U-a=[3d-6,3,0], and
C-1<i<C+b, clipped to i<=p-1=3d-6, retains only i=3d-6. These
four states are distinct and account for exactly four occurrence pairs.

Now beta*kappa=[1,1,-1]. X_7 has the actual L/R child
Z=(x,y,[2,2,2]) at indices (p+1,3), for every d>=7. Translating that
child by beta*kappa gives F=(x,y,[3,3,1]). But

    F.shift-a=2u-rho>0.

F is not even a strict overlap, hence cannot be a child of U. Therefore

    children(U) != children(X_7)+beta*kappa

throughout the boundary family. At d=7, both independent and native exact
enumeration give six translated labels and four actual children; the dump
records one rejected label. The all-d obstruction is the strict margin
above. This rejects the unguarded recursive extension of the star identity;
it says nothing against a transfer rule that re-clips occurrence windows.

#### Conditional reusable integer transfer

The existing [I,U,R] inflation rule and strict integer endpoint rule have
been factored into `boundary_offset_children`. It accepts all three letter
types, including c's asymmetric first/last letters c/x. For a strict parent
it enumerates the four singleton pairs, four singleton/run pairs and one
run-difference window, using actual word lengths and endpoints.

Its precise conditional contract is: if every sign/endpoint query falls in
|U|<=5, |R|<=10, the returned set is the complete distinct child set.
The integer endpoint proof in the preceding frontier note applies to every
query, and the nine-kind completeness proof applies unchanged. A query
outside that envelope or a checked arithmetic overflow refuses the whole
call; it never returns a truncated set. Hand quantifiers are all d>=7;
the executable still inherits the d=7..64 replay budget. No all-descendant
invariance of this envelope is assumed. The original twelve interfaces
are regression checked with unchanged export digests.
The helper also reproduces all nine canonical seed tables at every replayed
gap (522 interfaces), guarding all three letter types and c's c/x endpoints.

### Evidence and replay

Canonical module/driver: `kernel/psc/class_c_r_transfer.mojo` and
`kernel/class_c_r_transfer.mojo`. The shared helper remains in
`kernel/psc/class_c_boundary_frontier.mojo`. Native exhaustive occurrence
checks, the general exact transfer and the conditional integer transfer
agree at all three sources for every d=7..64: 174 interfaces, 8,468 accepted
pairs, 7,598 duplicates and 870 distinct children counted per interface.

The independent Python oracle imports only the archived integer/Fraction
literal-word implementation. It separately transcribes the closed sets,
enumerates actual pairs, checks all occurrence witnesses and both translation
statements, and compares every canonical parent/child export record.

From kernel/ with the pinned compiler:

    pixi run --locked mojo run -I . tests/test_class_c_r_transfer.mojo
    pixi run --locked mojo run -I . class_c_r_transfer.mojo dump > /tmp/class-c-r-transfer.txt

From repository root:

    python3 oracles/python/check_class_c_r_transfer.py --mojo-dump /tmp/class-c-r-transfer.txt --check-receipt evidence/class-c-r-transfer-2026-10-30/receipt.json

The dedicated workflow regenerates the export, compares the independent
full sets and receipt, checks both predecessor export digests, and uploads
artifacts. Local replay is separate from hosted acceptance.

### Negative controls

Strict tangential parents and queries outside the coefficient envelope
refuse. Invalid signs, c, source indices and letters refuse. The translated
candidate F fails a strict margin for every d and is retained as the failed
stronger rule. Malformed export controls reject missing/duplicate parents
and children, altered coefficients, false summaries and missing/altered
negative-control records. Actual occurrence multiplicity is not a state count.

### Non-claims / remaining gaps

R/T/U are three exact local interfaces and a uniform seed-reachable path,
with one exact translated star and one uniform obstruction to its recursive
extension. The other T children and the U children still need their outgoing
classifications. No forward-closed carrier, all-depth state bound, BH, PDS
or PSC follows. Other cone chambers and the realization/non-unit spectral
bridges keep their existing obligations. Human review remains validation debt.

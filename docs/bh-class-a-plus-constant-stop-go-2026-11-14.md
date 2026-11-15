# Plus-Class-A constant entry: pre-code source and hypothesis gate

Date: November 14, 2026 (America/New_York). Starting source:
`110e7e9ef8243bc24adf80d6e8a375add586d850` (draft PR #579).

## Proposed claim and decision

**Proceed with a narrowed plus-family theorem and original-occurrence
implementation.** The proposed all-source statement is typed coincidence
from every strict integral overlap for the literal ordered words

```text
x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n+1) c,
n >= 6, 5 <= d <= n+4.
```

Keep the plus sign in the incidence matrix, Perron polynomial, every
prefix vector and every geometric test. The minus-family constructor and
its guard are not a plus-family interface. The complete plus PIP domain
is larger: `n>=0,1<=d<=2n+11`. The upper chambers are separate targets.

The hand-derived mechanism to verify is as follows. With `Ly=1`, set
`h=1/beta`, `delta=d/(beta-1)`, `A=2h` and `B=n+4-beta`. In the proposed
chamber, `n+3<beta<n+4`, `Lc=1-h`, `Lx=Lc+delta`, `0<A<1/2`,
`B>0` and `A+B<1`. The original nearest RUN choice produces

```text
z[j+2] = nearest(-A*z[j] + B*z[j+1]),
next full offset = (z[j+1], z[j+1]-2*z[j],
                    z[j+2]-3*z[j+1]+2*z[j]).
```

The negative first coefficient changes the maximum argument: it needs an
absolute bound, not just an upper bound. Prove a finite integer-pair bound,
classify all periodic tails as constants, and derive eventual constancy.
The constant packet is `U_H=(y,y,H,-H,0)`; its exact amplitude condition
is `2d|H|<=n+2`. For positive height the proposed three RUN pairs are

```text
(dH+2,1), (1,n+4-dH), (d(H-1)+3,1).
```

Their proposed full offsets are `(H,-H,-1)`, `(H-1,-H-1,2)` and
`(H-1,-H+1,0)`. Reversing both original indices handles negative height.
Check the actual word ranges and strict intermediate intervals, not only
the algebraic endpoint. Nonzero nearest fixed points are expected and
must not be credited as hits.

For arbitrary-source entry use literal one-level counts. The proposed
weighted center bound uses `K=ceil(Lx)<=3`, with at most K bottom y-centers
inside a top x-tile and at most one in a top c-tile. Even though `Lc<1`,
two distinct y-centers are separated by at least one because their own
tiles have unit length. Verify the density gap and all partial-block
errors explicitly. Decode actual deep occurrences through their original
ancestors, and retain `M^m w=P-Q` after composing all prefixes.

The five small seam members `d=n+4`, `n=1,...,5` may use separate complete
swap-seed certificates. Such certificates retain their seed scope; they
do not prove an all-strict theorem below n=6. Assembly may use the existing
low-gap and seam results only at their authenticated source quantifiers.

## Primary sources inspected before implementation

1. Kirschenhofer and Thuswaldner, *Shift Radix Systems — A Survey*, RIMS
   Kokyuroku Bessatsu B46 (2014), 1–59,
   [publisher PDF](https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B46/pdf/B46_001.pdf),
   introduction and Section 8. Symmetric nearest-integer systems are prior
   art, and their finiteness property is distinct from eventual periodicity.
   Neither nearest rounding nor contraction alone gives a zero hit.
2. Kirschenhofer, Petho, Surer and Thuswaldner, *Finite and periodic orbits
   of shift radix systems*, JTNB 22 (2010), 421–448,
   [author PDF](https://www.math.tugraz.at/~tichy/publications/finitev8.pdf),
   introduction and contractive-orbit discussion. This paper's floor-map
   conclusions are not silently substituted for the present signed nearest
   recurrence. Its explicit coefficient argument is to be proved here.
3. Huszti, Scheicher, Surer and Thuswaldner, *Three-dimensional symmetric
   shift radix systems*,
   [author PDF](https://www.dmg.tuwien.ac.at/nfn/ssrsv10.pdf), Sections 1–2.
   The paper states the symmetric map and recalls Akiyama–Scheicher's exact
   two-dimensional finiteness region. Nonzero fixed cycles outside that
   region are compatible with contractivity. The contribution sought here
   is the literal family specialization and actual alternative exits,
   not a new general numeration-system classification. Direct access to
   Akiyama–Scheicher's author PDF failed; no unread claim from it is used.
4. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   AIF 64 (2014), 1373–1417,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf),
   Sections 2, 4 and 9. Marked prefix automata preserve admissible word
   occurrences, and nonunit representation spaces include finite places.
   This determinant-plus-two construction imports neither inverse
   integrality nor a unit-only spectral implication.
5. Akiyama and Lee, *Algorithm for determining pure pointedness of
   self-affine tilings*, [author source](https://arxiv.org/abs/1003.2898).
   Complete overlap reachability is established methodology. A finite
   exceptional-case certificate must include every required seed and child;
   a selected productive path is not a complete carrier or spectral proof.

The repository's append-only side-notes ledger, the two preceding minus
entry proofs, the Class-A run-index proof, the restored October 30 seam
pins and the plus gap/ray certificates were also read. The existing
plus d=1 recurrent family has unbounded hitting depth as n grows. Retain
that counter-calibration: no parameter-independent depth is proposed.

## Negative controls and acceptance boundary

Reject a minus word or field under a plus binder, changed word order or
prefix caches, incorrect offset signs, nonintegral/out-of-alphabet sources,
noncentral selector inputs, illegal RUN indices, altered full vectors,
nonzero fixed points mistaken for endpoints, and capped/overflowing paths
mistaken for conclusions. Distinguish first integral-zero BH termination
from typed coincidence; mixed-letter zero is not typed coincidence.

Canonical constructors and certificates are Mojo with checked arithmetic.
An independent exact-field oracle must count literal prefixes and replay
the whole original transcript. Symbolic calculations must cover unbounded
parameters and heights. Formal endpoints must expose their exact subset;
written entry, Perron identification and full assembly are not automatically
Lean theorems because an algebraic module compiles.

The fresh-source Lean policy is unchanged. Cached development evidence,
fresh isolated acceptance, exact-head hosted gates and human review remain
distinct. Preserve all failed attempts. No universal BH, arbitrary-ternary
A1-prime, C4, G1, PDS, PSC or all-alphabet claim is promoted by this decision.

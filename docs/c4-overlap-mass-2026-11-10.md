# C4: ordered overlap mass and conservative strict carriers

Date: 2026-11-10. Continuation of
[PR #535](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/535).
The [literature stop/go](c4-overlap-mass-literature-2026-11-10.md) preceded
the new theorem-facing code. No governed claim status is promoted.

## 1. Result and scope

The actual affine occurrence interface now has an exact physical mass
identity. Summing the overlap lengths of **every ordered image digit pair**
gives the common scale times the parent overlap length. Equal child labels
remain separate summands. Boundary contacts contribute zero.

The finite counting interface then supplies two previously explicit
obligations of the [physical-mass refinement](physical-mass-refinement-2026-11-08.md):
grouping occurrences into matrix entries preserves their multiplicity, and
uniform forward/incoming degrees on actual quotient fibers give the correct
weighted transpose correspondence. These are generic formal adapters; they
do not certify a particular serialized graph or its geometric completeness.

The strict-carrier specialization also settles a limitation of this route:
**the complete physical forward matrix of a supplied strict carrier is
conservative.** Its finite interior support retains every positive child,
so `F h = beta h`. A correctly weighted transpose of those same full counts
has zero deficit. The mass-exclusion theorem therefore cannot acquire a
losing vertex from local subdivision and strict closure alone.

| Module | Formal contribution | Hypotheses still supplied |
|---|---|---|
| [`OccurrenceMass`](../proof/PscVerif/PscVerif/OccurrenceMass.lean) | Finite interval subdivision, physical mass/interior equivalence, track-swap mass invariance, exact full digit sum | Nonnegative letter lengths and scale; exact image-length scaling |
| [`OccurrenceMassCounts`](../proof/PscVerif/PscVerif/OccurrenceMassCounts.lean) | Literal row counts, omitted-mass deficit, finite quotient double counting, composition with `PhysicalMass` | A complete finite occurrence inventory; explicit retained family; uniform counts on each quotient fiber |
| [`OccurrenceMassStrict`](../proof/PscVerif/PscVerif/OccurrenceMassStrict.lean) | Actual strict child closure retains all positive mass; full forward conservation; zero weighted transpose deficit | Supplied actual `StrictSystem`, positive letter lengths, nonnegative exact scale; inverse count transport when using the transpose conclusion |

No Pisot, irreducibility, primitivity, legal infinite tiling, compact overlap
set or measure-theoretic hypothesis is needed for finite subdivision. None
of these structures is constructed by the new lemmas. The contribution is
the formal binding to the repository's actual occurrences and sign/index
conventions, not a new general interval-partition theorem.

## 2. Physical coordinates and the subdivision proof

The packet convention from `OccurrenceTransport` is
`p = (a,b,r)`, where `r` is **top prefix minus bottom prefix**. Write
`delta = ell dot r`. After translating the top tile to zero, the two
closed intervals are

\[
[0,\ell_a],\qquad[-\delta,\ell_b-\delta].
\]

Define

\[
L(a,b;c,d)=\max(0,\min(b,d)-\max(a,c)),\qquad
h(p)=L(0,\ell_a;-\delta,\ell_b-\delta).
\]

The elementary proof begins with the clipping identity, for `a <= b` and
`c <= d`,

\[
L(a,b;c,d)=\min(\max(b,c),d)-\min(\max(a,c),d).
\]

Splitting an ordered interval at an intermediate endpoint telescopes this
expression. Applying it along the literal prefixes of a word gives the sum
over all its letter positions. Applying the word partition to both tracks
gives the complete double sum. Nonnegative lengths ensure the endpoints
are ordered; repeated endpoints and empty words are permitted.

For actual positions `i` in `sigma(a)` and `j` in `sigma(b)`, the existing
`markAt` retains the selected letter, prefix and suffix. If their prefix
lengths are `u_i` and `v_j`, the inflated child intervals are

\[
[u_i,u_i+\ell_{a_i}],\qquad
[-\beta\delta+v_j,-\beta\delta+v_j+\ell_{b_j}].
\]

`OccurrenceSuccessor.offset_affine` proves that their relative displacement
is exactly the new packet displacement:

\[
\ell\bigl(Mr+\pi(\sigma(a)_{<i})-\pi(\sigma(b)_{<j})\bigr)
=\beta\delta+u_i-v_j.
\]

Translating both intervals by `-u_i` identifies their intersection length
with `packetMass ell (digitPacket sigma p i j)`. Exact image scaling makes
the two whole image intervals the beta-scaled parent intervals. Since
`beta >= 0`, interval mass scales by beta. Thus the checked theorem
`sum_digitPacket_mass` is

\[
\sum_{i<|\sigma(a)|}\sum_{j<|\sigma(b)|}
h(\operatorname{digitPacket}(p,i,j))=\beta h(p).
\]

This statement applies to any packet, including one with zero parent mass
or no actual balanced-word realization. Separately,
`packetMass_pos_iff_interior` identifies strictly positive mass with the
existing geometric `Packet.Interior` predicate. It needs no positivity
assumption on the length row: existence of a strict common interior point
is itself equivalent to the displayed positive intersection length.

## 3. Occurrences, finite labels and omitted mass

For a finite set `A` of occurrence identities and a target map `t`, define

\[
N_j=\#\{e\in A:t(e)=j\}.
\]

`sum_rowCount` proves `sum_j N_j h_j = sum_(e in A) h_(t(e))`.
The target type can also be infinite if a finite label support is supplied:
`sum_rowCount_on` gives an explicit indicator of support membership, and
`sum_rowCount_on_of_zero_outside` removes that indicator only under a proof
that every omitted label has zero mass. This is the adapter needed for
packets, whose ambient residual coordinates are unbounded.

For a row family, let `A_i` be the complete occurrence inventory and let
`R_i` be an explicitly retained subset. Assuming the complete subdivision
identity, finite disjoint summation gives

\[
\beta h_i-(Fh)_i
=\sum_{e\in A_i\setminus R_i}h_{t_i(e)}.
\]

For nonnegative masses this is a nonnegative deficit. It is strictly
positive exactly when some omitted occurrence has strictly positive mass.
The omitted set is a set of occurrence identities, so two equal targets
can still be independently retained or omitted. The proof does not
authorize an omission in a geometric application. Such authorization must
come from the application's actual domain and decomposition.

## 4. Quotient sizes and the transpose convention

The next adapter takes a finite ordered-state type `Omega`, a finite edge
type `E`, literal source/target maps, and a quotient label map `q`.
Parallel edges have different identities in `E`.

Let `m_i` be the cardinality of the fiber `q^-1(i)`. Suppose the forward
degree into label `j` is the same at every ordered representative of label
`i`, with value `F_ij`. Likewise suppose the incoming degree from label
`j` is uniform at representatives of label `i`, with value `T_ij`.
Count the exact edge block from fiber `j` to fiber `i` first by sources,
then by targets. The resulting theorem is

\[
m_iT_{ij}=m_jF_{ji}.
\]

These uniform-degree hypotheses are explicit. An actual symmetry can
establish them through edge bijections, but merely calling a map a
track-swap quotient does not establish the hypotheses. A label has positive
fiber size exactly when it has an actual representative.

The existing `PhysicalMass.weighted_deficit` theorem, reused without
duplicating its algebra, now yields for `H_i=m_i h_i`,

\[
\beta H_j-(T^{\mathsf T}H)_j
=m_j\bigl(\beta h_j-(Fh)_j\bigr).
\]

Only constant nonzero fiber size permits cancellation to `T_ij=F_ji`.
A mixture of fixed and free orbits does not meet that premise.
For example, take ordered states `a,b,c`, labels `q(a)=q(b)=0`, `q(c)=1`,
and edges `a -> c`, `b -> c`, `c -> c`. Then

\[
m=(2,1),\quad
F=\begin{pmatrix}0&1\\0&1\end{pmatrix},\quad
T=\begin{pmatrix}0&0\\2&1\end{pmatrix}.
\]

For `h=(1,1)` and `beta=1`, the forward row is conservative and
`T^T (2,1) = (2,1)`. Using the unweighted vector instead gives
`T^T (1,1) = (2,1)`, so its purported budget fails at coordinate zero.
This example has a literal edge inventory and uniform degrees; the wrong
conclusion comes solely from dropping the fiber weights.

## 5. Why complete strict support supplies no loss

Let `S = OccurrenceFinite.interiorSupport C ell` for an actual supplied
strict carrier `C`. Define the forward matrix on this finite label set by
counting every pair of actual image positions that has the indicated
target packet. There is no deduplication of equal targets.

If an actual digit packet has positive mass, it is geometrically interior.
`OccurrenceStrict.realized_closed` uses literal child localization to put
that packet back inside the same carrier. It is therefore in `S`.
Contrapositively, every digit label outside `S` has zero mass.

The finite-support grouping theorem now applies to the full double sum,
and `full_forward_conservative` proves, at every `p in S`,

\[
(Fh)_p=\beta h_p,\qquad h_p>0.
\]

Consequently `weighted_deficit_zero` proves zero deficit everywhere for
any inverse matrix with the stated exact weighted correspondence to these
same counts. The theorem does not assert that a proposed geometric inverse
graph has that correspondence. It says that if it does, this complete
forward support cannot supply strict physical loss.

This is consistent with the known strict non-PIP carrier for `1/012/1`,
whose positive row is `(1,2,1)` with scale two. Recurrence, positive mass
and conservative subdivision coexist. No contradiction is available from
these properties alone.

## 6. Controls and verification contract

The canonical native regression is
[`test_c4_overlap_mass.mojo`](../kernel/tests/test_c4_overlap_mass.mojo).
It uses actual occurrence indices and the existing affine/overlap kernels.
The independent bounded specification is
[`C4OverlapMass.qnt`](../proof/quint/C4OverlapMass.qnt), driven by
[`check_c4_overlap_mass_quint.py`](../tools/check_c4_overlap_mass_quint.py).
The runner is provenance/orchestration code, not a Python mathematical
implementation.

The central multiplicity control has `sigma(a)=00`, unit lengths, scale
two, and parent `(0,1,0)`. Its four ordered digit pairs have masses
`[1,0,0,1]`. The positive children have the same packet label, so summing
the full list gives two while summing distinct labels gives one. Removing
a boundary-only occurrence changes no mass; removing one of the positive
occurrences creates exactly one unit of arithmetic deficit.

The wrong positive row `(2,1,1)` for `1/012/1` retains the previous scaling
countercontrol. Its strictly overlapping parent can have zero child mass;
the exact image-scaling equations fail, so the theorem cannot be applied.
Literal mixed-fiber graphs separately check the weighted formula, matrix
orientation, and failure of uniformity when an edge inventory is altered.
The bounded domains are finite tests, not a new Pisot census. The
[control inventory](c4-overlap-mass-controls-2026-11-10.md) records all
sixteen test contracts, nine assertion-failing variants, exact domains and
the native production sweep's opposite displacement convention.

Replay at the exact revision being accepted:

```sh
python tools/make_proof_bank.py --check
./tools/check_lean.sh
python tools/check_c4_overlap_mass_quint.py --output /tmp/c4-overlap-mass-quint
cd kernel
pixi run --locked mojo run -I . tests/test_c4_overlap_mass.mojo
```

The dedicated C4 workflow runs the new native test and a separate Quint
job, recording the published commit/tree and immutable source hashes.
The isolated Lean workflow recompiles the whole bank and audits every
local declaration. Development checks and exact published-revision
receipts are distinguished in the implementation PR. A prior revision's
passing receipt does not cover this extension.

## 7. Remaining C4 work

The interval/counting bridge is now available. The mass route still needs
an actual inverse-domain construction with complete occurrence semantics,
the intended compact overlap sets and nonunit Haar scaling, sufficient
coverage of a putative strict system, and a justified source-loss argument
or a different contradiction. Complete strict support's conservation must
remain visible in that construction.

The independent alternatives remain a coherent family of protected legal
ancestry towers, or an explicit nonzero cut-derived rational row fixed on
one complete three-generation window. Neither finite recurrence nor local
flatness constructs those missing objects. General C4, Concentration,
global G1 and PSC remain open; independent human review remains final
validation debt.

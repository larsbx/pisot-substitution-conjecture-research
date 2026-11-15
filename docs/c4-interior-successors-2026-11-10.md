# C4 interior successors from exact length scaling

**2026-11-10.** The local continuation obligation now has a direct finite-word
proof: every strictly interior packet has a strictly interior successor
selected at actual positions in the two substitution images, provided the
positive length row scales exactly under the substitution. The theorem is
`Psc.OccurrenceSuccessor.interiorStep_exists` in
[`OccurrenceSuccessor.lean`](../proof/PscVerif/PscVerif/OccurrenceSuccessor.lean).

The pre-code decision is recorded in
[`c4-finite-carrier-dual-literature-2026-11-10.md`](c4-finite-carrier-dual-literature-2026-11-10.md).
This note gives the interval argument, its exact hypotheses, and the limits
of composing it with the accepted occurrence lift.

## Exact theorem and interfaces

Let `σ : Fin 3 → Word`, let every letter length `ℓ(a)` be strictly positive,
and let `β > 0`. Assume the three exact equations

\[
  L_\ell(\sigma(a))=\beta\ell(a),
  \qquad
  L_\ell(w)=\sum_i\ell(i)|w|_i.
\]

For a packet `p=(a,b,r)`, use the repository's top-prefix-minus-bottom-prefix
sign convention and set

\[
  d=\ell\cdot r.
\]

Its geometric `Interior` predicate is

\[
  \exists t:\quad 0<t<\ell(a),\qquad 0<t+d<\ell(b).
\]

The theorem concludes that actual marks `dt : Mark (σ(a))` and
`db : Mark (σ(b))` produce a packet

\[
  q=\bigl(dt.letter,db.letter,
       Mr+p(dt.before)-p(db.before)\bigr)
\]

with `q.Interior ℓ`. Consequently `InteriorStep σ ℓ p q` holds by the
existing literal digit-edge definition. The selected prefixes and suffixes
are part of the marks; equal letters or equal packet labels do not identify
their distinct occurrences.

The source packet need not already be realized in a word pair. When it is
realized in an actual marked balanced block, the previously accepted
`OccurrenceTransport.lift_digitStep` supplies the actual child occurrence.
The finite-carrier and strict-system consequences are separate consumers of
this theorem.

| Declaration | Checked mathematical content |
| --- | --- |
| `offset_incidence` | Exact image-length scaling implies `offset ℓ (M *ᵥ r) = β * offset ℓ r` for every integral vector `r`. |
| `offset_add`, `offset_affine` | The displacement of an actual digit pair is the scaled parent displacement plus the two image-prefix lengths with their signs retained. |
| `exists_mark_containing` | A point strictly between a word's endpoints, avoiding all prefix boundaries, lies in the strict interior of an actual selected letter. |
| `exists_between_avoiding` | A finite subset of the real line cannot exhaust a nonempty open interval. |
| `prefixCuts`, `mem_prefixCuts` | The finite boundary set includes every prefix of length between zero and the actual word length. |
| `interiorStep_exists` | The scaled overlap contains a point in both selected image-letter interiors, yielding an actual digit edge and an interior target. |

## Work shown

### Assumptions and hypotheses

The successor theorem uses exactly positive letter lengths, a positive
common scale, the exact scaling equations, and strict interior overlap of
the source packet. It does not require `β > 1`, primitivity, irreducibility,
a Pisot spectrum, legality, a balanced-pair carrier, or a finite graph.
Every image is automatically nonempty: its weighted length is
`βℓ(a) > 0`, whereas the empty word has length zero.

The two offset identities are purely finite algebra and do not need the
positivity hypotheses. The word-point locator also has a broader elementary
statement: it assumes its strict endpoint inequalities and boundary
avoidance directly. The final theorem applies it to positive-length image
words.

`Packet.Interior` refers to strict intersection of physical letter
interiors. The native `TargetPacket.interior` field records a different
combinatorial boundary property; the two interfaces must not be substituted
for one another.

### Derivation / reduction

First, exchange the two finite sums in the incidence action. The scaling
equations identify each column's weighted sum:

\[
\begin{aligned}
  \ell\cdot Mr
    &=\sum_j\left(\sum_i\ell(i)M_{ij}\right)r_j\\
    &=\sum_j\beta\ell(j)r_j
     =\beta(\ell\cdot r).
\end{aligned}
\]

For any two image prefixes `u,v`, add the already established identity
`offset ℓ (residual u v) = Lℓ(u) − Lℓ(v)` to obtain

\[
  \ell\cdot\bigl(Mr+p(u)-p(v)\bigr)
   =\beta d+L_\ell(u)-L_\ell(v).
\]

Second, scale the nonempty source overlap by the positive number `β`.
In coordinates measured from the inflated top letter's left endpoint,
the resulting open interval is

\[
  I=\left(
       \max(0,-\beta d),
       \min(\beta\ell(a),\beta\ell(b)-\beta d)
     \right).
\]

The source interior inequalities and positivity prove that its left
endpoint is strictly less than its right endpoint. Both inflated words
have the required total lengths by exact scaling.

Remove from `I` the following finite set:

\[
 \{L_\ell(\sigma(a)[0:i]):0\le i\le|\sigma(a)|\}
 \;\cup\;
 \{L_\ell(\sigma(b)[0:j])-\beta d:
                         0\le j\le|\sigma(b)|\}.
\]

Choose a remaining point `x`. An induction over the actual word locates it
inside an actual top digit and locates `x+βd` inside an actual bottom digit.
If `u` and `v` are those marks' literal prefixes, the inequalities are

\[
\begin{aligned}
  &0<x-L_\ell(u)<\ell(dt.letter),\\
  &0<x+\beta d-L_\ell(v)<\ell(db.letter).
\end{aligned}
\]

Set `y=x−Lℓ(u)`. The affine identity gives

\[
  y+\ell\cdot q.delta=x+\beta d-L_\ell(v).
\]

These two strict inequalities are precisely the witness for
`q.Interior ℓ`. The marks themselves witness `DigitStep σ p q`.

The boundary-avoidance step matters. A midpoint of the parent overlap can
land on a child cut, and a shared endpoint of two child letters supplies
no strict interior witness. Removing a finite set preserves a point in
the open interval without relaxing either strict inequality.

### Evidence and replay

The implementation imports the accepted occurrence transport module and
uses its literal `Word`, `Mark`, `Packet`, `DigitStep`, `InteriorStep`,
incidence, residual, and physical-length definitions. It introduces no
replacement model, axiom, stub, or hidden declaration.

The deterministic production-module replay, from `proof/PscVerif`, is:

```sh
lake build PscVerif.OccurrenceSuccessor
```

The final integration receipt must also compile the complete Lean bank and
audit the published declaration dependencies. A narrow exact-source check
is used during development to avoid rebuilding unrelated imports; it is
not a replacement for that production replay.

The narrow check passed on 2026-11-10: the exact new module body compiled
after the accepted transport definitions and proofs, without replacement
declarations or new axioms. The only diagnostics were two pre-existing
unused-section-variable warnings in the earlier newborn core.

The production command also passed on 2026-11-10, with the target built in
324 seconds and the complete invocation reporting 8,919 completed jobs.
It emitted no new-module diagnostics; the same two accepted newborn
warnings were replayed. This receipt uses the actual production imports
and is separate from the subsequent complete-bank and axiom-audit gate.

The canonical native controls for this PR use the existing occurrence and
packet kernels. Their acceptance records and the independent bounded model
receipts belong to the integrating PR; no numerical approximation enters
the Lean proof.

### Negative controls

**A positive row without exact scaling is insufficient.** Use the existing
strict fixture

\[
  \sigma=1/012/1,\qquad U=01/10,
  \qquad (i_{\rm top},i_{\rm bottom})=(0,1).
\]

Both selected source letters are `0`. With the wrong positive row
`ℓ=(2,1,1)`, their actual intervals are `[0,2]` and `[1,3]`, so the packet
has strict interior overlap. Its residual is `r=(0,−1,0)` and its physical
offset is `−1`.

Both selected image words are the singleton `1`, hence only one digit
pair is available. The inflated actual pair is `1012/0121`; its selected
letters occupy `[0,1]` and `[4,5]`. Algebraically,

\[
  Mr=(-1,-1,-1),\qquad \ell\cdot Mr=-4,
\]

while both target letters have length one. The only digit successor has
no interior overlap. This example satisfies positivity and nonerasure;
the missing hypothesis is a common exact scaling row.

The correct row for that substitution is `ℓ=(1,2,1)` with `β=2`.
Selecting the first source occurrence on each side of `01/10`, and then
the first digit on each side, gives the actual ordinal-zero cycle

\[
  01/10\longleftrightarrow10/01,
  \qquad (0,1,0)\longleftrightarrow(1,0,0).
\]

It retains strict physical overlap and has no diagonal packet along the
chosen route. Thus seriality and finite recurrence do not imply that
every path terminates. This fixture is outside the standing irreducible
Pisot regime and does not refute the C4 existential productive-route
target.

Boundary contact must remain excluded by the strict inequalities, and
erased-image examples must fail the positive exact-scaling premises.
Repeated equal letters retain their individual occurrence marks even when
the finite packet support later identifies their labels.

### Non-claims / remaining gaps

The theorem proves existence of a next interior digit choice. It proves
neither a productive choice nor termination of every continuation. Even
after actual occurrence lifting and finite strict-carrier closure yield a
recurrent obstruction, a contradiction still needs a theorem that supplies
a productive route under the full C4 hypotheses.

A repeated packet or hierarchy state does not identify the top and bottom
legal contexts, construct a common legal limit, or satisfy a recognizable
same-point hypothesis. Those extraction obligations remain distinct.

No weighted overlap-mass partition is proved here. A sum over ordered
digit occurrences retains multiplicity and would naturally give a forward
refinement identity. Transporting it to the transpose budget used by
`PhysicalMass.lean` requires a separately explicit orientation binding.
The finite support and existential successor statements do not supply that
identity.

## Primary-source boundaries and novelty

The stop/go review inspected the following primary sources before code.

- Akiyama–Lee, [*Algorithm for determining pure pointedness of self-affine
  tilings*](https://arxiv.org/html/1003.2898v1), §2.5 and §4, especially
  equations (4.1)–(4.2). Their real overlaps use intersecting interiors and
  refine through actual image digit pairs. This is the closest standard
  geometric construction. Ordered digit multiplicities matter in its
  weighted version. Its global spectral criterion retains the tiling and
  Meyer return-set hypotheses; finite balanced-pair closure alone does not
  supply them.
- Berthé–Steiner–Thuswaldner–Yassawi, [*Recognizability for sequences of
  morphisms*](https://www.irif.fr/~steiner/recognizability.pdf), Definition
  2.1 and §3. Recognizability concerns uniqueness of centered
  representations of the same point. Incidence rank hypotheses can give
  recognizability for aperiodic points, but they do not identify two
  distinct configurations constructed from separate balanced-pair
  contexts. The successor proof uses no recognizability theorem.
- Durand, [*A characterization of substitutive sequences using return
  words*](https://arxiv.org/pdf/0807.3322), §2.3 and Proposition 6. The code
  property uses boundaries given by successive occurrences of one common
  prefix in a single sequence. Arbitrary balanced component words have
  not been shown to have that property. Two intertwining substitution
  morphisms alone do not supply the required return-word decomposition.

The interval subdivision, finite avoidance, and incidence duality are
standard. The contribution here is their checked specialization to the
repository's signed packet convention and literal actual-digit witnesses,
ready to compose with its occurrence-address lift. No new general overlap,
recognizability, or return-word theorem is claimed. Uniform productive
crossing, C4, global G1, Concentration, and PSC remain open.

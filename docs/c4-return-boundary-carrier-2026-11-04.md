# Exact return-boundary carrier and a two-phase residual controller

Date: 2026-11-04. Source lease: PR #487 at
`2a8799e93b845475e84abe16386b02a89ca6c212`.

Scope: a written, exact construction for the **single productive Pisot
specimen** sigma=(01,121,012) and its genuine return substitution from #487.
The 28 local states are finite; the emitted word registers and the two-track
Parikh difference are not asserted finite. Neither C4 nor PSC is promoted.
Native Mojo acceptance remains pending until an exact-head run succeeds.

## Literature stop/go

The proposed experiment is to retain the interior position in a return word
rather than discard it when a physical prefix ends away from a return seam.
Durand's return-word coding supplies the genuine morphism intertwining
sigma h = h tau [1, Section 2.3 and the return-substitution construction].
The closest algorithmic construction is the substitution addressing automaton:
one edge for **each** child-letter occurrence, with prefix labels/weights,
as used in Dumont-Thomas numeration [2, Section 2, equations defining the
addressing automaton]. These are established constructions, not novelty claims.

What transfers is exact word substitution, ordered prefix decomposition and
finite occurrence labels. What does not transfer automatically is a finite
state space for comparing two arbitrary prefixes, or universal productivity.
In particular #487's prefix-free derived images cannot be turned into literal
prefix satellites merely by taking a power.

Decision: proceed with the narrowed **explicit occurrence refinement and
residual register identities**, with an adversarial test against dropping
the two-track prefix difference. Do not call this a new general numeration
or return-substitution theorem.

[1] F. Durand, *A characterization of substitutive sequences using return
words*, Discrete Mathematics 179 (1998), 89-101; author preprint
https://arxiv.org/abs/0807.3322 .
[2] O. Carton, J.-M. Couvreur, M. Delacourt, N. Ollinger, *Addition in
Dumont-Thomas Numeration Systems in Theory and Practice* (2024), Section 2,
https://arxiv.org/html/2406.09868v1 . No addability theorem is imported here.

## Exact inputs and conventions

All indices are zero-based. A cut (j,d) is immediately **before** physical
letter r_j[d], so 0 <= d < |r_j|. Terminal cuts are excluded because they
have no next letter; an interior seam belongs to the return word on its right.

```
sigma = (01,121,012)
r0 = 01121121       r1 = 012121121
r2 = 012121         r3 = 01121
h(j) = rj
tau = (012,3212,322,02)
```

The parent note proves this is the complete genuine zero-return coding.
The new executable reuses the parent's literal return-image reconstruction;
it does not replace it with a new guessed return list.

## Complete local cut refinement

There are exactly 8+9+6+5 = **28** local states (j,d).
For x=r_j[d] and **each** t=0,...,|sigma(x)|-1, form the actual prefix

```
w = sigma(r_j[:d]) sigma(x)[:t].
```

In the fixed ordered factorization sigma(r_j)=h(tau(j)), locate the unique
return occurrence k and local offset e for which

```
w = h(q) r_c[:e],
q = tau(j)[:k], c = tau(j)[k], 0 <= e < |r_c|.
```

The edge records source (j,d), the child index t, occurrence k, output q,
and target (c,e). This is an **occurrence** record: equal return symbols at
different k must not be collapsed. The next physical letters agree:

```
sigma(r_j[d])[t] = r_c[e].
```

Existence and uniqueness follow from the strictly positive lengths of the
ordered return-word blocks. In particular t=0 transports the old cut;
t>0 records all additional child-letter positions. Enumerating t for all
28 states gives **80 occurrence edges**, not merely 28 inherited edges.
Every physical position in each sigma(r_j) occurs exactly once.

For a complete exterior return prefix U the lifted update is

```
(U,j,d) --t--> (tau(U) q,c,e).
```

Indeed applying sigma to h(U)r_j[:d], then appending sigma(x)[:t], equals
h(tau(U)q)r_c[:e]. This proves the update for arbitrary U and every depth
by induction, independently of a bounded replay.

Equivalently let H(j) list (j,0),...,(j,|r_j|-1). The 28-letter decorated
substitution Lambda maps (j,d) to its ordered target states over all t.
Then the following are **literal word identities**:

```
Lambda H = H tau,
pi Lambda = sigma pi,       pi(j,d)=r_j[d].
```

Thus the carrier keeps every one-step occurrence in the supplied return
coding. It does not assert that an arbitrary C4 overlap lies in this coding.

## The inherited submap is not a synchronization theorem

The complete 28-row t=0 map has three fixed states, (0,0), (1,6), (2,3).
Every state enters one of them within three iterations; their basin sizes
are respectively 12,8,8. These are exact finite-table assertions replayed
independently. The fixed states (1,6) and (2,3) are **interior** cuts.
A finite recurrent local state is therefore not evidence of seam alignment.

The two relevant unmatched boundaries satisfy

```
(0,5) --q=0,k=1,t=0--> (1,6)
(1,6) --q=32,k=2,t=0--> (1,6).
```

For each source above, t=1 and t=2 go to (1,7) and (1,8), respectively,
with the same q and k. These children are retained, not inferred from t=0.

## Exact two-phase residual controller

Write B=121. The parent identities r0=r3 B and r1=r2 B give the initial
physical prefix comparisons. More information is available at the return
code level than a growing unstructured suffix.

For the pair (0,3), initialize Q_0=V_0=empty and phase A. One step uses

```
Q_1 = 0,      V_1 = 2,       phase A -> phase B.
```

In phase B every further step is

```
Q_{n+1} = tau(Q_n) 32,
V_{n+1} = 2 tau(V_n).
```

For all n>=1 this gives **exact entire return-code words**

```
tau^n(0) = Q_n 1 V_n,
tau^n(3) = Q_n 2.
```

For the pair (1,2), initialize in phase B with Q_0=V_0=empty. The same
update gives tau^n(1)=Q_n 1 V_n and tau^n(2)=Q_n 2 for every n>=0.

Proof: tau(0)=0 1 2, tau(3)=0 2 supply the transient; tau(1)=32 1 2
and tau(2)=32 2 supply the recurrent step. Substitute the displayed
factorizations and concatenate. No bounded experiment is used in this proof.
The first differing symbols stay 1 versus 2, so Q is the actual longest
common return-code prefix in phase B, not an arbitrary proposed alignment.

For both initial pairs

```
V_n = 2 tau(2) ... tau^(n-1)(2),
sigma^(n+1)(1) = B h(V_n),
```

with V_0 empty. The last identity follows from sigma(B)=B h(2) and
sigma h=h tau. The unbounded suffix is therefore represented by finite
update rules and word registers, not by finitely many possible raw words.
The phase controller has two states; its **full register configuration
space is infinite**. This distinction is essential.

## What must remain in a two-track state

Let delta be the Parikh difference of the **complete physical prefixes**
of two addressed tracks, with next letters x,y. On child occurrences t,u,

```
delta' = M delta + Parikh(sigma(x)[:t]) - Parikh(sigma(y)[:u]).
```

This follows directly by applying sigma to both prefixes. The return-cut
updates above preserve the exact prefixes, so they preserve this equation.
A balanced cut is delta=0; a strong coincidence additionally requires
x=y. Equality of local return-offset states alone is insufficient.

Explicit negative control: take identical local state (1,6) on both tracks,
but exterior return prefixes empty and 0. The next physical letters agree,
yet delta=-Parikh(r0)=(-1,-5,-2), not zero. Repeated inherited updates keep
the same local pair and multiply delta by M. This defeats a proposed
28-by-28 local-state-only coincidence test.

No bound on the reachable delta register for arbitrary strict C4 sources
has been proved. Nor has the missing occurrence-compatible productivity
argument for all legal two-track children been supplied. Those, not the
single-track return-cut recoding, remain the substantive C4 obligations.

## Replay and acceptance

Canonical code: `kernel/psc/c4_return_boundary_carrier.mojo`.
Native regression: `kernel/tests/test_c4_return_boundary_carrier.mojo`.
Independent oracle: `tests/test_c4_return_boundary_carrier_oracle.py`.
The oracle reconstructs return words from actual source words, locates
child positions by flattened word offsets, exhausts every address through
depth four, and checks all 80-by-80 pairs of one-step defect updates.
Native materialization is capped at depth six before expansion; the finite
80-edge carrier has no search/exhaustion inference.

```
python -m pytest -q tests/test_c4_return_boundary_carrier_oracle.py
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_return_boundary_carrier.mojo)
python tools/make_proof_bank.py --check
```

Written exact identities, finite Python results, native Mojo execution,
source governance, hosted exact-head CI and independent human review are
separate evidence layers. Native/hosted acceptance is not asserted here. Local independent Python replay
passed all nine tests, covering 2,796 descendant occurrence addresses through
depth four and 6,400 one-step two-track defect updates. An initial hard-coded
address-count expectation of 2,800 was corrected to the independently summed
exact count 2,796; the word-level checks themselves did not fail.
No generated Proof Bank source heading or governed claim status is edited.

## Dated side finding and integration record

2026-11-04: the growing return mismatch in #487 has an exact two-phase
word-register recursion and an occurrence-complete 28-state/80-edge local
carrier. Two interior fixed cuts and an explicit nonzero two-track defect
show why neither construction is a finite C4 productivity proof. This
note and the #461 comment preserve the result; append its locator to the
central side-notes ledger during integration (not yet performed here).

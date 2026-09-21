# P1b adelic prefix-difference target

**Status:** exact specification for issue #139. This note defines the target
predicate left open by the literature gate. It does **not** prove that the
target is ever hit, prove overlap coincidence, or authorize a finite search as
a completeness argument.

Dependencies:

- `p1b-strict-zipper-literature-gate-2026-09-21.md`;
- manuscript Proposition 5.44(iii)(b) and Lemma 5.45;
- Minervino–Thuswaldner's non-unit representation-space construction.

## 1. Algebraic carrier

Let (sigma) be a primitive irreducible Pisot substitution with incidence
matrix (M), Perron root (eta), alphabet (A), and number field
(K=mathbb Q(eta)). Let (L_sigma) be the exact (M)-stable
(mathbb Z)-module used by the repository's offset coordinates. Before an
implementation may claim equivalence with the graph predicate, it must provide
an explicit injective intertwiner
[
 lambda:L_sigmalongrightarrow K,qquad
 lambda(Mz)=etalambda(z).                         	ag{1}
]

This is a required binding, not a new assumption. Irreducibility supplies the
rational cyclic representation; the implementation must record the chosen
basis and verify (1) exactly.

Let (S_eta) contain:

1. every non-dominant Archimedean place of (K); and
2. every finite place whose prime ideal divides the principal ideal
   ((eta)).

Define the full contracting representation space
[
 K_sigma=prod_{mathfrak pin S_eta}K_{mathfrak p}
]
and the diagonal internal embedding
[
 Phi'_sigma:Klongrightarrow K_sigma.
]
Write (B) for componentwise multiplication by (eta). At every selected
place, (B) is contracting. Multiplication by (eta) remains invertible in
the ambient local fields even though (M^{-1}) need not preserve
(mathbb Z^A).

**Firewall.** When (|det M|>1), omitting the finite places is a change of
predicate unless their irrelevance is separately proved. No Euclidean
projection may be called the full representation.

## 2. Occurrence-labelled prefix differences

For a letter (a), define the occurrence-labelled proper-prefix set
[
 widetilde P_m(a)=
 {(u,k):sigma^m(a)=u,k,v	ext{ for some word }v}.
]
Repeated occurrences with the same Parikh vector remain distinct records.
Their Parikh projection is
[
 P_m(a)={pi(u):(u,k)inwidetilde P_m(a)}.
]

For an ordered pair ((i,j)), define
[
 widetilde D_m(i,j)=
 {((u,k),(v,ell),,pi(u)-pi(v)):
       (u,k)inwidetilde P_m(i), (v,ell)inwidetilde P_m(j)},
]
and (D_m(i,j)=P_m(i)-P_m(j)).

The occurrence-labelled set is authoritative for replay. The unlabelled set
is sufficient only for the equality predicate. Deduplicating equal Parikh
differences must not erase the witness occurrences.

## 3. Level targets

For (mge0), define the exact level-(m) adelic target
[
 mathcal C_m(i,j)
 =B^{-m}Phi'_sigma(lambda(D_m(i,j)))
 subset K_sigma.                                    	ag{2}
]

Equivalently, (xinmathcal C_m(i,j)) exactly when
[
 B^m x=Phi'_sigma(lambda(d))
 quad	ext{for some }din D_m(i,j).                  	ag{3}
]

For an offset (win L_sigma), injectivity of the diagonal field embedding
and (1) give
[
 Phi'_sigma(lambda(w))inmathcal C_m(i,j)
 iff M^m win D_m(i,j).                              	ag{4}
]

Equation (4) is the acceptance bridge. A future implementation must test the
right-hand side by exact integer equality and may use the left-hand side only
as a structured representation or theorem interface. Floating or truncated
local coordinates never decide acceptance.

Define the cumulative target
[
 mathcal C_{le n}(i,j)=igcup_{m=0}^{n}mathcal C_m(i,j),
 qquad
 mathcal C_infty(i,j)=igcup_{mge0}mathcal C_m(i,j). 	ag{5}
]

The closure of (mathcal C_infty) may be related to differences of Rauzy
subtiles. Membership in the closure, positive measure, or membership almost
everywhere is not membership in (mathcal C_infty).

## 4. Realized strict-zipper orbit

A replayable strict-zipper record contains:

- substitution images and the exact incidence matrix;
- the realized ordered-overlap vertex ((i,j,w));
- an occurrence-labelled closed path of length (r);
- digits (d_0,ldots,d_{r-1}) derived from the two ordered child prefixes;
- the exact cycle identity
  [
   (I-M^r)w=sum_{k=0}^{r-1}M^{r-1-k}d_k;
  ]
- the legality/realization provenance tying every edge to the seed-patch
  overlap graph;
- the assertion that the component is child-closed and contains no
  offset-zero vertex.

Its internal periodic orbit is
[
 mathcal O(w,r)=
 {Phi'_sigma(lambda(M^t w)):0le t<r}.            	ag{6}
]
The cycle identity makes this orbit describable by a purely periodic digit
address. It does not imply a target hit.

## 5. Exact residual theorem

### AdelicPeriodicOffsetHitting

For every substitution in the standing PIP regime satisfying the separately
named P1a dependency, and every realized child-closed recurrent strict-zipper
component (S), there exist a vertex ((i,j,w)in S) and (mge0) such that
[
 Phi'_sigma(lambda(w))inmathcal C_m(i,j).         	ag{7}
]
By (4), this is exactly
[
 M^m win P_m(i)-P_m(j),
]
hence an actual prefix-boundary hit.

The theorem must be uniform in the chosen component. Acceptable closure forms
are:

- a substitution-dependent bound (mle H(sigma)) derived from declared
  exact data and independent of (S);
- a Noetherian/compactness/recurrence argument yielding existence without an
  enumerated cap;
- a finite quotient theorem whose completeness map back to (7) is proved.

A cap, corpus maximum, collar depth, contracting lower bound, or residual
spectral-radius equality is not a closure form.

## 6. Smallest next lemma

The next proof target is deliberately weaker than the whole theorem but must
already be complete.

### Periodic-orbit cylinder recurrence (open)

For the finite set of realized periodic offset orbits of a child-closed
strict-zipper component (S), prove that at least one orbit point belongs to
the exact union of compatible occurrence-labelled targets:
[
 igcup_{(i,j,w)in S};
 igcup_{mge0}
 left(
   {Phi'_sigma(lambda(w))}
   capmathcal C_m(i,j)
 ight)
earnothing.                               	ag{8}
]

“Compatible” means that the prefix occurrences in
(widetilde D_m(i,j)) replay to the same ordered overlap convention used by
the graph. A proof for the larger untyped difference of all Rauzy subtiles is
insufficient unless it proves this compatibility refinement.

## 7. Negative controls

Every proposed recurrence lemma must be checked against:

1. the determinant-two six-edge zero-shift-free affine pump, which is
   productive and therefore refutes bare cycle exclusion;
2. the proper-power/nonseparating collar specimen, which refutes universal
   bounded-context ancestry recovery;
3. a unimodular specimen, to ensure the adelic definition specializes to the
   Archimedean one without making unimodularity an assumption;
4. a non-unit specimen with a nontrivial finite-place coordinate, to ensure an
   Archimedean collision is not accepted as equality in (K_sigma).

These controls falsify overstrong lemmas; passing them does not prove
AdelicPeriodicOffsetHitting.

## 8. Implementation gate

No new theorem-facing search is authorized until the following exact bindings
are reviewable:

- a basis and exact (lambda) satisfying (1);
- the prime ideals/valuations defining (S_eta);
- occurrence-labelled generation of (widetilde D_m(i,j));
- an exact replay certificate for (4);
- explicit capped-versus-proved result types.

The canonical implementation belongs in Mojo. Python or Julia may independently
check small fixtures, but neither is the source of truth. Local-field displays
may use approximations for diagnostics only; certificate acceptance remains
integer/algebraic and fail-closed.

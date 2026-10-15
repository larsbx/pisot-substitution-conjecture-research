# P1b adelic prefix-difference target

**Status:** exact specification for issue #139. This note defines the target predicate left open by the literature gate. It does **not** prove that the target is ever hit, prove overlap coincidence, or authorize a finite search as a completeness argument.

Dependencies:

- \`p1b-strict-zipper-literature-gate-2026-09-21.md\`;
- manuscript Proposition 5.44(iii)(b) and Lemma 5.45;
- Minervino–Thuswaldner's non-unit representation-space construction.

## 1. Algebraic carrier

Let \(\sigma\) be a primitive irreducible Pisot substitution with incidence matrix \(M\), Perron root \(\beta\), alphabet \(A\), and number field \(K=\mathbb Q(\beta)\). Let \(L_\sigma\) be the exact \(M\)-stable \(\mathbb Z\)-module used by the repository's offset coordinates. Before an implementation may claim equivalence with the graph predicate, it must provide an explicit injective intertwiner
\[
 \lambda:L_\sigma\longrightarrow K,\qquad
 \lambda(Mz)=\beta\lambda(z). \tag{1}
\]

This is a required binding, not a new assumption. Irreducibility supplies the rational cyclic representation; the implementation must record the chosen basis and verify (1) exactly.

Let \(S_\beta\) contain:

1. every non-dominant Archimedean place of \(K\); and
2. every finite place whose prime ideal divides the principal ideal \((\beta)\).

Define the full contracting representation space
\[
 K_\sigma=\prod_{\mathfrak p\in S_\beta}K_{\mathfrak p}
\]
and the diagonal internal embedding
\[
 \Phi'_\sigma:K\longrightarrow K_\sigma.
\]
Write \(B\) for componentwise multiplication by \(\beta\). At every selected place, \(B\) is contracting. Multiplication by \(\beta\) remains invertible in the ambient local fields even though \(M^{-1}\) need not preserve \(\mathbb Z^A\).

**Firewall.** When \(|\det M|>1\), omitting the finite places is a change of predicate unless their irrelevance is separately proved. No Euclidean projection may be called the full representation.

## 2. Occurrence-labelled prefix differences

For a letter \(a\), define the occurrence-labelled proper-prefix set
\[
 \widetilde P_m(a)=
 \{(u,k):\sigma^m(a)=u\,b_k\,v\text{ for some word }v\}.
\]
Repeated occurrences with the same Parikh vector remain distinct records. Their Parikh projection is
\[
 P_m(a)=\{\pi(u):(u,k)\in\widetilde P_m(a)\}.
\]

For an ordered pair \((i,j)\), define
\[
 \widetilde D_m(i,j)=
 \{((u,k),(v,\ell),\pi(u)-\pi(v)):
       (u,k)\in\widetilde P_m(i),\ (v,\ell)\in\widetilde P_m(j)\},
\]
and \(D_m(i,j)=P_m(i)-P_m(j)\).

The occurrence-labelled set is authoritative for replay. The unlabelled set is sufficient only for the equality predicate. Deduplicating equal Parikh differences must not erase the witness occurrences.

## 3. Level targets

For \(m\ge0\), define the exact level-\(m\) adelic target
\[
 \mathcal C_m(i,j)
 =B^{-m}\Phi'_\sigma(\lambda(D_m(i,j)))
 \subset K_\sigma. \tag{2}
\]

Equivalently, \(x\in\mathcal C_m(i,j)\) exactly when
\[
 B^m x=\Phi'_\sigma(\lambda(d))
 \quad\text{for some }d\in D_m(i,j). \tag{3}
\]

For an offset \(w\in L_\sigma\), injectivity of the diagonal field embedding and (1) give
\[
 \Phi'_\sigma(\lambda(w))\in\mathcal C_m(i,j)
 \iff M^m w\in D_m(i,j). \tag{4}
\]

Equation (4) is the acceptance bridge. A future implementation must test the right-hand side by exact integer equality and may use the left-hand side only as a structured representation or theorem interface. Floating or truncated local coordinates never decide acceptance.

Define
\[
 \mathcal C_{\le n}(i,j)=\bigcup_{m=0}^{n}\mathcal C_m(i,j),
 \qquad
 \mathcal C_\infty(i,j)=\bigcup_{m\ge0}\mathcal C_m(i,j). \tag{5}
\]
Membership in the closure of \(\mathcal C_\infty\), positive measure, or almost-everywhere membership is not membership in \(\mathcal C_\infty\).

## 4. Realized strict-zipper affine orbit

A replayable strict-zipper cycle record contains:

- substitution images and the exact incidence matrix;
- a realized ordered-overlap vertex \((i_0,j_0,w_0)\);
- an occurrence-labelled closed path of length \(r\);
- edge digits \(d_0,\ldots,d_{r-1}\) derived from the two ordered child prefixes;
- replayed vertices \((i_t,j_t,w_t)\) satisfying
  \[
   w_{t+1}=Mw_t+d_t\quad(0\le t<r), \tag{6}
  \]
  with indices modulo \(r\);
- the exact affine cycle identity
  \[
   (I-M^r)w_0=\sum_{k=0}^{r-1}M^{r-1-k}d_k; \tag{7}
  \]
- legality/realization provenance tying every edge to the seed-patch overlap graph;
- child-closure and absence of an offset-zero vertex.

For \(0\le t\le r\), let
\[
 q_0=0,\qquad
 q_t=\sum_{k=0}^{t-1}M^{t-1-k}d_k,
 \qquad
 w_t=M^t w_0+q_t. \tag{8}
\]
Equation (7) says \(w_r=w_0\); it does **not** say \(M^r w_0=w_0\). The exact realized internal periodic orbit is therefore
\[
 \mathcal O_{\mathrm{aff}}=
 \{\Phi'_\sigma(\lambda(w_t)):0\le t<r\}. \tag{9}
\]
Using \(\{\Phi'_\sigma(\lambda(M^t w_0))\}\) would drop the forcing digits and generally test points that are not overlap vertices.

## 5. Exact residual theorem

### AdelicPeriodicOffsetHitting

For every substitution in the standing PIP regime satisfying the separately named P1a dependency, and every realized child-closed recurrent strict-zipper component \(S\), there exist a realized vertex \((i,j,w)\in S\) and \(m\ge0\) such that
\[
 \Phi'_\sigma(\lambda(w))\in\mathcal C_m(i,j). \tag{10}
\]
By (4), this is exactly
\[
 M^m w\in P_m(i)-P_m(j),
\]
hence an actual prefix-boundary hit.

The theorem must be uniform in the chosen component. Acceptable closure forms are:

- a substitution-dependent bound \(m\le H(\sigma)\) derived from declared exact data and independent of \(S\);
- a Noetherian/compactness/recurrence argument yielding existence without an enumerated cap;
- a finite quotient theorem whose completeness map back to (10) is proved.

A cap, corpus maximum, collar depth, contracting lower bound, or residual spectral-radius equality is not a closure form.

## 6. Smallest next lemma

### Affine periodic-orbit cylinder recurrence (open)

For the finite set of realized affine periodic orbits of a child-closed strict-zipper component \(S\), prove that at least one replayed orbit point hits an occurrence-compatible level target:
\[
 \bigcup_{(i_t,j_t,w_t)\in S}
 \ \bigcup_{m\ge0}
 \left(
   \{\Phi'_\sigma(\lambda(w_t))\}
   \cap\mathcal C_m(i_t,j_t)
 \right)
 \ne\varnothing. \tag{11}
\]

“Occurrence-compatible” means that the prefix occurrences in \(\widetilde D_m(i_t,j_t)\) replay with the same ordered-overlap convention used by the graph. A proof for the larger untyped difference of all Rauzy subtiles is insufficient unless it proves this compatibility refinement.

This lemma is deliberately smaller than the whole theorem but must already be complete. Its inputs are the affine replay data (6)–(9), not the homogeneous powers \(M^t w_0\).

## 7. Negative controls

Every proposed recurrence lemma must be checked against:

1. the determinant-two six-edge zero-shift-free affine pump, which is productive and refutes bare cycle exclusion;
2. the proper-power/nonseparating collar specimen, which refutes universal bounded-context ancestry recovery;
3. a unimodular specimen, to ensure the adelic definition specializes to the Archimedean one without making unimodularity an assumption;
4. a non-unit specimen with a nontrivial finite-place coordinate, to ensure an Archimedean collision is not accepted as equality in \(K_\sigma\).

5. a synchronized SFT exact-diagonal but non-divisible **source address** (distinct from a realized overlap): \(\sigma(a)=aaab,\ \sigma(b)=ab\) has \(M=\left(\begin{smallmatrix}3&1\\1&1\end{smallmatrix}\right)\), \(\det M=2\). Two legal addresses equal to \((a:\emptyset)^\infty\), except that one uses \((a:a)\) at level \(d-1\), have exact full-adelic translation \(W_t=M^{d-1}e_a\) for every synchronized depth \(t\ge d\), but \(W_t\notin M^t\mathbb Z^2\). Do not transfer source polynomial cancellation to the repository's \(M^t w_{\mathrm{PSC}}\)-hitting predicate without an *exact* lattice/congruence and occurrence-realization bridge. See the existing Nakaishi source audit under "Exact reverse-address affine transport and a non-unit obstruction".

6. a seed-patch-realized stationary nonzero overlap (stronger negative control than 5): for the same \(\sigma(a)=aaab,\ \sigma(b)=ab\), \(S=(a,a,e_b)\) is an actual interior overlap of the swapped patches \(ab/ba\), since the positive Perron lengths are \((1,\sqrt2-1)\). The ordered second-\(a\) / first-\(a\) child edge satisfies \(S\to S\) with \(Me_b-e_a=e_b\). For every \(r\ge1\) the repeated path has prefix difference \(W_r=(M^r-I)e_b\notin M^r\mathbb Z^2\); \(e_b\notin M\mathbb Z^2\) by parity. Nonetheless **\(S\) is productive**, via the exact ordered two-step path \(S\to (a,a,-e_a+e_b)\to(a,a,0)\), using top/bottom prefix indices \((2,0)\) and \((0,2)\). Thus an **individual realized recurrent path**, even with exact affine periodicity, does not force the divisibility or synchronized-cylinder witness. Do not substitute it for the quantified **child-closed bad-SCC** hypothesis of #139. Evidence is in the Nakaishi audit §"Realized overlap loop: geometric realization is not sufficient".

7. **Infinite ternary PIP good-edge calibration (positive and negative, no universal claim):** for every \(k\ge3,\ 2\le h\le k\), \(\sigma(a)=a^kbc^h,\ \sigma(b)=ab,\ \sigma(c)=a\) has irreducible Pisot cubic \(X^3-(k+1)X^2+(k-1-h)X+h\), \(\det M=-h\), and a genuine swap-seed interior overlap \(S=(a,a,e_b)\). The labelled top-second-\(a\)/bottom-first-\(a\) edge is a nonzero stationary loop; its prefix gain \(W_t=(M^t-I)e_b\) is **not** in \(M^t\mathbb Z^3\) for any \(t\ge2\). Nevertheless a **different labelled child** (top first \(c\), bottom last \(a\)) gives \((c,a,0)\) in one step and \((a,a,0)\) in two steps, uniformly in both parameters. A nonresolving periodic itinerary is thus compatible with immediate **half-coincidence** and rapid full coincidence from the *same* reachable vertex. Use the complete occurrence-labelled outgoing relation, not an arbitrary recurrent path or an incomplete zero-class residue test. The complete symbolic proof is in the Nakaishi audit section "Infinite ternary non-unit Pisot family: an explicit all-child escape". This does **not** certify all seed vertices or a closed bad SCC.

These controls falsify overstrong lemmas; passing them does not prove AdelicPeriodicOffsetHitting.

## 8. Implementation gate

No new theorem-facing search is authorized until the following exact bindings are reviewable:

- a basis and exact \(\lambda\) satisfying (1);
- the prime ideals/valuations defining \(S_\beta\);
- occurrence-labelled generation of \(\widetilde D_m(i,j)\);
- an exact replay certificate for (4);
- affine orbit replay satisfying (6)–(9);
- explicit capped-versus-proved result types.

The canonical implementation belongs in Mojo. Python or Julia may independently check small fixtures, but neither is the source of truth. Local-field displays may use approximations for diagnostics only; certificate acceptance remains integer/algebraic and fail-closed.

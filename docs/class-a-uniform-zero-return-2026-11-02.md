# Minus Class A: an exact uniform one-step zero-return predecessor theorem

**Status:** proposed, mathematically derived parameter-uniform **one-step** family lemma; native and independent-oracle acceptance required. This neither proves BH (#139) nor any multi-step X-descendant productivity. All inputs are literal ordered substitutions and full integer Parikh offsets. No quotient, unimodularity assumption, floating point or finite extrapolation enters the proof.

## Target and prior work

Continue BH #139 after the merged finite-completeness/reversal certificates #447 and abstract Lean shortest-distance result #448. Both demonstrate exact bounded graph behaviour, not how to force a boundary hit at unbounded parameters. This note instead characterizes **every possible one-generation offset-zero child**, without searching a finite graph. The existing indexed child equation and real-geometry semantics are in `kernel/psc/class_a_boundary_children.mojo`; the general nonunit finite-cokernel engine is in `kernel/psc/finite_cokernel_address.mojo`. The result here is an elementary Class-A-specific specialization, not a new general spectral theorem.

## Theorem: all one-step zero predecessors

Let k,t be arbitrary nonnegative integers, n=k+t+3, d=k+2t+5, A=n+d. Use x=0,c=1,y=2 and

    sigma(x) = x y^A x,
    sigma(c) = c y^n x,
    sigma(y) = x y^(n-1) c.

Represent the parent by its **oriented** five-tuple w=(a,b,p,q,r), where (p,q,r) is bottom-minus-top Parikh offset. Let f(a)=x for a=x,y, and f(c)=c. Define

    delta(a,b) = 1_{f(a)=x} - 1_{f(b)=x} in {-1,0,1}.

An *actual* ordered pair of child occurrences has indices (i,j), each zero based. Its child has **full Parikh offset zero** exactly in the following and only the following cases:

**(F) FIRST/FIRST:** i=j=0 and p=q=r=0, irrespective of the child tile types.

**(P) Both indices positive:** i,j>=1, and

    p = delta(a,b),
    p+q+r = 0,
    i-j = m := q+(d+1)delta(a,b).

The legal positive addresses therefore form one contiguous integer interval:

    max(1,1+m) <= i <= min(R_a+1,R_b+1+m),
    j = i-m,

where R_x=A, R_c=n, R_y=n-1 are the literal y-run lengths; an inverted interval means there are no positive hits. There are **no** mixed FIRST/non-FIRST zero-offset children. This characterizes zero **offset** only: an unequal-letter zero child is not a typed coincidence. Every legal nonempty (F)/(P) address additionally gives an actual **strict physical parent-child overlap**, as shown below; a source satisfying only the algebraic equations with an *empty* legal index interval has no such conclusion. Seed reachability is still separate.

Equivalently, for any fixed actual addresses i,j>=1, the **unique integral parent offset** capable of mapping to zero is

    (p,q,r) = (delta, i-j-(d+1)delta, j-i+d delta).

For (0,0) the only parent offset is (0,0,0). For a mixed first/non-first pair **no integral offset** can map to zero.

### Proof, no finite-enumeration premise

The incidence matrix in row/column order (x,c,y) is

    M = [ [2, 1, 1], [0, 1, 1], [A, n, n-1] ],    det(M)=-2.

For v=(p,q,r), let h=Mv=(X,C,Y). Then X-C=2p, and conversely every integral triple with X-C even has a unique integral preimage:

    p=(X-C)/2,    r=A p+n C-Y,    q=C-r.

Consequently, `M Z^3 = {(X,C,Y) in Z^3: X-C even}`, with quotient Z/2. This statement includes the nonunimodular index; it is not the cubic-power-basis displacement lattice of #438/#439.

The proper-prefix Parikh vector at occurrence i=0 is zero. At any i>=1 it is `e_{f(a)}+(i-1)e_y`. The actual child offset is

    M(p,q,r) + prefix_b(j) - prefix_a(i).

A zero child requires `M(p,q,r)=prefix_a(i)-prefix_b(j)`. If just one index is zero, the RHS has X-C odd, so is not in the image lattice. If both are zero, invertibility gives the unique zero parent.

If both indices are positive, the RHS is

    (delta,-delta,i-j).

Substitute in the displayed integer inverse to obtain exactly

    (p,q,r)=(delta,i-j-(d+1)delta,j-i+d delta).

The three coordinate equations are equivalent to the two source conditions and the value of m in (P). Actual word ordinals enforce 1<=i<=R_a+1 and 1<=i-m<=R_b+1, giving the interval. Conversely each address in that interval has the required full Parikh update to zero. This proves necessity and sufficiency for literal indexed child offsets **for all k,t>=0**, with no claim about how the parent itself was reached. QED.

### Corollary: exactly nine affine predecessor segments

For a fixed oriented parent letter pair (a,b), the positive-index difference m=i-j ranges over **every** integer in the interval

    -R_b <= m <= R_a.

Indeed the extreme differences come from (1,R_b+1) and (R_a+1,1), and each intermediate m is achieved by i=max(1,1+m), j=i-m. Consequently, the entire positive-address one-step zero-return **parent state** set for that oriented pair is the single affine integer segment

    W_(a,b)(m) = (a,b,delta,m-(d+1)delta,-m+d delta),
    -R_b <= m <= R_a.

Add the FIRST/FIRST zero-offset parent (a,b,0,0,0). This additional point is already on the segment iff delta=0 (at m=0). Because every state includes its two *oriented tile letters*, different (a,b) never collide; within one segment m uniquely determines q. There are five oriented pairs with delta=0 (four within {x,y}, one (c,c)) and four pairs with delta nonzero. The number of **distinct** oriented full-five-tuple literal strict predecessors is therefore

    sum_(a,b) (R_a+R_b+1) + 4
      = 6(R_x+R_c+R_y)+13
      = 18n+6d+7
      = 24k+30t+91.

Exactly nine of those states have parent offset zero; hence the nonzero-offset predecessor set has **18n+6d-2** distinct states. For k=t=0, this is 91 total (82 nonzero) versus 784 vertices in the accepted *seed-reachable finite S18 graph*. The sets are not asserted equal or directly comparable without taking their intersection: the inverse set is constructed from all formal oriented letter types, while the S18 graph uses only its seed descendants.

This is a **uniform linear-size, explicitly enumerable reverse-target set**, even though enumerating every individual indexed child address would yield quadratically many repetitions. The finite predecessor set does not imply finite reachability from the swap seed or any bound on the depth of entry. The normal terminalized overlap graph omits outgoing edges from already typed full-zero coincidences; they are offset-zero targets in their own right, not missing nonterminal transitions.

### Conditional hitting equivalence (no new productivity premise)

Let Gamma be **any actual occurrence-indexed, strict, child-closed** directed overlap graph for a fixed minus-Class-A substitution. Let Z be its full offset-zero vertex set, not merely its typed equal-letter coincidence terminals. Let H be Gamma's **nonzero-offset** vertices belonging to the explicit nine-segment inverse-target set. For any v in Gamma with nonzero offset,

    v reaches Z  <=>  v reaches H.

For the forward implication take the vertex just before the *first* offset-zero state on any composable occurrence path. Its index pair is necessarily a legal (F)/(P) address, hence that nonzero predecessor belongs to H. For the reverse implication, a vertex in H has a genuine legal zero-offset child by the inverse theorem and strict-geometry lemma, and child-closure keeps this child in Gamma. Concatenating that one edge reaches Z. The argument explicitly needs child closure; it does not claim it for an arbitrary curated label set.

Thus the remaining Class-A specialization of BH can be expressed as a **uniform entry-to-H problem** for every relevant cyclic seed descendant, using an O(n+d)-size exact reverse target. This is a *reduction*, not a proof that entry occurs. It does not extend automatically to all substitutions or the adelic realized-overlap system.

### Strict-overlap admissibility of every nonempty inverse address

This is stronger than a mere algebraic precursor: a legal address in the theorem actually yields a strict physical overlap. Let L_a>0 be the normalized tile length, so the incidence eigenvector equation gives L M = beta L. The top parent inflation interval is [0,beta L_a], and the bottom is [beta s,beta(s+L_b)], where s=L(p,q,r). Actual child i begins at its top proper-prefix length P_a(i), while bottom child j begins at beta s+P_b(j). Since the *full* Parikh zero-child equation is M w=prefix_a(i)-prefix_b(j), their beginnings are identical: P_a(i)=beta s+P_b(j). Both children have strictly positive lengths and lie inside their respective inflated parent intervals, hence share a positive open interval. Therefore their inflated parents overlap strictly; dividing by beta shows that the original parent overlap is also strict. The child at common beginning is strict too. No approximation of beta, endpoint-equality guess, or extra tiling legality hypothesis is used.

Thus the formula describes genuine literal one-step **strict overlap edges** between the computed parent and offset-zero child whenever the index interval is nonempty. It does not prove that those parent states occur in the swap-seed forward closure or arise in the full realized tiling-dynamical system. Native regression checks strict Perron geometry independently for every unique inverse predecessor at the declared parameter specimens.

### Immediate uniform consequence for the X hub

The canonical X state is `(x,x,1,0,-1)`. Both initial letters are x, so delta(x,x)=0. Case (P) would require p=0, contradicting p=1. Case (F) would require the entire parent offset to vanish. Thus **X has no direct one-step offset-zero child at any minus-Class-A parameters**, even though known selected paths can reach coincidence after further steps. This is a lower bound of two steps, not a failure of BH and not a statement about all descendants.

## Executable contract and controls

New canonical `kernel/psc/class_a_zero_return.mojo` implements the integer interval, unique inverse predecessor, and complete nine-segment enumeration with checked arithmetic. The native test replays every literal address at (k,t)=(0,0),(1,2),(3,0),(0,3), checks each unique parent and child against the independent strict Perron geometry guard and actual member transport, perturbs all three-offset conditions, exhaustively cross-checks bounded parent triples, and compares predicted zero-index pairs with all outgoing occurrence rows of the complete (0,0) S18 graph. All typed coincidences remain terminalized in that graph, so those sources are deliberately skipped. Nonexistent addresses, negative parameters and mixed first/non-first inverse requests refuse. The separate Python test implements independent proper-prefix counting and integer matrix multiplication; its positive/negative checks are not substitutes for native CI.

Run at repository root:

```sh
python -m pytest -q tests/test_class_a_zero_return_oracle.py
```

Run from `kernel/` with the locked environment:

```sh
pixi run --locked mojo run -I . tests/test_class_a_zero_return.mojo
```

No new governed PSC theorem status is requested until exact-head acceptance. **Nonclaims:** no parameter-uniform size bound or productivity of Reach(X); no classification of more than one substitution generation; no forced access to the one-step predecessor interval; no nonunit realized-overlap/adelic representation bridge; no global #138, #139, #84, G1 or PSC closure. In particular, this is an exact *reverse-target filter*, not a recurrence mechanism.

## Next reproducible mathematical obligation

Using these intervals, identify an occurrence-compatible predecessor **transfer** that carries every relevant cyclic seed descendant into (F) or (P) in finitely many generations. A successful candidate must supply a parameter-uniform forward-covering/escape argument, include genuine RUN/LAST distinctions, and separately handle the nonunit realization dictionary. A fitted table of points satisfying (P) is not enough: the hard step is forcing entry from the entire cyclic obstruction set.

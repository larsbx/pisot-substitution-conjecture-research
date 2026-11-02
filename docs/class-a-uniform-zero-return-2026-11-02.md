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

where R_x=A, R_c=n, R_y=n-1 are the literal y-run lengths; an inverted interval means there are no positive hits. There are **no** mixed FIRST/non-FIRST zero-offset children. This characterizes zero **offset** only: an unequal-letter zero child is not a typed coincidence. Nor does a formal parent satisfying (F)/(P) automatically belong to the strict overlap graph.

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

### Immediate uniform consequence for the X hub

The canonical X state is `(x,x,1,0,-1)`. Both initial letters are x, so delta(x,x)=0. Case (P) would require p=0, contradicting p=1. Case (F) would require the entire parent offset to vanish. Thus **X has no direct one-step offset-zero child at any minus-Class-A parameters**, even though known selected paths can reach coincidence after further steps. This is a lower bound of two steps, not a failure of BH and not a statement about all descendants.

## Executable contract and controls

New canonical `kernel/psc/class_a_zero_return.mojo` implements the integer interval and the inverse predecessor directly with checked arithmetic. The native test replays every literal address at (k,t)=(0,0),(1,2),(3,0),(0,3), checks the unique parent against independent actual member transport, perturbs all three-offset conditions, exhaustively cross-checks bounded parent triples, and compares predicted zero-index pairs with all outgoing occurrence rows of the complete (0,0) S18 graph. All typed coincidences remain terminalized in that graph, so those sources are deliberately skipped. Nonexistent addresses, negative parameters and mixed first/non-first inverse requests refuse. The separate Python test implements independent proper-prefix counting and integer matrix multiplication; its positive/negative checks are not substitutes for native CI.

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

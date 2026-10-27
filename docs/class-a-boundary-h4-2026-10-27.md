# Minus class-A boundary H4: all actual children return to the E2 image

**Scope and provenance (2026-10-27).** This is a new scoped one-source result stacked on [PR #360](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/360) and its predecessors #359, #357 and merged #355. No full carrier closure, uniform boundary-hitting theorem or Pisot Substitution Conjecture claim is made. Independent human review pending. The accepted three-primary-source stop/go remains \`docs/class-a-boundary-e2-stopgo-2026-10-27.md\`; this continuation is the next actual-word source specialization, not a new import of a tiling theorem.

## Work shown

### Assumptions and hypotheses

On the entire **minus** determinant-two class-A boundary chamber, \(\varepsilon=-1\), \(k,t\in\mathbb Z_{\ge0}\), \(n=k+t+3\), \(d=2n-1-k\), \(A=n+d=2n+t+2\), \(N=n-1\). Exactly the three ordered substitution images are \(x\mapsto xy^Ax\), \(c\mapsto cy^nx\), \(y\mapsto xy^Nc\). Use true occurrence ordinal pairs, the complete bottom-minus-top Parikh difference, and strict physical interior overlap in the canonical cubic Perron field. No global unimodularity, tile-length independence, legal-tower identification, nonunit internal-space transfer, or predecessor contraction is assumed.

The source is the literal state

\[
H_4=(x,y,0,-2,4).
\]

PR #360 establishes that it occurs as the **actual** \((A+1,2n+1)\) child of the strict Dxx=(x,x,1,2,-4) overlap on every member; this is not yet a proof that Dxx is reachable from a seed in every parameter chamber. For the positive Perron root \(\beta=n+2+\alpha\), write \(h=1/\beta\) and set \(a=L_x/L_y\), \(b=L_c/L_y\). The exact previous certificates prove \(0<h<\alpha<1\), \(0<z=\alpha+h<1\), \(b=1+h\), \(a=2+\alpha-h>2\). PR #358 supplies the **exact** half-chamber separator

\[
\text{high}:\quad \alpha>\tfrac12\iff (t>k)\ \lor\ (t=k\ge2),
\]
and proves \(\alpha\ne\tfrac12\); this is not guessed from samples.

### Derivation / reduction

The true source shift in \(L_y\) units is \(4-2b=2-2h\), strictly between \(1\) and \(2\). After inflation it is

\[
B=\beta(2-2h)=2\beta-2=2n+2+2\alpha.
\]

The top x-image starts at \(0\), \(a+i-1\) (run \(1\le i\le A\)), and \(a+A\) (last \(i=A+1\)). The bottom y-image starts at \(B\), \(B+a+j-1\) (run \(1\le j\le N\)), and \(B+a+N\) (last \(j=N+1\)). For an actual pair of intervals \([S_t,S_t+\ell_t]\), \([S_b,S_b+\ell_b]\), the **strict** overlap predicate is

\[
-\ell_b<S_b-S_t<\ell_t.
\]

Every one of the nine first/run/last kinds follows from this exact open-interval test, with actual word bounds:

| top/bottom | iff actual interior-overlap ordinals | resulting typed target |
|---|---|---|
| first / any | none, since \(B>a\) | — |
| run / first | \(j=0,\quad2n+1\le i\le\min(A,\,2n+3+\mathbf1_{\rm high})\) | \((y,x,1,2,2n-3-i)\) |
| run / run | \(1\le j\le N,\ i=j+\delta\le A\), \(\delta\in\{2n+2,2n+3\}\) (low), or \(\delta\in\{2n+3,2n+4\}\) (high) | \((y,y,2,2,2n-4-\delta)\) |
| run / last | none | — |
| last / first | \((A+1,0)\) iff \(t=0\) or \(t=1\) and high | \((x,x,1,2,-t-6)\) |
| last / run | \(i=A+1,\ \max(1,t-\mathbf1_{\rm high})\le j\le t+2\) | \((x,y,2,2,j-t-7)\) |
| last / last | none | — |

The top/bottom Parikh recurrence is the existing literal prefix identity
\[
w'=Mw+P_{\rm bottom}(j)-P_{\rm top}(i),\qquad
M(0,-2,4)^{\mathsf T}=(2,2,2n-4)^{\mathsf T}.
\]
It is checked symbolically for first, run and last representatives in \(\mathbb Q[t,k]\) by \`psc.class_a_boundary_occurrences.symbolic_child\`, then every accepted member occurrence is verified against the actual word and cubic Perron geometry by \`verify_member_edge\`.

The nontrivial index rounding is reproducible from:

* **run/first.** \(B-a=2n+\alpha+h=2n+z\) and \(B+1=2n+3+2\alpha\), so \(B-a<i<B+1\) yields exactly the stated three or four possible ordinals.
* **run/run.** The physical offset is \(B+j-i\); strict overlap is \(|B+j-i|<1\). The two possible integer differences shift by one across the exact \(\alpha=1/2\) separator. Discarding the actual word bound \(i\le A\) invents nonexistent children for small \(t\).
* **last/first.** The two x intervals have shift \(z-t-2\), and strict overlap is \(|z-t-2|<a\). Since \(a+z=2+2\alpha\), this is \(t<2\alpha\). Precisely \(t=0\), or \(t=1\) in the high chamber, survive.
* **last/run.** The bottom y start relative to the last top x is \(j-t-1+2\alpha\). The guard \(-1<j-t-1+2\alpha<a\) reduces to \(j\ge t\) (low) or \(j\ge t-1\) (high), with \(j\le t+2\) in both. The actual bottom run starts at \(j=1\), so the low \(t=0\) case has only \(j=1,2\).
* The first children and run/last and last/last are disjoint using \(B>a\), the genuine terminal positions, \(a>2\), \(N=n-1\) and the positive root inequalities; this is a geometric exclusion, not a projected adjacency omission.

The four accepted classes have, **for every admissible \(k,t\)**,

\[
\boxed{\#\text{actual ordered children of }H_4=2t+5.}
\]

For low \(\alpha<1/2\), the four case counts are: at \(t=0\), \(2+0+1+2=5\); at \(t=1\), \(3+1+0+3=7\); and for \(t\ge2\), \(3+(2t-1)+0+3=2t+5\). For high \(\alpha>1/2\), necessarily \(t\ge1\): at \(t=1\), \(3+0+1+3=7\); at \(t=2\), \(4+1+0+4=9\); for \(t\ge3\), \(4+(2t-3)+0+4=2t+5\). Hence the two half-chambers have the same cardinality **despite different actual ordinal sets**.

The complete **union over all members** of the children consists of exactly **13** typed labels:

| child types | Parikh \((x,c)\) | y values | number |
|---|---|---|---:|
| y/x | (1,2) | −7…−4 | 4 |
| y/y | (2,2) | −8…−6 | 3 |
| x/x | (1,2) | −7…−6 | 2 |
| x/y | (2,2) | −8…−5 | 4 |

Each is actually realized at finite true word ordinals. **All 13 labels are contained in PR #360's already registered E2/Dxx 46-label image.** This is a useful two-stage closure compatibility fact; it does **not** establish that the 46-label image, or the prior 50-label T_m image, is forward closed.

### Evidence and replay

Canonical sources: \`kernel/psc/class_a_boundary_h4_children.mojo\`, \`kernel/class_a_boundary_h4_children.mojo\`; native regression \`kernel/tests/test_class_a_boundary_h4_children.mojo\` and independent Python oracle \`oracles/python/class_a_boundary_h4_children.py\`, with \`tests/test_class_a_boundary_h4_children.py\`. Source checks use existing vendored exact arithmetic, not a parallel polynomial package. The native test (36 members) independently compares the complete Cartesian product of actual word indices against exact Perron overlap and full Parikh transport, validates the actual Dxx→H4 ancestry, verifies every generated indexed packet, detects duplicate synthesis and attains every target type. Python uses its separately written Fraction root enclosure/ordered word model; the finite fixed experiment on \(0\le k,t<10\) checked **100 members / 1,400 accepted occurrences**, all 13 labels and no classification mismatches; the finite computation is not the proof of uniformity.

From repository root:
\`\`\`sh
python -m pytest -q tests/test_class_a_boundary_h4_children.py
\`\`\`
From \`kernel/\`:
\`\`\`sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_h4_children.mojo
pixi run --locked mojo run -I . class_a_boundary_h4_children.mojo
\`\`\`
Dedicated \`.github/workflows/class-a-boundary-h4.yml\` is the fresh exact-head canonical/native acceptance check and also replays the inherited #360 E2 regression. **Do not describe a queued, unexecuted or failed workflow as successful**; the source is a proposed theorem package until the required replay has been checked.

### Negative controls

The high-half rule is **not** simply \(t\ge k\): \((k,t)=(0,0),(1,1)\) are low, while \(k=t\ge2\) is high. The low/high child index difference jumps, but the final \(2t+5\) count does not. In the low chamber \(t=0\), the bottom run index \(j=0\) is nonexistent, leaving \(j=1,2\). The last/first child exists at \(t=0\) and at \(t=1\) only in the high half; every remaining nominal first/last, last/last and run/last choice is rejected at the actual strict geometry layer. Corrupted Parikh coefficients, an invented ordinal, a disjoint pair, duplicate indexed children and a target escaping the 13/46-label envelope all cause refusal.

### Non-claims / remaining gaps

This is an exact **one-parent outgoing star** and a 13-label containment fact, not a productive-path theorem for all 13 targets, not a full forward-closed seed-reachable carrier, not a target-aware balanced-pair packet proof, and not a proof that H4 is seed-reachable on every parameter member. The predecessor's one-sided A1′, C4 hub-residual word, global G1, universal BH/#139, plus-sign strips, and general Pisot Substitution Conjecture remain open. The next mathematical obligation is to incorporate this 13-label image into a uniform descendant carrier with *existential* well-founded occurrence-compatible paths, preserving the genuine cycles already found in #352/#355/#359. Independent human review remains pending and is not a development blocker.

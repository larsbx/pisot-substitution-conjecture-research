# Class D is uniformly outside the Barge power/rotation shortcut — 2026-10-16

**Status:** exact symbolic endpoint-map theorem; **negative stop/go**, not pure-discrete-spectrum or #139 closure. This closes a *prior-art applicability question*, not a Pisot-conjecture premise.

**2026-10-19 status correction:** PRs #263/#266 are no longer open review
candidates; their distinct `b=0` certificate systems were integrated by
merged PR #277. The theorem in this note is unchanged. The remaining class-D
boundary-hitting target is the two positive-`b` interiors
`s=±1, a>=0, b>=1`.

**Target:** the unsettled portion of class D of Theorem E, including the complete determinant-two \(b=0\) boundaries in the two residual parameter quadrants and their \(b>0\) interiors. At the time this note was written, #263/#266 were open review contributions. They were later integrated by merged PR #277; this note itself neither proves nor depends on those boundary certificates.

## 1. Primary prior art and precise scope

Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems* (2016), Theorem 3.13, arXiv:1403.7826, proves PDS for primitive nonperiodic Pisot substitutions **injective on initial letters** and **constant on final letters**, and the mirror condition is covered by reversal. The theorem has no unit-determinant requirement. The verified import and the power/common-prefix-or-suffix-rotation preservation facts are already recorded at:

- \`docs/sadic-transfer-literature-gate-2026-10-11.md\`, §§2–3;
- \`kernel/psc/barge_class.mojo\` and the vendored \`substitution_dynamics.barge_class\` detector;
- ledger nodes \`BargeClassFlowPDS\` and \`BargeClassSymbolicPDS\`.

The candidate shortcut under audit is **only**: some positive power \(\sigma^n\), or its allowed maximal common-prefix or common-suffix rotation, belongs to Barge's class or its mirror. Other conjugacies, return-word substitutions, Rauzy geometries and independent overlap arguments are **not** ruled out by the theorem below.

## 2. A uniform, exact endpoint-map obstruction

For any nonnegative integers \(p,q,r\), consider the non-erasing class-D word system
\[
\boxed{
\sigma(x)=x\,y^p c,\qquad
\sigma(c)=c\,y^q x,\qquad
\sigma(y)=c\,y^r c.}\tag{D}
\]
The determinant-two Pisot members have \(p=q\pm1\) with the additional exact parameter inequalities of \`docs/p1b-boundary-hitting-progress-2026-10-08.md\` §4d. We do **not** assume those inequalities for the elementary endpoint statement.

Let \(f(i)=\mathrm{first}(\sigma(i))\) and
\(g(i)=\mathrm{last}(\sigma(i))\). Their tables are
\[
\begin{array}{c|ccc}
i&x&c&y\\\hline
 f(i)&x&c&c\\
 g(i)&c&x&c
\end{array}.
\tag{1}
\]
Since every image is nonempty, the first and last letters of \(\sigma^n(i)\) are respectively \(f^n(i)\) and \(g^n(i)\), by elementary induction. Direct composition gives
\[
 f^n=(x,c,c)\quad(n\ge1),\qquad
 g^n=\begin{cases}(c,x,c)&n\ \text{odd},\\
                   (x,c,x)&n\ \text{even},
      \end{cases}\tag{2}
\]
with ordered coordinates \((x,c,y)\).

**Proposition D-Barge-STOP (proved).** For every \(p,q,r\ge0\) and \(n\ge1\):

1. \(\sigma^n\) is **neither** injective on initial letters **nor** constant on initial letters: \(x,c\) keep distinct initials, while \(c,y\) share an initial.
2. \(\sigma^n\) is **neither** injective on final letters **nor** constant on final letters: \(x,c\) keep distinct finals, while one of \(x,y\) or \(c,y\) shares a final.
3. The images of \(\sigma^n\) have **no nonempty common prefix and no nonempty common suffix**: the images of \(x,c\) start with different letters and end with different letters.
4. Consequently, \(\sigma^n\) lies in **neither** Barge's class (initially injective, finally constant) **nor** its mirror (initially constant, finally injective); every maximal common-prefix and common-suffix rotation is the identity and does not change that verdict.

**Proof.** (1) and (2) follow from the two explicit maps (2), independent of \(p,q,r\). In particular \(f^n(x)\ne f^n(c)\) and \(g^n(x)\ne g^n(c)\), which give (3). For (4), failure of both endpoint conditions rules out direct membership. With no common nonempty prefix or suffix, the only conjugate obtained through the documented common-prefix/suffix rotations of that power is itself. This holds for *every* \(n\), not merely powers tested by the executable search. \(\square\)

**Corollary (scope of the stop).** Every determinant-two PIP class-D member, on the already certified region \(r\ge q-1\), on either pending \(b=0\) boundary, and throughout the unproved \(b>0\) interiors, lacks **this** Barge power/rotation witness. Thus class D is a legitimate testing ground for genuinely new #139 boundary-hitting machinery, unlike the October 15 \(\sigma_{k,h}:a\mapsto a^kbc^h,\ b\mapsto ab,\ c\mapsto a\) family, which was corrected on October 16 as *directly mirror-Barge*.

## 3. Exact calibration and acceptance

The endpoint proof is parameter-uniform and needs **no PIP screening or eigenvalue numerics**. The canonical Mojo regression in \`kernel/tests/test_barge_class.mojo\` checks, for the class-D parameter triples
\[
 (p,q,r)=(3,2,0),\ (5,6,4),\ (4,3,3),
\]
that the first/last maps of powers \(n=1,2,3\) match (2), that every such power has zero common-prefix/suffix length, that neither class membership holds, and that the existing \`barge_witness\` reports no witness through power 3. These are finite tests of the *general identity*, not a proof of it; a negative \`barge_witness\` result alone would prove nothing about unbounded powers.

The contrasting *positive* regression from PR #271 checks direct mirror-Barge witnesses on two members of its own family. Both controls should remain together: class-D is not accidentally classified as a prior-art family, and the already-solved mirror family is not accidentally promoted as new.

**Fail-closed research decision:** do not rerun \`barge_witness\` on growing class-D parameters in the hope that a higher power or one of the *supported* common-word rotations eventually succeeds. Such an attempt is ruled out for all powers by (2). Instead retain class-D's established explicit overlap witnesses and advance the independent occurrence-labelled symbolic/target-aware boundary certificates. Historical note: #263/#266 were review candidates when this stop/go was written. Merged PR #277 later integrated their scoped \(b=0\) certificate machinery; the positive-\(b\) interiors remain open.

The remaining mathematical obligation remains universal #139 (or a scoped class-D uniform boundary-hitting theorem with complete parameter coverage). Neither this theorem nor its tests prove a child-closed bad-SCC contradiction, PDS, G1 or general PSC.

# Exact length windows for the two open existence questions

**Status:** elementary interface lemma and finite executable controls. Neither
universal aligned coincidence (#138) nor universal boundary hitting (#139)
is proved here. The class-D certificates in PRs #290 and #293 retain their
separate scope and execution requirements.

The [targeted literature gate](two-obstruction-moments-literature-gate-2026-10-20.md)
was completed before this implementation. The linear algebra below is a
standard cyclic-vector argument. Its purpose is to expose the missing step
in a tempting fixed-ray pumping argument and to give a second, exact check
of supplied boundary addresses.

## 1. A finite observation window is injective

Let $M\in\mathbb Z^{d\times d}$ have irreducible characteristic polynomial
$\chi_M$ over $\mathbb Q$, and let $e^T=(1,\ldots,1)$. Define

$$
O_M=\begin{pmatrix}e^T\\e^TM\\\vdots\\e^TM^{d-1}\end{pmatrix}.
$$

**Length-window lemma.** $O_M$ is nonsingular. Consequently, for any two
finite words $P,Q$ over this alphabet,

$$
\pi(P)=\pi(Q)
\quad\Longleftrightarrow\quad
|\sigma^j(P)|=|\sigma^j(Q)|\quad(0\le j<d).
$$

**Proof.** A dependence of the rows would give a nonzero polynomial $f$ of
degree less than $d$ with $e^Tf(M)=0$. Irreducibility makes $f$ coprime to
$\chi_M$. A Bezout identity and Cayley–Hamilton make $f(M)$ invertible,
contradicting $e^T\ne0$. Finally
$|\sigma^j(P)|-|\sigma^j(Q)|=e^TM^j(\pi(P)-\pi(Q))$.

For a PIP incidence matrix the same conclusion holds with $M^r$ for any
integer $r>0$. Indeed, if $\beta$ is its degree-$d$ Pisot root, then
$\mathbb Q(\beta^r)=\mathbb Q(\beta)$. Otherwise separability would provide
another embedding fixing $\beta^r$, hence another conjugate of $\beta$ of
modulus $\beta>1$, impossible for a Pisot number. Thus the characteristic
polynomial of $M^r$ is again irreducible of degree $d$.

The executable checks rank directly, so it needs no unverified irreducibility
assertion. Full rank alone does **not** prove PIP. Arithmetic uses the
vendored unbounded rational and generic matrix routines; offsets are lifted
before multiplication. The supported executable dimension is 1 through 6;
the lemma itself has no such restriction.

## 2. What this says about the fixed hub rays (#138)

Suppose the fixed rays $u,v$ contain the same nonempty word $B$ at the same
position $k$. Write their preceding words as $P=u[0:k)$ and $Q=v[0:k)$,
and put $\delta=\pi(Q)-\pi(P)$. Under substitution the **specified** two
occurrences of $B$ become occurrences of $\sigma^r(B)$ whose starting
positions differ by

$$D_r=e^TM^r\delta.$$

For a ternary PIP substitution, if these inherited occurrences remain at
equal positions at levels $0,r,2r$, then $\delta=0$. The first letter of
$B$ already witnesses strong coincidence in the original fixed rays.
This is a statement about the same inherited occurrences, not all possible
occurrences of the word.

Thus an argument that repeatedly inflates one same-position block cannot
quietly assume its alignment survives. Three aligned observations would
already contain the desired coincidence. A proximality proof that chooses
different blocks after inflation must instead prove those choices remain
at the same position on the two tracks and provide unbounded lengths. The
imported Barge–Zamboni equivalence does not supply that existence step.

**Actual PIP fixed-ray control.** With letters $(x,c,y)=(0,1,2)$, take

$$\sigma(x)=xy^4c,\qquad \sigma(c)=cy^3x,\qquad \sigma(y)=cyc.$$

The canonical PIP screen accepts this specimen. Both fixed rays have $yyy$
at position 1. Their preceding words are $x,c$, with bottom-minus-top defect
$(-1,1,0)$. The three start differences are $(0,-1,-3)$: the first inherited
blocks start at 6 and 5, the next at 23 and 20. This is a productive PIP
control against automatic alignment, **not** a nonproductive hub component
or a counterexample to A1′.

The same matrix has the nonzero defect $(2,-3,1)$ with length observations
$(0,0,-1)$. Hence even two scalar checks are insufficient. This latter
defect is an algebraic sharpness control; no claim is made that it occurs
between prefixes of these fixed rays. More generally, fewer than $d$ rows
have a nonzero rational kernel, and clearing denominators gives an integer
defect they cannot distinguish.

## 3. An exact address certificate for boundary hitting (#139)

Use bottom-start minus top-start convention for an integer offset $w$.
Starting at letters $i,j$, choose **proper-prefix occurrence indices** on
each track, from root to leaf. If the chosen level-$m$ descendants have
prefixes $P\prec\sigma^m(i)$ and $Q\prec\sigma^m(j)$, their offset is

$$\delta_m=M^m w+\pi(Q)-\pi(P).$$

At each step the verifier reconstructs the current parent letters and the
actual prefix digits, and updates $\delta'=M\delta+q-p$. It never trusts a
supplied prefix vector or a list of unrelated prefix choices. The identity
above follows by induction on the address length.

**Supplied-address criterion.** In dimension three, the selected descendants
have a common left boundary exactly when all three entries of $O_M\delta_m$
vanish. Equal terminal letters additionally give a coincidence; different
terminal letters give only a boundary hit.

**Why a successful address is geometrically compatible.** For a primitive
substitution use its positive left Perron length vector $\ell$. At zero
defect the two descendant intervals have the same left endpoint and positive
lengths, hence positive interior intersection. Each is nested in its
specified ancestor interval. Their common interior therefore lies in both
ancestors at every level (after the common positive inflation rescaling).
All chosen ancestor pairs are genuine interior overlaps. Proper occurrence
indices are essential: an empty terminal interval at the end of an image
would invalidate this argument, and the reader rejects such indices.

This verifies **one supplied path**. It does not prove the starting state is
seed-reachable, cover a carrier, or find a hit for every cyclic state.
An unsuccessful supplied path does not prove absence of another path.

## 4. Exact coordinates do not remove the remaining obstruction

If $\chi_M(t)=t^d+c_{d-1}t^{d-1}+\cdots+c_0$ and $\mu=O_M\delta$, then
Cayley–Hamilton gives the same recurrence in moment coordinates:

$$
\mu'=C\mu+O_M(q-p),\qquad
C=\begin{pmatrix}
0&1&\cdots&0\\
\vdots&&\ddots&\vdots\\
0&0&\cdots&1\\
-c_0&-c_1&\cdots&-c_{d-1}
\end{pmatrix}.
$$

This is an invertible rational change of coordinates of the original affine
problem. Its integer states lie in $O_M\mathbb Z^d$, which need not be the
whole integer lattice. No new contraction, descent, or hit-forcing mechanism
follows. Because full integer defects are distinguished, no finite-place
information is discarded, and no unimodularity assumption is introduced.

**Reducible negative control.** For $0\mapsto102,1\mapsto210,2\mapsto021$,
the incidence matrix is all ones, hence primitive with characteristic
polynomial $t^2(t-3)$. Every length row is a multiple of $e^T$; the nonzero
defect $(1,-1,0)$ is invisible forever. The executable refuses its singular
observation map. This is not a PIP counterexample.

## 5. Implementation, replay and proof boundary

Canonical implementation: `kernel/psc/length_moments.mojo`.
Regression and finite receipts: `kernel/tests/test_length_moments.mojo`.
From `kernel/`, the required-toolchain command is:

```sh
pixi run --locked mojo run -I . tests/test_length_moments.mojo
```

The regression checks the two drift controls; independently found
Dumont–Thomas coincidence addresses for all three pairs of the stated PIP
specimen; a genuine nonzero-offset swap occurrence against the existing
geometric path reader; unequal-letter boundary targets; altered root offsets;
malformed indices, depths and budgets; return periods 1,2,3,7,64; and the
singular reducible control. The search control uses depth 20, 10,000 states
and 1,000,000 occurrence choices, and requires a successful path receipt.

Execution provenance and limitations are in
[`evidence/two-obstruction-moments-2026-10-20/README.md`](../evidence/two-obstruction-moments-2026-10-20/README.md).
The exact mathematical obligations still missing are:

- **#138:** force arbitrarily long common blocks at equal positions in the
  residual fixed hub rays, or directly produce an equal-Parikh same-letter
  prefix witness. Inherited block inflation by itself supplies neither.
- **#139:** supply such a zero-defect address for every relevant seed-reachable
  cyclic overlap, or a justified seed-containing invariant cover and descent.
  This finite reader supplies neither coverage nor universal existence.

The general PSC theorem remains conditional on both universal premises.
No existing lattice partition, class-D carrier, cap or acceptance gate is
modified by this contribution.

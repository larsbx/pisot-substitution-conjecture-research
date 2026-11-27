# Diagonal residual exit: targeted literature decision

Date: 27 November 2026 (America/New_York).

## Exact proposed target

Continue the literal family `sigma=(1,0 1^r 2,0^r 1)`, for integer
`r>=12`. Put `A=beta-r`, `B=r/beta`, `theta=(r-1)/beta`, where
`beta` is the specified root of `X^3-r X^2-2 X-r` in `(r,r+1)`.
For a full integral typed packet `(1,1;x,y,z)`, retain
`D=x+beta*y+(1+B)*z`. The immediate target is an actual original-occurrence
path from the run-window residual region `|D|<=r-1`, beyond the previously
proved box `max(|z|,|y|)<=floor((r-2)/3)`, to labelled coincidence.

The prior written outer descent reduces the unresolved region to a finite
integer ellipse for each parameter, but not to one parameter-independent
finite list. Its weaker convenient enclosure is `z^2+y^2<r^2`.
The selected child is `(1,1;y+r*z,t,y)`, with
`|t+A*y+B*z|<=theta`. Both original run ordinals and the full first
coordinate must be reconstructed at every edge. No projected-coordinate
certificate is substituted for that path.

Read before deciding: the 24 November diagonal reduction, its source gate,
and the append-only side notes, especially the nearest-rounding four-cycle
and the difference between selected productivity and closed carrier
termination.

## Primary sources inspected

1. S. Akiyama, T. Borbely, H. Brunotte, A. Petho and J. Thuswaldner,
   *Generalized radix representations and dynamical systems I*,
   [author manuscript](https://www.math.tsukuba.ac.jp/~akiyama/papers/cubic.pdf),
   Theorem 2.1, Lemma 4.2 and Theorem 5.1.
   Theorem 2.1 identifies greedy beta finiteness with termination of the
   corresponding prescribed floor SRS. Lemma 4.2 bounds orbits in a
   contracting regime and therefore gives eventual periodicity. Theorem 5.1
   needs a witness set containing the signed standard vectors, closed under
   both the map and its signed counterpart, whose members all terminate.
   These distinguish boundedness, periodicity and zero-hitting.
   They do not assert productive exit for a freely selected literal digit
   map. A finite witness computation at selected parameters does not prove
   uniform coverage of this whole curve of parameters.

2. S. Akiyama and A. Petho, *Discretized rotation has infinitely many periodic
   orbits*, Nonlinearity 26 (2013), 871-880,
   [author-hosted published paper](https://arato.inf.unideb.hu/petho.attila/cikkek/Akiyama_Petho_2012a.pdf),
   introduction and Theorems 1-2.
   Their reversible map is `(x,y)->(y,-floor(x+lambda*y))`, with
   `-2<lambda<2`; the linear part has determinant one. The shifted interval
   version still fixes the rounding rule. The diagonal PSC map has
   determinant `B<1`, several possible admissible digits, and additional
   original-word occurrence constraints. The theorem is a useful warning
   against treating a rotation-like recurrence as automatically terminating,
   not a theorem about the present map. The repository's literal four-cycle
   is the directly relevant negative control.

3. M. Minervino and J. Thuswaldner, *The geometry of non-unit Pisot
   substitutions*, Annales de l'Institut Fourier 64 (2014), 1373-1417,
   [publisher PDF](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf),
   Section 2, Definition 2.1 and Theorem 9.10.
   Prefix-automaton edges retain a decomposition `sigma(a)=p b s`;
   strong coincidence retains actual equal letters and equal prefix or
   suffix Parikh vectors. The nonunit representation uses the relevant
   non-Archimedean places. The tiling conclusion in Theorem 9.10 additionally
   assumes geometric property (F) and strong coincidence. This supports
   literal occurrence bookkeeping but supplies neither of those missing
   hypotheses here. Do not use a unit-only inverse argument or replace the
   original words by the incidence polynomial alone.

4. S. Akiyama and J.-Y. Lee, *Algorithm for determining pure pointedness of
   self-affine tilings*,
   [author manuscript](https://arxiv.org/pdf/1003.2898),
   introduction, Section 2.4 and Definition 2.4.
   Their overlap notion uses interior intersection and coincidence also
   requires matching tile type. The global criterion quantifies over every
   overlap, under the specified substitution/Meyer hypotheses. A selected
   literal path is the appropriate local witness, but it is not a complete
   overlap graph or an automatic spectral conclusion. Their discussion
   explicitly warns that omitting the Meyer hypothesis can invalidate an
   algorithmic verdict.

## Hypothesis transfer and decision

**Proceed with the narrowed family-specific exit problem.** The cited work
supplies the right recurrence vocabulary, finite witness methods and literal
prefix semantics; none of these inspected statements closes this parameter
family's residual region without additional proof. The novelty claim should
therefore be limited to an explicit specialization, occurrence certificate,
or formal endpoint actually obtained.

A useful equivalent form for proof design is to set `u=t+z`. The pair update
is then

`(z,y) -> (y,-z+u)`, with `|u+A*y-(1-B)*z|<=theta`.

This exposes a controlled perturbation of the quarter-turn. It suggests
bounded blocks of choices and quadrant/axis cases, rather than relying on
strict descent of a fixed nearest selector at every edge. It is only a
change of coordinates, not itself an exit proof. Any proposed ranking must
be checked against admissible digits and the retained full packet.

## Negative controls and acceptance boundary

- Keep the exact four-step nonzero nearest-rounding cycle and its productive
  alternative exit. Selector nontermination is not a counterexample to
  existential literal coincidence.
- Reject out-of-run or shifted original ordinals, wrong child types,
  endpoint-only contact, altered first coordinates, projected zero mistaken
  for full zero, and a terminal `1/2` zero labelled as equal-letter zero.
- A cap, unresolved sign comparison or arithmetic refusal gives no verdict.
- Separate all-parameter mathematics, any Lean endpoint, native Mojo replay,
  independent finite oracle, and hosted acceptance.
- Any all-source theorem still has to compose the required literal entry
  with the proved exit and expose exactly its hypotheses. The present
  literature decision supplies neither uniform general BH nor the general
  Pisot substitution conjecture.

The DOI page of the discretized-rotation paper and one arXiv fetch were
unavailable; the author-hosted published PDF above was inspected instead.
No inaccessible source statement is used.

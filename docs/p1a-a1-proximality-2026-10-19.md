# A1′ as a proximality problem for the two fixed hub rays — 2026-10-19

**Status:** imported equivalence plus a narrowed open theorem target for #138.
This note does not prove A1′, strong coincidence, #84 or PSC.

## 1. Standing A1′ configuration

After the endpoint normal form and Theorem C's squaring reduction, a hypothetical
aligned obstruction may be assumed to have two distinct letters `x,c` with

```text
sigma(x) = x X,
sigma(c) = c Y,
```

so the right-infinite words

```text
u = sigma^infinity(x),
v = sigma^infinity(c)
```

are substitution-fixed and anchored at the same origin. A1′ says that this
prescribed pair is eventually coincident.

The extra hypotheses are not the generic ternary strong-coincidence problem:
`{x,c}` is the residual bad hub edge of a closed nonproductive aligned
obstruction, while a distinct Barge–Diamond-good pair already exists.

## 2. Imported fixed-point equivalence

Barge–Zamboni, *Central sets and substitutive dynamical systems*
(arXiv:1301.5745), Theorem 4.1, for an irreducible primitive substitution of
Pisot type and any pair of substitution fixed points `u,v`, gives the
equivalence

```text
u and v strongly coincident
<=> u and v proximal
<=> v = p*(u) for a minimal idempotent p
<=> for every prefix z of v, Occ_u(z) is central.
```

Their Proposition 4.8(2) supplies the direction needed here directly:
**proximal fixed points are strongly coincident**. Their Corollary 4.10,
using the uniformly recurrent-word characterization of central sets, also gives

```text
strong coincidence
<=> for every prefix z of v, Occ_u(z) is an IP-set.
```

The hypotheses match PIP and add no unimodularity assumption.

Primary source:
https://arxiv.org/abs/1301.5745

## 3. Equivalent A1′ target

The final aligned lemma can therefore be attacked as:

> **A1-Prox (open).** In the residual fixed-hub configuration supplied by the
> aligned obstruction normal form, the two substitution-fixed rays
> `u=sigma^infinity(x)` and `v=sigma^infinity(c)` are proximal.

Equivalently, for every `N` there are shifts `k` at which `u` and `v`
agree on a word of length `N`. Proving A1-Prox proves A1′ by the imported
Barge–Zamboni proposition.

The IP-set version gives a second exact target:

> For every prefix `z` of `v`, the occurrence set of `z` in `u` is an
> IP-set.

Neither formulation is itself a proof.

## 4. Why this helps the current proof machinery

The C4 recognizability track has already proved:

- arbitrarily long legal ancestry towers in a finite strict component;
- finite decorated ancestry/cut states;
- recognizability of both the original substitution hierarchy and the derived
  component hierarchy.

Those results do **not** force alignment by themselves. But A1-Prox changes the
quantity to force: rather than aiming immediately at an equal Parikh prefix and
equal next letter, it suffices to force arbitrarily long common legal blocks
between the two fixed rays. Once proximality is obtained, Barge–Zamboni supplies
the strong-coincidence conclusion.

The next proposed lemma is therefore narrower than generic recognizability:

> **Hub proximality lemma.** A closed nonproductive aligned hub component with
> `h(x)=x` and `h(c)=c` cannot keep the two fixed rays uniformly separated.

A proof must use the extra hub/component hypotheses. Primitive minimality alone
cannot suffice, or it would solve the general strong-coincidence conjecture.

## 5. Firewalls and negative controls

- Do not replace proximality by equality of Parikh vectors or by one repeated
  finite germ.
- Do not infer proximality merely because both rays lie in the same minimal
  subshift; minimality does not make arbitrary pairs proximal.
- Do not invoke unimodular Rauzy-fractal tiling conclusions.
- Do not use eventual coincidence transitively through the known good pair.
- The existing productive repeated-germ and non-Pisot strict controls from
  `c4-recognizable-cut-germs.md` remain mandatory.
- A finite common-block census is evidence only; the theorem needs arbitrary
  block length.

## 6. Immediate proof experiment

Decorate the legal ancestry tower of the fixed hub edge by the two actual word
contexts in `u` and `v`, not only Parikh defects. Test the following
candidate statement on retained exact fixtures before promoting it:

```text
recurrent legal hub ancestry state
+ pointwise-fixed endpoint letters
+ closed nonproductivity
=> common-word radius increases under some return of the state.
```

If the increment can be made uniform and positive, iteration gives proximality.
If false, retain the first exact PIP countermodel and identify the missing
finite datum.

The objective is A1-Prox, not another broad strong-coincidence census.

## 7. October 20: inherited block alignment is a load-bearing premise

The [length-window interface](two-obstruction-moment-interface-2026-10-20.md)
isolates the position constraint in the proposed radius-increase experiment.
Inflating the same common block shifts its starts by `1^T M^r delta`, where
`delta` is the preceding Parikh defect. In dimension three, equal starts at
levels `0,r,2r` force `delta=0`, so this inherited block already carries a
strong coincidence. A PIP fixed-ray control has drift `(0,-1,-3)`.
Consequently the proposed recurrence must either prove the balanced prefix
condition or explicitly justify the reselected equal-position occurrences;
word growth alone does not give proximality. This does not refute A1-Prox.

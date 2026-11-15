# Degree-five reciprocal polynomial and image rank — 2026-11-10

**Scope:** completion of the existing signed degree-five image sieve. The
source module is
[`Degree5Completion.lean`](../proof/PscVerif/PscVerif/Degree5Completion.lean).
Acceptance requires Lean elaboration and the whole-bank axiom audit at this
change's exact revision; earlier #528 receipts cover the prerequisites only.
The [targeted stop/go review](c4-degree-five-completion-literature-2026-11-10.md)
was recorded before implementation.

## Hypotheses and conclusion

Keep a supplied normalized ternary `ChildSystem`, `Equiv4` on every state,
primitive incidence, irreducible incidence characteristic polynomial, and a
Pisot root. These are exactly the hypotheses of
`Degree5Sieve.sieve5_of_primitive`; no nonzero image is required. Define

\[
d=\det M,\quad e_1=\operatorname{tr}M,\quad
e_2=\operatorname{tr}(\wedge^2M),\quad
g(X)=X^3-de_2X^2+d^3e_1X-d^5.
\]

For `q5`, the characteristic polynomial of the action on the **actual
rational defect image**, the completion gives

\[
\exists k\in\mathbb N:\qquad q_5=g^k,\qquad
\dim_{\mathbb Q}\operatorname{im}Q_5=3k.
\]

The image can be zero: `q5 = 1` exactly when the entire column map is zero.
An actual nonzero defect column forces `k > 0`. Thus the nonzero image has
rank at least three and divisible by three. Neither the whole signed source
space nor its kernel is substituted for the image in these statements.

## Formal statement map

All names below are in `Psc.Degree5Completion`.

| Declaration | Exact contribution |
| --- | --- |
| `reciprocal_monic`, `reciprocal_natDegree`, `reciprocal_irreducible` | The displayed cubic is monic, has degree three, and is irreducible whenever the original rational incidence cubic is irreducible. |
| `reciprocal_aeval_of_root` | A nonzero incidence root `r` gives the reciprocal root `d²/r`. |
| `eq_pow_of_roots` | A monic rational polynomial whose complex roots lie among the roots of a fixed monic irreducible rational polynomial is a power of that polynomial, including exponent zero. |
| `reciprocal_roots_of_sieve` | Applies the existing degree-five sieve to the actual image polynomial. |
| `q5_eq_pow_rank` | Simultaneously gives `q5 = g^k` and actual image rank `3k`. |
| `columns_eq_zero_iff`, `q5_eq_one_iff` | Vanishing of every representative column, vanishing of the entire linear map, and `q5 = 1` agree. |
| `q5_eq_pow_rank_of_nonzero` | A supplied nonzero representative column implies the exponent is positive. |
| `columns_eq_zero_of_det_bound` | `beta < |det M|³` forces the entire degree-five column map to vanish. |
| `columns_eq_zero_of_nonunit_small_perron` | The explicit specialization `|det M| >= 2` and `beta < 8` forces that map to vanish. |

The Lean statements use `norm beta`; the existing primitive Pisot interface
identifies the Perron value. They keep the same complex-root formulation as
the accepted sieve.

## Derivation

Write `f(X) = X³ - e1 X² + e2 X - d`. Irreducibility of this cubic makes
`d` nonzero. Exact evaluation gives

\[
f(d^2/x)=-\frac{d}{x^3}g(x),\qquad
g(d^2/z)=-\frac{d^5}{z^3}f(z).
\]

A rational root `x` of `g` cannot be zero, because the constant term is
`-d^5`. The first identity would then give a rational root of the irreducible
cubic `f`. Therefore `g` is irreducible. The second identity transports the
incidence roots. The previous sieve identifies every root of `q5` as one of
the corresponding `(2,2,1)` weights, equal to `d²/r` by `d = r0 r1 r2`.

For a nonconstant monic rational polynomial `p` with this root containment,
choose a complex root. Its minimal polynomial is `g`, so `g` divides `p`.
The monic quotient retains root containment and has smaller degree. Induction
therefore yields `p = g^k`; the constant case is `p = 1`. Taking degrees of
the image characteristic polynomial gives the rank identity. This proof
fixes multiplicities without any semisimplicity assumption.

The determinant exclusions are contrapositives of the existing
`Degree5Sieve.det_cube_le_of_nonzero`; they do not introduce a stronger
spectral estimate.

## Controls and replay

- `reciprocal_plastic_control` checks the coefficient signs and
  irreducibility for the plastic incidence: `g = X³ + X² - 1`. This is an
  abstract reciprocal-sector control, not a nonzero actual child image.
- `plastic_zero_image_control` uses the existing empty child system over the
  primitive irreducible Pisot plastic substitution. Its polynomial is `1`
  and its image rank is zero. This is deliberately a zero-image control.
- `reducible_root_containment_control` shows why rational root containment
  alone is insufficient: the roots of `X-1` lie among those of `X³-1`, while
  `X-1` is not a natural-number power of `X³-1`.
- The existing lower-balance, signed-normalization, tensor-transpose,
  characteristic-five and image-kernel controls remain in place. See the
  [degree-five word note](c4-degree-five-2026-11-09.md).

With the repository's pinned Lean setup, the dedicated source replay is:

```sh
cd proof/PscVerif
lake build PscVerif.Degree5Completion
```

The integrated proof-bank import and axiom audit must include this module;
a successful replay of only the older sieve is insufficient. This extension
adds deductive Lean algebra, not a new finite search or executable numerical
kernel.

## Remaining obligations

The optional upper bound `rank Q5 <= 18` still needs the transported
homogeneous-sector decomposition; the finite Lyndon multiplicities alone do
not supply it. The degree-five `StrictSystem` first-defect wrapper, literal
ordered-word realizability and uniform forced-crossing exclusion remain
separate. The maximum-column-sum specialization `beta <= 3` is not added by
this module. General Concentration, C4, G1 and PSC remain open. The
degree-three determinant sector, degree-four configuration (R), higher
first-defect degrees, and the nonzero-`K2` branch retain their existing status.

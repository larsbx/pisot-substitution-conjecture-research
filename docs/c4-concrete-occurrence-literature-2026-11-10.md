# C4 concrete diagonal extraction: literature stop/go

**Decision (2026-11-10): proceed with a narrowed formalization.** This check
precedes the new Lean development. The target is the concrete implication
from an aligned equal-letter occurrence in the one-step inflation of an
irreducible noncoincident balanced parent to a singleton factor and an
interior synchronized newborn cut. It does not assert that any forced
crossing reaches such an occurrence.

## Primary sources inspected

1. M. Barge and B. Diamond, [*Coincidence for substitutions of Pisot
   type*](https://www.numdam.org/item/BSMF_2002__130_4_619_0/), Bulletin de la
   SMF **130** (2002), 619–626. Strong coincidence uses equal letters after
   prefixes with equal abelianization. This is the word-level conclusion
   needed at an aligned tile. The two-letter theorem and the partial
   higher-alphabet result do not furnish the uniform ternary productivity
   premise sought here.
2. S. Akiyama and J.-Y. Lee, [*Algorithm for determining pure pointedness of
   self-affine tilings*](https://arxiv.org/abs/1003.2898), Sections 2.5 and 4.
   Real overlaps require intersecting interiors; a coincidence requires
   matching tile type and position. Potential overlaps are a larger
   computational universe. Thus a boundary touch or a potential graph edge
   cannot silently replace an actual occurrence. The tiling/Meyer hypotheses
   of their global criterion are not supplied by an arbitrary balanced pair.
3. B. F. Martensen, [*A Generalized Balanced Pair
   Algorithm*](https://arxiv.org/html/math/0309194v1), Sections 2, 3.1 and
   3.3. Ordinary population balance and geometric balance agree in the
   irreducible case; reducible examples carry genuine rational length
   relations. Examples 3.3 and 3.5 forbid dropping the irreducibility
   hypothesis when recovering Parikh equality from physical alignment.
   Termination and coincidence remain separate requirements in Theorem 3.10.

## Scope and proof design

The finite-word implication is standard in the balanced-pair/overlap
framework. The contribution is a machine-checked connection to this
repository's concrete `Reduction.red`, `IsBlock`, and `Binomial.subst`
definitions. No new spectral or coincidence theorem is claimed.

The planned proof has two independent parts:

- derive injectivity of a nonzero left eigenrow on rational vectors from
  irreducibility of a rational cubic, using the existing cyclic-vector
  theorem; apply it to the difference of the actual prefix count vectors;
- factor the resulting balanced prefixes, the equal singleton and the
  balanced suffixes with the existing exact reduction theorem. Select the
  singleton's left boundary when it is interior, and otherwise its right
  boundary. Nonerasing inflation of a noncoincident balanced parent has
  length at least two; irreducibility excludes all inherited interior
  zero returns.

Positive tile lengths support common-factor interval transport separately.
This proof development must retain actual occurrence decompositions and
factor ordinals wherever it claims to transport them. A theorem accepting
an arbitrary abstract edge as an occurrence would not discharge that
obligation.

## Negative controls and remaining obligations

Retain [the #530 control](c4-both-end-route-obstruction-2026-11-09.md):
reaching a diagonal need not pass through either alignment of a nominated
good pair. A singleton at the left exterior boundary requires the right
interior boundary and `Sync_-`; endpoint orientation does not determine the
newborn side. Removing irreducibility of the parent can make an interior
return inherited. Removing incidence irreducibility can identify physical
lengths of unequal Parikh columns. An erasing substitution can destroy the
length lower bound.

Proceed also with bounded Quint controls over literal small words for
interior overlap versus boundary touch, repeated factor ordinals, erasure
and singleton parents, and first-diagonal versus nominated-route
quantifiers. Strengthen the existing canonical Mojo addressed replay to
reject a malformed suffix even after a first-diagonal receipt has been
found. These controls test the declared finite contracts and do not replace
the universal Lean deduction.

The uniform existence of a productive forced crossing, complete packet
refinement and consistent lifting of paths, general C4, and global G1
extraction remain separate. No legality hypothesis for arbitrary seeds is
introduced. These boundaries implement the
[next-obligations roadmap](c4-next-proof-obligations-2026-11-10.md).

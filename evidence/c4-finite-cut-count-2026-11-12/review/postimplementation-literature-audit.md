# PR #560: postimplementation finite cut-count contract and literature audit

Date: 2026-11-12. This is a read-only review of the already implemented PR,
not a pre-code gate, a test run, or a theorem-acceptance receipt.

Subject: `31f8046291f2428e839d95e8890c8342858ec210`, tree
`e38c3f65efb79fa72860d8ef222e96695847a551`, in
`/workspace/scratch/f96c28a561ad/psc-count`.

## Decision and chronology

**GO for unchanged full verification of the finite contract.** No correction
to the mathematical statements was identified. The implementation proves an
elementary finite counting interface and binds it to the named substitution
and existing compact-neighborhood theorem. It does not establish a lattice
asymptotic, positive Haar measure, overlap coincidence, or the Pisot
substitution conjecture.

The research-design chronology needs an explicit qualification. `AGENTS.md`
requires a targeted literature check before new theorem-facing implementation.
The earlier compact-neighborhood gate approved a topological transfer and left
the fixed-origin lattice count and original strict-cut density as separate
obligations. Its archived
`next-count-plan.md` expressly proposed the new modules after a fresh targeted
gate; `next-count-interface-review.md` marked its interfaces proposed and
uncompiled. They provide substantial design and source-interface preparation,
but they are not a recorded three-to-six-source pre-code gate for this
increment. PR #560's short note cites that lineage without supplying such a
gate. This review therefore records a **post-code contract/literature audit**;
it cannot repair chronology by retroactive relabeling. A documentation
clarification should preserve that distinction. There is no reason from this
audit to repeat or enlarge the mathematical implementation before running the
unchanged acceptance gate.

## Exact reviewed contract

Write `bs = red u v`, assuming `Equiv1 u v`. For each `j : Fin bs.length`,
the implementation takes the integer Parikh vector of the concatenated top
factors strictly before occurrence `j`. Its finite set `Z` is the image of
these occurrence indices. Thus:

1. Nonempty top factors make ordinary prefix lengths strictly increasing.
   Equal integer Parikh vectors imply equal ordinary lengths, so the map from
   occurrences to vectors is injective and `Z.card = bs.length`.
2. Complete reduction reconstructs both words. Each selected occurrence has
   literal top and bottom `Mark` witnesses, including the following letter and
   suffix, whose prefix Parikh vectors both equal the selected integer vector.
3. If every reduced top factor has physical length at most `L`, finite
   additivity gives `physicalLength ℓ u ≤ L * (Z.card : ℝ)`.
4. Positive letter weights place each selected vector in the original
   half-open strip `0 ≤ offset ℓ z < physicalLength ℓ u`.

For a named fixture, a supplied fixed strict carrier `C`, a source `T ∈ C`,
and the same uniform carrier bound `L`, `integerStarts fixture n T` applies
this construction to the actual words at power `12*n`. Its strip length is

\[
X_n=\beta^{12n}\operatorname{physicalLength}_{\mathrm{physicalRow}}(T.1).
\]

`integerStarts_count_and_strip` supplies `X_n ≤ L * card Z_n` and the strip
membership of these same integer vectors. `eventually_integerStarts_mem`
uses their actual marks to invoke the previously proved named capture
theorem. For an open `U` containing the exact `carrierOverlap fixture C`,
one threshold works for all later `n`, all `T ∈ C`, and all `z ∈ Z_n`.
The carrier overlap is the existing union over represented strict letter
pairs; the adapter does not substitute an unrelated or enlarged label set.

This source review finds nine public theorem declarations, three private
proof helpers, and three definitions across `StrictCutCount.lean` and
`NamedCutCount.lean`. These are source counts, not compiled-audit counts.

## Six primary sources and what transfers

### 1. Martensen: balanced-pair reduction and multiplicity

Brian F. Martensen, [A Generalized Balanced Pair Algorithm](https://arxiv.org/abs/math/0309194),
[primary PDF](https://arxiv.org/pdf/math/0309194), §§2 and 3.1, printed
pp. 2–4; compare the density discussion surrounding Theorem 3.10 on pp. 7–9.
The paper uses population vectors, substitution of balanced pairs, and
reduction into irreducible balanced pairs. Its terminating algorithm has a
finite set of pair types; occurrences in a reduced word still retain
multiplicity. It also discusses physical lengths from a positive length
vector and a Perron left eigenvector. This supports the terminology and the
finite additive setup. The later frequency/density argument uses additional
dynamical input; neither that argument nor generalized length-based
equivalence is imported by this PR. The repository retains full integer
Parikh equality.

### 2. Barge–Diamond: coincidence retains the following letter

Marcy Barge and Beverly Diamond,
[Coincidence for substitutions of Pisot type](https://www.numdam.org/articles/10.24033/bsmf.2433/),
[primary PDF](https://www.numdam.org/item/10.24033/bsmf.2433.pdf),
pp. 619–621, especially the definition and Theorem 1. Coincidence requires
both matching following letters and equal abelianized prefixes. Thus a
balanced prefix alone is not a coincidence witness. Their theorem gives
some pair of distinct letters in general alphabet size and settles the
two-letter consequence; it is not an all-pairs ternary theorem. The lattice
strand description retains original ordered word prefixes. The PR correctly
constructs full marks and passes their actual labels through the strict
carrier adapter. It claims no new coincidence theorem.

### 3. Minervino–Thuswaldner: physical digits and the nonunit setting

Milton Minervino and Jörg M. Thuswaldner,
[The geometry of non-unit Pisot substitutions](https://arxiv.org/abs/1402.2002),
[primary PDF](https://arxiv.org/pdf/1402.2002), §§2–4, particularly §4.1,
Proposition 4.1 and Definition 4.2. Physical prefix digits are obtained by
pairing the population vector with a Perron left eigenvector; prefix
automata retain actual prefix/letter/suffix information. The nonunit
representation includes non-Archimedean components. These facts agree with
the chosen additive physical coordinate and the need to retain the full
ambient model. Their numeration limits and geometric conclusions do not
identify the repository's model automatically and are not invoked to infer
cardinality or measure from a finite collection of prefix digits.

### 4. Akiyama–Lee: the direction and hypotheses of coincidence transfer

Shigeki Akiyama and Jeong-Yup Lee,
[Overlap coincidence to strong coincidence in substitution tiling dynamics](https://arxiv.org/abs/1403.0377),
[primary PDF](https://arxiv.org/pdf/1403.0377), §2.3, §3, Theorem 4.1 and
Corollary 4.2. The transfer assumes a self-affine tiling with Meyer return
vectors, admissible control points, and a specified generated-group
condition; trivial height supplies a sufficient group condition. Its
direction is from overlap coincidence to strong and simultaneous
coincidence. The proof's density limit has its own dynamical hypotheses.
These conditions are not supplied by the finite start count or open-set
capture, so this PR does not obtain a spectral or overlap result by citing
that transfer.

### 5. Akiyama: the converse needs a stronger coincidence premise

Shigeki Akiyama,
[Strong coincidence and overlap coincidence](https://arxiv.org/abs/1509.04471),
[primary PDF](https://arxiv.org/pdf/1509.04471), §3, Theorem 3.2,
Corollary 3.3 and Remark 3.4. The equivalence is with multiple strong
coincidence at a suitable level, quantified over admissible control-point
choices satisfying a group condition. The general tiling theorem also
requires connected tiles, the non-rod condition and Meyer return vectors.
The Pisot suspension corollary does not replace multiple strong
coincidence by one finite witness. This bounds what could follow later from
the current strict-cut analysis; no such converse is used in either new
module.

### 6. Mathlib: finite image cardinality requires injectivity

Primary [Mathlib `Finset.Card` documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html#Finset.card_image_of_injective),
especially `card_image_of_injective` and `card_image_iff`.
The image cardinality equals the domain cardinality under injectivity;
arbitrary image formation only gives an upper bound. The new proof supplies
the injectivity premise before applying this API. The project manifest pins
Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`; a read-only check of the
available source cache found the same declaration and premise. This is an
API/source check, not a replacement for compiling against the checked-in
manifest and auditing the exact revision.

## Hypotheses and negative boundaries checked

| Boundary | Concrete reason | What the implementation does |
|---|---|---|
| Factor occurrences versus factor types | Two equal nonempty factors occur at two different prefix lengths even though the set of labels has one member. | Indexes by `Fin bs.length`; `repeated_factor_control` has cardinality two. Its abstract sample need not itself be a balanced reduction. |
| Nonempty top factors | In a list containing two empty top factors, their starts coincide at zero. | Requires nonempty tops for injectivity; obtains them from `red_isBlock` for balanced input. |
| Finite index domain | On all naturals, `take j` is constant after the list ends. | Uses `Fin bs.length`, not an all-natural injectivity assertion. |
| Complete balanced input | A partial list of balanced blocks need not reconstruct an arbitrary original pair. | Requires `Equiv1 u v` and uses the complete top/bottom reconstruction identities. |
| Proper marks and the terminal point | The terminal prefix has no following letter and lies at the excluded strip endpoint. | Counts factor starts only; the empty factor list contributes no zero point. `empty_startVectors` states this explicitly. |
| Strict physical upper endpoint | A zero length for every letter makes a nonempty word have total length zero, so its initial point cannot satisfy `0 < total`. Negative weights also need not produce a nonnegative strip coordinate. | Requires strictly positive letter weights for the strip theorem; the named row supplies them. |
| Sign in the finite sum bound | Replacing equal cardinality by a larger cardinality would need `L ≥ 0` for the multiplication step. | Uses exact cardinality equality, so the generic finite sum theorem correctly needs no sign premise on `L` or `ℓ`. |
| Exact labels and uniform threshold | A threshold for one source or pair does not automatically work for infinitely many moving sources. | Uses the fixed finite strict carrier and its existing represented-pair overlap; the open set is fixed before the threshold. |
| Integer count versus internal image count | Counting an image requires a separate injectivity argument if the image map is used for cardinality. | Keeps `Z_n` in integer Parikh space; `ambientStar` is used only for membership in `U`. |
| Conditional finite estimate versus asymptotic mass | A supplied finite factor bound and eventual open-set membership do not supply lattice occupancy finiteness or a normalized counting limit. | Leaves lattice count, covolume, all-depth cylinder masses, regular outer covers, and positive Haar measure open. |

The counterexamples in this table delimit weaker abstract hypotheses. They
are not asserted to be counterexamples within the standing primitive,
irreducible Pisot substitution regime. Only the repeated-factor and
empty-list rows describe new formal controls already present in these
modules; the other rows are contract analysis, not newly compiled controls.

## Standard argument versus repository contribution

The strictly increasing prefix-length argument, finite additive sum bound,
and positivity argument for proper prefixes are standard elementary facts.
They require no new Pisot-specific analytic theorem. The useful repository
work is binding those facts to complete reduction, literal occurrence
marks, strict carrier closure, the named physical row and its exact power
scaling, and the existing uniform compact-open capture theorem.

The named public theorem accepts a carrier bound `L`; this PR does not
export a separately constructed positive maximum, a theorem that `X_n`
tends to infinity, or a normalized asymptotic lower density. Such adapters
may be useful later, but their absence does not weaken the stated finite
contract. The next analytic step still needs its own exact fixed-origin
lattice counting statement and measure normalization. No stronger claim
should be attached to this verification run.

## Verification disposition

Proceed with the unchanged isolated gate at the subject revision and
inspect the actual compiled declaration/axiom audit when it completes.
This review ran no tests or builds, changed no repository file or HEAD,
and records no full-gate pass, hosted-check success, or independent human
review. Preserve the postimplementation timing in the eventual report and
append-only side ledger.

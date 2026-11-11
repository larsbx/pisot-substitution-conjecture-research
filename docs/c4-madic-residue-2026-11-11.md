# C4: the actual matrix-adic carrier and its occurrence-residue bridge

The [pre-code source gate](c4-madic-residue-literature-2026-11-11.md)
approves this construction after the
[local incoming-admissibility interface](c4-local-admissibility-2026-11-11.md).
The introducing pull request records the exact accepted revision and the
observed Lean, native, oracle, and governance receipts. A source-level
development compile is not the canonical complete Lean/axiom audit.

**Advance:** the residue carrier is now constructed as the actual inverse
limit of integer image-lattice quotients. Its first coordinate proves the
integral lifting property previously left as a premise. Its matrix action
is injective when the integral action is injective, and its topology is
proved compact for an injective endomorphism of a finite free integer
module. These facts are connected to the existing literal incoming-cover
theorems on a product with a supplied stable factor.

The compact tiles themselves are still supplied sets. Their authentic
prefix realization and complete literal tile equation are not constructed
by this step. A finite ancestor-domain completeness theorem, nonunit
product-Haar scaling, a measure recurrence, and strict-cut positivity are
not supplied. C4, global G1, Concentration, and general PSC remain unproved;
[issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
remains open. No governed claim status is promoted.

## 1. The actual carrier

The generic Lean construction in
[`MadicResidue.lean`](../proof/PscVerif/PscVerif/MadicResidue.lean)
starts with an additive commutative group `V`, with its canonical
integer-module structure, and an integer-linear endomorphism `M`. Put

\[
L_q=\operatorname{range}(M^q),\qquad Q_q=V/L_q.
\]

The inclusion `L_n <= L_m` for `m <= n` gives an actual quotient map
`reduction M h : Q_n -> Q_m`. The carrier is the submodule

\[
H_M=\{x\in\prod_{q\geq0}Q_q:
       r_{n,m}(x_n)=x_m\text{ whenever }m\leq n\}.
\]

The quotient at depth zero is trivial. The construction uses the column
image of the endomorphism; it does not replace an image lattice with the
row span of a matrix representation. All quotient equalities are proved
against the actual image submodule:

\[
[z]_q=[w]_q\quad\Longleftrightarrow\quad
\exists y,\ M^q y=z-w.
\]

Define the canonical integral map, coordinate maps, and induced action by

\[
\iota(z)_q=[z]_q,\qquad \rho_q(x)=x_q,\qquad
(Tx)_q=\overline M_q x_q.
\]

These are integer-linear maps, constructed on the compatible tuples.
The reduction maps commute with the quotient actions. Lean proves

\[
T\iota(z)=\iota(Mz),\qquad
\rho_q(\iota z)=[z]_q,\qquad
\rho_q(Tx)=\overline M_q\rho_q(x).
\]

Every coordinate map is surjective: lift a representative through `iota`.
There is no assertion that one finite coordinate determines a coherent
tuple or an integral vector.

### The canonical map is not assumed injective

The exact theorem is

\[
\iota(z)=0\quad\Longleftrightarrow\quad
\forall q,\ z\in M^qV.
\]

For an invertible integer matrix every quotient is trivial. For
`diag(2,1,1)` on `Z^3`, both unchanged coordinate axes are in the kernel
of `iota`. The term *canonical map* is therefore intentional. An embedding
claim requires an additional separation argument.

## 2. Integral lifting is now a theorem of this carrier

At the first coordinate,

\[
\rho_1(Tx)=0,\qquad
\rho_1(\iota z)=0\quad\Longleftrightarrow\quad
\exists y\in V,\ My=z.
\]

The first equality is quotient annihilation by the image of `M`; the
second is the exact kernel property of the quotient. Consequently

\[
\boxed{(\exists x\in H_M,\ Tx=\iota z)
       \quad\Longleftrightarrow\quad
       (\exists y\in V,\ My=z).}
\]

The forward direction takes the first residue. For the reverse direction,
an integral solution supplies `x=iota(y)`. This equivalence needs neither
injectivity nor finite quotients, compactness, or a tile equation.

At every depth there is also the exact annihilation theorem

\[
\rho_q(T^q x)=0.
\]

The module does not need the stronger identity
`range(T) = kernel(rho_1)` for arbitrary coherent tuples. Its integral
preimage equivalence suffices for the occurrence-cover interface.

### Why the full action can be injective

Assume `M` is injective. If `Tx=0`, choose a representative `u` of
`x_(q+1)`. The vanishing coordinate says

\[
Mu\in M^{q+1}V=M(M^qV).
\]

Cancel `M` to get `u in M^qV`. Reduction and compatibility give `x_q=0`.
This works for every `q`, proving `x=0` and hence injectivity of `T`.

The proof uses the next coordinate. The action on a single finite
quotient can have a nontrivial kernel, and its `q`th power is zero at
depth `q`. A finite-level injection assertion would invalidate the
argument for the intended nonunit examples.

## 3. Compactness and continuity

Suppose `V` is a finite free integer module and `M` is injective. The
range of `M^q` has the same rank as `V`; Mathlib's equal-rank quotient
theorem therefore proves that every `Q_q` is finite.

Each quotient receives its discrete topology. The product is compact and
Hausdorff. Each compatibility equation is an equality between continuous
coordinate maps, so the compatible tuples form a closed submodule.
`carrier_compactSpace` proves compactness of this actual carrier.
Hausdorffness and the topological additive-group structure are inherited
from the product. `continuous_eval` and `continuous_action` prove
continuity of the coordinate maps and `T`.

For `V = Fin 3 -> Z`, finite freeness is available directly. Nonsingularity
is used through injectivity of the integral linear action. The algebraic
construction remains meaningful for singular endomorphisms, but the
injectivity and compactness conclusions are not asserted there without
their hypotheses.

Only the matrix-adic factor is proved compact. A product with an
unbounded stable vector space is not thereby compact, and no tile
boundedness or Haar-measure conclusion follows from this carrier theorem.

## 4. Connection to actual inverse occurrences

The application module
[`OccurrenceResidue.lean`](../proof/PscVerif/PscVerif/OccurrenceResidue.lean)
uses the actual integral incidence action of the supplied substitution.
Let `E` be an additive commutative group, `B : E -> E` additive, and
`pi : Z^3 -> E` additive. On

\[
G=E\times H_M
\]

define

\[
A(e,h)=(Be,Th),\qquad
\star z=(\pi z,\iota z).
\]

The residue detector ignores the first coordinate. It proves
`ReflectsIntegralRange` for this concrete product action and translation
map. It is no longer an unspecified ambient lifting assumption.

For the full incoming-cover conclusions, also supply

\[
B\text{ injective},\qquad M\text{ injective},\qquad
B(\pi z)=\pi(Mz),
\]

and the complete literal tile equation for the sets `K_a` in this product.
The existing occurrence-piece identity then identifies every selected
integral paired piece using the same two actual marks. The existing
incoming-cover and history-cover theorems give the all-integral cover and
the cover at every prescribed finite depth.

Nonintegral paired pieces in this **constructed carrier** are empty by
the first-residue theorem. This does not contradict the previous finite
cyclic countermodels: those models did not have this carrier's exact
integral residue detector. An application to independently defined
geometric tiles must still establish their representation in this carrier
with the stated action and translation maps.

The conclusion is an incoming cover. It does not prove forward closure.
It also does not put every nonempty ancestor in a particular finite
constructor. Restriction to a supplied finite domain keeps the existing
nonempty-ancestor representation or exact retained-union hypotheses.

## 5. Complete literal block profiles

For the genuine iterated image words `iterateImages s q`, retain every
marked decomposition

\[
s^q(a)=P\,c\,S.
\]

Its finite profile is the set image of the complete incoming-digit type:

\[
F_{c,q}=\{[v(P)]_q:s^q(a)=P\,c\,S\},
\]

where `v(P)` is the integer Parikh vector. The incoming-digit type keeps
the parent letter and the full mark. Taking this set image may identify
equal residues, but never changes the occurrence inventory used by a
counting argument.

Supply the complete block tile equation

\[
K_c=\bigcup_{s^q(a)=P c S}(A^qK_a+\star v(P)).
\]

Because `rho_q(A^q x)=0`, Lean proves

\[
\boxed{\rho_q(K_c)\subseteq F_{c,q}.}
\]

No compactness, injectivity, measure, or nonemptiness premise is needed
for this enclosure once the block equation and annihilation are supplied.
Equality holds if every contributing ancestor tile is nonempty. Without
that premise a listed digit can come from an empty ancestor, so the
complete literal profile is only an outer bound.

The block tile equation is an explicit premise of this application.
The module does not silently infer it from a fixed-point period or an
unproved original-to-block iteration theorem. The existing theorem
`incidenceZ_iterateImages` binds these literal words to the powered
incidence matrix. Authentic prefix-tile equations may require a depth
divisible by the fixed-point period, as in the November 4 written bridge.

### Sound exclusions and inconclusive profiles

For `p=(i,j,z)`, separation of `F_(i,q)` from the translate
`F_(j,q)+[z]_q` proves `K_i intersect (K_j+star z)` empty, using the
authenticated enclosure. A nonempty projected intersection proves
neither a genuine intersection nor positive measure.

The same enclosures and commuting residue action are suitable inputs to
the previous paired-profile exclusion theorem. For an integral inverse
occurrence, excluding its ancestor overlap excludes its affine piece.
Every omitted candidate still needs a sound reason for exclusion or a
proved containment in the retained union. A resource cap is a refusal,
not a geometric exclusion.

The existing cylinder verifier's zero-area calculation includes boundary
contact. It cannot substitute for set emptiness. A measure-zero argument
would need a separately authenticated measure interpretation.

## 6. Bounded native certificate and independent oracle

The canonical implementation is
[`kernel/psc/c4_madic_residue.mojo`](../kernel/psc/c4_madic_residue.mojo),
with a driver and contract tests. The independent implementation is
[`oracles/python/c4_madic_residue.py`](../oracles/python/c4_madic_residue.py).
The introducing PR records the final packet digest, exact finite inventory,
accepted tests and refusal controls.

The finite certificate uses the actual column lattice `M^q Z^3`. It
enumerates quotient classes by deterministic positive-basis traversal,
using exact adjugate residue keys and checked arithmetic. The traversal
must exhaust every generator extension and agree with the exact lattice
index. It records complete quotient operations, reductions and induced
actions, as well as the actual inflated words and every selected position.
The independent oracle reconstructs the finite object using permutation
determinants and exact Cramer divisibility, rather than trusting the
native quotient labels or aggregate totals.

Every record is checked, including repeated literal marks with the same
residue. Missing, duplicated, reordered, substituted or unknown records
must fail. A conservation identity alone does not establish correct
residue placement. Accepted finite levels do not identify an infinite
coherent state or certify a compact tile equation.

The fixed protocol is `c4-madic-residue-v1`. Its declared inventory is
four fixtures, 17 quotient levels, 139 classes, and 333 literal
occurrences. Full source words plus the parent/position pair determine
the actual prefix and suffix; their Parikh vectors are checked fields,
not replacements for the literal address.

| Fixture | Substitution | All emitted levels |
| --- | --- | --- |
| Named nonunit | `1/021/001` | `0..4` |
| Same incidence, different literal order | `1/012/001` | `0..4` |
| Unimodular control | `01/02/0` | `0..3` |
| Mandatory doubled-letter control | `00/11/22` | `0..2` |

The general bounded builder requires three nonempty images of length at
most three and depth at most six. At each level it permits at most 64
quotient classes, 192 basis-extension candidates, 729 letters per source
word, and 2,187 literal occurrences across the three source words.
Each limit refuses the whole requested construction. The final traversal
must process all `3 * index` candidates even after it has discovered all
class representatives. Separate regression coverage reaches the named
depth-six quotient of index 64; it is not an extra level in the fixed
driver packet. The exact native packet digest and observed control results
belong to the revision-bound replay receipt.

Required boundaries include:

- `1/021/001` at depth two has quotient invariants `(1,2,2)` and group
  `Z/2 x Z/2`, not `Z/4`.
- A finite quotient action can have a kernel while the inverse-limit
  action is injective.
- Translation sign is checked in the named depth-three quotient, where
  `[e0]` has order four: `F_0 intersect (F_0+[e0])` is class set `{3}`,
  while `F_0 intersect (F_0-[e0])` is `{2}`. An exponent-two control
  alone could not distinguish those signs. These are projected set
  identities, not actual compact intersections.
- For `2I`, a nonzero displacement `2^q e0` has zero residue at depth `q`
  and nonzero residue at depth `q+1`; a truncated zero is not all-depth
  vanishing or integral equality.
- Unit quotients are trivial and give no residue separation. The finite
  constructor refuses singular incidence; this does not invalidate the
  more general algebraic definition.
- Equal projected prefixes retain distinct parent/position records.
- The mandatory inverse-closed but forward-leaking `00/11/22` example
  remains a physical calibration. Across its two sources, the receipt is
  `full=4, retained=2, positive_exits=2`. Per source, four positional
  pairs comprise one retained positive pair, one positive exit, and two
  outside pairs with zero physical calibration mass. These numbers are
  never compact-overlap Haar measures.

## 7. Replay and acceptance boundary

From the repository root, the canonical deductive gate is:

```bash
./tools/check_lean.sh
python tools/make_proof_bank.py --check
```

For the locked native implementation and its independent replay:

```bash
(
  cd kernel
  pixi install --locked
  export MODULAR_HOME="$PWD/.pixi/envs/default/share/max"
  export MODULAR_TELEMETRY_ENABLED=0
  .pixi/envs/default/bin/mojo run -I . tests/test_c4_madic_residue.mojo
  .pixi/envs/default/bin/mojo run -I . c4_madic_residue.mojo > /tmp/c4-madic-native.txt
)
C4_MADIC_RESIDUE_NATIVE=/tmp/c4-madic-native.txt \
  python -m pytest --assert=plain -o addopts='' -q tests/test_c4_madic_residue_oracle.py
python -O oracles/python/c4_madic_residue.py \
  --native-output /tmp/c4-madic-native.txt --output /tmp/c4-madic-receipt.json
```

The [dedicated workflow](../.github/workflows/c4-madic-residue.yml) binds
the exact head, tree, clean initial checkout, and source digests before
execution, rechecks them afterwards, and uploads the full native packet
and oracle receipt. The complete canonical Lean/axiom audit is separate.
The finite numerical fixtures are native/oracle checks, not closed Lean
evaluations of a parsed native certificate.

## 8. The remaining authentic geometric bridge

The missing realization theorem must now supply the intended compact
prefix sets in `E x H_M`, identify their action and integral translation
map, and prove their complete literal occurrence tile equation at the
appropriate original or block scale. An alternative route can authenticate
a map from another geometric model that intertwines action and translations
and provides the needed enclosures; the original tile equation remains
explicit for the incoming-cover conclusions.

Once this realization is established, the new residue detector discharges
integral lifting, and complete block-prefix inventories give actual support
enclosures. It still takes separate geometric arguments to prove that a
particular finite ancestor constructor represents all nonempty pieces,
to justify stable-coordinate exclusions, and to establish the product-Haar
recurrence and positive overlap measure needed at strict cut roots.

The finite quotient operations, the infinite carrier theorems, the supplied
tile equation, and those remaining geometric obligations have distinct
quantifiers. None is credited as proof of the others.

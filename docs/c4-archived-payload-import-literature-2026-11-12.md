# Archived paired-overlap payloads: kernel import gate

Decision recorded on 2026-11-12 (UTC): **proceed with a narrowed, proof-producing
import of the two original archived graphs.** The baseline is
`06dac7ea4e83a6b5a2c7c36bfe84cfec75da3903`, the merge of #550. Its accepted
proof head is `1c0687241cf2f4103b24166a2024fb917f6e8185`.

This note precedes new theorem-facing implementation. It follows inspection
of `AGENTS.md`, the append-only side-notes ledger, the
[previous mathematical source gate](c4-archived-graph-refinement-literature-2026-11-11.md),
the accepted `NamedArchivedGraph` interfaces, and the existing concrete
`OverlapPacket` decoder. It is a research-design decision, not an assertion
that the proposed import has already compiled or that independent human
review has occurred.

## Exact proposed claim

For each fixed original source, reify its preserved states, full positional
slots, discovery witnesses and positive integer potential as concrete Lean
data. Prove that an accepted finite decoder constructs all of the following
objects for those same data:

1. `TableBinding (iterateImages (substitution fixture) 2) states cert`, with
   orbit-distinct states and exact literal rows;
2. `DecodedCandidatesClosed fixture states`, quantifying over every selected
   parent/local occurrence pair from every stored state, including candidates
   not already listed in the payload;
3. the three exact root IDs and `rootBound`, together with earlier-ID
   `TableDiscovery table.row ArchivedRoot`;
4. `cert.check = true`, `cert.numerator = archivedNumerator fixture` and
   `cert.denominator = 20` for that identical degree/target function.

The original source-specific sizes and rates stay fixed:

| Fixture | Substitution | States | Positional edges | Rate |
| --- | --- | ---: | ---: | ---: |
| 0 | `1/021/001` | 7,150 | 34,826 | `99/20` |
| 1 | `1/012/001` | 7,083 | 34,853 | `101/20` |

When these concrete proof terms have passed the required acceptance checks,
apply the existing `rooted_nonempty_domain_iff`,
`original_roots_null_of_table` and `all_original_ancestors_null_of_table`.
The resulting nullity is for the original named rooted inverse ancestry and
the actual product of stable volume with a probability additive Haar measure
on the existing matrix-adic factor. It does not quantify over all
noncomputable `strictPackets` merely because their carrier is finite.

## Primary sources and transferable conclusions

Three fresh Lean sources address the new implementation boundary. The three
mathematical sources in the preceding gate retain their previously recorded
scope; the present step proposes no new tiling or spectral criterion.

1. **Lean Language Reference, pinned version `4.34.0-rc2`, section 14.5.18
   and section 14.5.19**, [official reference](https://lean-lang.org/doc/reference/4.34.0-rc2/Tactic-Proofs/Tactic-Reference/).
   `decide +kernel` performs kernel reduction, while `native_decide` uses
   compiled evaluation and adds an axiom. The reference also documents
   reduction obstructions from well-founded recursion and dependent casts.
   Its proof-producing `cbv` alternatives may be considered if needed, but
   any such change must pass the same compiled axiom audit. Performance
   difficulty does not authorize changing the accepted axiom boundary.
2. **Lean implementation at the exact toolchain tag**, inspected directly:
   [`src/Lean/Elab/Tactic/Decide.lean`](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/Elab/Tactic/Decide.lean),
   Git blob `929dd0a01dc12e7df21860ef791f6a2cf2a038c0`, and
   [`src/Lean/Meta/Native.lean`](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/Meta/Native.lean),
   Git blob `890d6e446ffff269d98078b436b569134f172ae0`.
   `evalDecideCore.doKernel` submits an auxiliary proof lemma for kernel
   checking; `nativeEqTrue` compiles and evaluates a Boolean, then inserts a
   fresh `Declaration.axiomDecl`. Consequently, a grep only for the older
   name `Lean.ofReduceBool` is insufficient. Audit the complete transitive
   axiom set against the existing allowlist, including generated concrete
   acceptance declarations and their consumers.
3. **Theorem Proving in Lean 4, chapter 12, Axioms and Computation**, [official
   text](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/).
   Classical existence can provide mathematical objects without executable
   data, and proof-dependent casts can obstruct kernel normalization. This
   supports keeping the payload checker computational and proving a
   separate soundness theorem into the geometric interface. A noncomputable
   finite carrier is not an executable enumeration or a source-bound graph
   decoder.

The carried mathematical conclusions are from **Akiyama--Lee**, [section 4
of the primary preprint](https://arxiv.org/pdf/1003.2898), on complete
occurrence multigraphs and the extra tiling/Meyer hypotheses in their
spectral equivalence; **Minervino--Thuswaldner**, [Lemma 3.1 and Theorem
8.3(i)](https://arxiv.org/pdf/1402.2002), on nonunit representation and product
scaling; and **Thuswaldner**, [Lemma 3.4, Definition 3.6 and Remark
3.7](https://www.numdam.org/item/JTNB_2006__18_2_487_0.pdf), on finite bounds,
rooted closure and ordering in a unimodular setting. Their hypotheses and
nontransfers are detailed in the previous gate. No new identification of the
repository's determinant-two compact representation with those other
spaces, no pure-point equivalence, and no strict-root positivity is imported.

Proof by reflection, checking externally found witnesses, and splitting a
finite check into proved exhaustive chunks are established techniques. The
new contribution sought here is their checked specialization to these exact
archived payloads and the already proved original geometric domains.

## Existing project construction to reuse

At the baseline, [OverlapPacket.lean](../proof/PscVerif/PscVerif/OverlapPacket.lean)
already provides balanced `Table` data, a checked layout, and
`Table.get?_eq_toList`. Its `Nat.allLTTR` checker has a soundness equivalence;
`checkRange_append` and `valid_of_range` permit exhaustive chunked kernel
checks. `toCertificate` preserves every target-list entry and uses proved
target bounds instead of reducing malformed indices modulo the state count.
Reuse these definitions where their types fit, or prove the necessary
source-specific extension against them. Avoid a duplicate unverified table
or range-checking infrastructure.

That earlier `Packet` is specifically the later 18-source import. Its
header admits source numbers below 18, its state field is formatted text,
and its row inequality and certificate numerator fix `102/20`. It contains
neither full parent/local addresses nor a proof of candidate completeness.
It cannot be relabelled into the original `(16,8)` graphs. The new
source-specific decoder must retain the original rates and supply the
missing semantic fields and proofs.

[replay_overlap_lean_packets.py](../tools/replay_overlap_lean_packets.py)
also supplies a reusable acceptance protocol: compile generated source,
import it freshly, type-check the acceptance theorem against the actual
checker, collect transitive axioms, emit the data and compare the full
emitted packet with the independent reconstruction. Hashes bind the
archival artifacts and byte comparison binds the emitted data; neither
alone proves literal geometric refinement. The decoder soundness theorem
and concrete kernel-accepted check supply that mathematical connection.

## Obligations the checker must actually discharge

- **Literal source and box.** Bind each fixture to the unchanged substitution
  and its actual squared words. Use the already authenticated sharp
  `(16,8)` enclosure and rational exclusion predicate. Keep the `(24,12)`
  artifact separate. A guessed smaller enclosure or changed metadata is
  not an additional exclusion theorem.
- **Occurrence and orientation.** Decode both parent letters, both local
  positions, the integral offset and the target-swap flag. Prove each slot's
  literal inverse equation and exact source/target relation. The swapped
  affine translation remains `current.delta + bottomPrefix`; the unswapped
  translation remains `topPrefix`. Equal endpoints retain their separate
  positional slots.
- **Complete rows and justified rejection.** Exhaust the complete finite
  selected-pair type for each source state. A pair is excluded only through
  the proved exact matrix-adic residue failure or strict box separation;
  contact at the boundary is retained. Prove that every admitted decoded
  candidate occurs in the ordered lift and that each required literal
  occurrence occurs exactly once in its row. Checking only supplied edges
  would leave the central completeness premise unproved.
- **State identity and ancestry.** Prove orbit distinctness, both ordered
  orientations, the three zero-offset roots and genuine earlier-ID
  discovery edges. Discovery establishes reachability of stored states;
  exhaustive candidate closure supplies completeness in the other
  direction. Neither premise substitutes for the other.
- **One graph for geometry and arithmetic.** The row slots in `TableBinding`
  and the potential sum in `Certificate` must share the same indexed degree
  and target functions. Bounds, positive weights, the exact rates and every
  repeated slot are checked. Any finite lookup accelerator or witness map
  must be proved faithful to the actual table, not trusted because its
  native implementation succeeded.
- **Exhaustive computation.** Reuse balanced lookup and compositional
  finite ranges to control reduction cost. Prove the range partition covers
  every index, without skipped endpoints or duplicated ranges standing in
  for missing rows. If computation exceeds resources, preserve the failure
  and retain the outstanding proposition. Do not fall back to a native axiom
  or weaken the completeness quantifier.

## Negative controls and exact acceptance

Retain the existing native/oracle mutations for an omitted repeated
positional edge, a reversed inverse equation, a wrong swap, a wrong box,
an incomplete inverse ancestor and a graph/source/domain mismatch. The
omitted-edge control must continue to show why an easier numerical
inequality is not sufficient. Add direct Lean controls on the new checker
for those same semantic classes where a small exact payload exposes the
failure. Keep the exact-residue control whose odd right-hand side is still
in the matrix image; componentwise parity is not the criterion.

Import-specific controls must refuse malformed target IDs, a false table
layout, hidden or truncated packed fields, incomplete check ranges, zero
weights and changed numerator/denominator. The replay protocol must reject
an acceptance declaration proving `True` instead of the actual checker
equality, an emitted payload different from the checked one, and any
transitive axiom outside `propext`, `Classical.choice`, `Quot.sound`.
These controls supplement the generic soundness proofs; they do not prove
full completeness by sampling.

Acceptance requires the canonical Mojo export and independent Python oracle,
complete concrete Lean checks, the unchanged isolated full-source build and
compiled axiom audit, and retained exact-revision receipts. Record the
generated source and payload digests, original and addressed graph digests,
toolchain/Mathlib pins, exact commands and failed attempts. A development
probe or successful generic checker theorem alone does not count as
acceptance of either 7,150- or 7,083-state payload.

## Decision and remaining scope

**Proceed with the concrete import.** The finite obligations are now sharply
specified and reuse an existing checked packet-evaluation pattern. If a
particular concrete obligation cannot be compiled and audited, retain it
explicitly and report that narrower result. Do not describe the finite
connection as complete until the actual payload has all required proof
terms.

Even successful import will establish the stated original rooted-domain
representation and its product-Haar nullity. It will not identify that
domain with all noncomputable strict packets, establish positive strict-root
measure, produce forward conservation from inverse closure, or promote C4,
BH, A1', G1, Concentration or the general PSC. Those boundaries survive the
removal of the finite-payload hypotheses.

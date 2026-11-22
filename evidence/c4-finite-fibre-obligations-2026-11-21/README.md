# Acceptance of the next finite-fibre obligations

This receipt covers the [finite-fibre continuation](../../docs/c4-finite-fibre-obligations-2026-11-21.md)
after draft PR #649's automaton/hull witness tree, integrated with main
`bbe0640dcef2520d57532a1a9e301b35ed97fc1f`.

## Exact accepted scope

- **76 project library modules** were rebuilt from current repository
  sources in an initially empty project-output directory.
- **Eight audit fixtures** passed. Their 84 combined source hashes,
  commands, exits and compiler output are preserved in the receipts.
- The four new audits cover **16 added modules, 159 owned declarations,
  143 theorem constants, 102 independently stated endpoint types and
  owners, and 222 refusal controls**. The source inventory adds 110 named
  proofs; compiled counts also include generated declarations.
- All sixteen added library modules compile without warnings. Existing
  baseline deprecation warnings are retained in `project-build.log`.
- Recursive axiom checks allow only `propext`, `Classical.choice`, and
  `Quot.sound`. The finite-proximal audit refuses the alternative chain
  and old closure imports.

Proved scope: actual ordinary proximality equals factor-fibre equality;
nonproximal fibre rank is one; the actual solenoid has the intrinsic
maximal equicontinuous-factor property; entire finite fibres synchronize
after finite inflation and translation; a bounded integer-origin gap
gives a nonempty open synchronized set; full-history finite character
certificates have dense continuous span and pull back to actual hull
eigenfunctions; nontrivial characters have distinct finite inflation-orbit
samples.

The distinct zero-fibre seam, the actual nonunit history with character
value minus one, and the nonzero compatibility certificate representing
the constant character remain concrete controls. Matcher refusals are
reported separately from such mathematical counterexamples.

## Source and dependency provenance

`lean-receipt.json` records all accepted source hashes, package pins,
compiler/options and scope boundaries. `build-receipts.json` records each
command, duration, exit, artifact digest and complete compiler output;
the original local log path is retained as provenance. The eight audit
logs are also preserved separately.

The compiler is pinned Lean `4.34.0-rc2`; Mathlib is pinned to
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`. All nine external dependency
revisions and tracked source trees were checked. Existing pinned external
artifacts are reused; thirty absent Mathlib modules are compiled from
the pinned sources into an external-only overlay, as recorded in
`external-build-receipts.json`. The overlay contains no project objects.
No earlier project artifact is reused in the fresh acceptance.

`source-reuse.json` records the accepted local closure at
`4b02c2d4c55fb62bf37f25aa0bbc4e44bec0b6a7`. Seven support sources are
unchanged; the family FibreDistal wrapper changes only its import and
opened namespace. The new six-theorem adapter supplies the automaton
witnesses. The existing bounded-lattice finiteness proof is merely
exported, with its body unchanged, for the finite origin-gap consumer.

`native-reuse.json` checks that the native automaton implementation and
test are byte-identical to their previous accepted replay. This increment
adds Lean consumers and does not rerun or extend that native algorithm.
`semantic-review.json` records automated read-only reviews of the exact
new source hashes; these are not independent human review.

The initial development namespace lookup diagnostic is retained under
`diagnostics/`. It was resolved by preparing the correct development
artifact overlay; the final acceptance starts from empty project outputs
and cannot inherit that overlay.

## Reproduction and boundary

From the repository root:

```sh
tools/check_c4_parameter_family.sh
```

The recorded local run uses the same pinned compiler, options, source
closure and audit fixtures. It does not claim execution of the full
network/bootstrap shell gate, full-repository acceptance or completed
hosted workflows. Independent human review remains pending.

Haar preservation and inflation ergodicity, Haar-a.e. singleton fibres,
the measurable inverse and the hull's invariant-measure `L2` conclusion
remain explicit subsequent obligations. The existing compact hull,
realization bounds, dense real flow and Stone--Weierstrass are named
reused dependencies; the complete chain is not represented as free of
analysis or topology.

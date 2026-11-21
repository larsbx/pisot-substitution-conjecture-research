# Retained replay-path diagnostic

The first strict candidate invocation supplied two separate search roots
for the `PscVerif` namespace: a fresh candidate output directory and the
freshly rebuilt baseline output directory. Lean selected the candidate
namespace root and did not fall back to the other root when resolving a
baseline import. It stopped with a missing object-file error at the first
import of `PeriodicPartnerProximal.lean`.

The corrected driver links the freshly rebuilt baseline artifacts into
the otherwise fresh candidate namespace, then recompiles the seven new
modules and audit fixture there. The linked files come from the final
strict baseline replay, not the old development build. No Lean proof
source or theorem statement changed to repair this path-layout issue.

The three `first-path-layout-*` files preserve the initial failure. Final
acceptance is recorded separately under `../candidate/`.

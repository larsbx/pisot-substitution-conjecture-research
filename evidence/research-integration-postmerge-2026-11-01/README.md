# Post-integration replay and PR reconciliation, 2026-11-01

Main c27cb59693f17648d6291e6f6b306ece73ffd6a2 merges #445 at candidate
82e84827b83e72865e0e8bd7c271d18101e9baa9. Their trees are identical.
All 26 selected original source heads are ancestors of main. Eleven stacked
source PRs still open after the merge were closed as already incorporated;
#443/#444 were closed as superseded by the narrower implemented SymPy fix.
Their branches, original evidence and review histories remain available.
Dependabot #305 is separate. Closure is not hosted acceptance.

## Fresh Lean replay with an explicit environment trust input

The unmodified pinned Lean executable cannot start in this sandbox because
its IO.appPath calls readlink on /proc/<getpid()>/exe, which is denied.
/proc/self/exe correctly resolves the current executable. The archived C
compatibility wrapper redirects only that exact current-process path to
/proc/self/exe; all other path queries pass to the original libc function.
The source, compiler command, wrapper binary digest and negative controls
are explicit additional trust inputs. No Lean binary, proof source, source
pin, vendored file or assertion was patched. No wrapper is installed in CI.
The prior default-startup failure remains true and its receipt is unchanged.

The original tools/check_lean.sh ran to completion: it copied only source
and configuration into an isolated workspace, freshly cloned the pinned
Mathlib dependencies, built the cache tool, downloaded source-addressed
upstream Mathlib artifacts into an empty cache, compiled PSC, and audited
all compiled local declarations, including definitions and generated helpers.
All 52 named Lean proofs were reached; only the three configured standard
axioms were allowed. The exact declaration/theorem counts are in bindings.json.
This is a local compatibility run, not an ordinary unmodified-environment
hosted acceptance result or independent human proof certification. It does
not prove general PSC or formalize the entire Class-C argument.

Replay in this particular sandbox after the normal pinned toolchain setup:

```sh
PSC_PACKET=evidence/research-integration-postmerge-2026-11-01
cc -shared -fPIC -Wall -Wextra -Werror "$PSC_PACKET/proc_self_compat.c" -ldl -o /tmp/libproc_self_compat.so
cc -Wall -Wextra -Werror "$PSC_PACKET/test_proc_self_compat.c" -o /tmp/test_proc_self_compat
LD_PRELOAD=/tmp/libproc_self_compat.so /tmp/test_proc_self_compat
LD_PRELOAD=/tmp/libproc_self_compat.so PATH="$HOME/.elan/bin:$PATH" bash tools/check_lean.sh
```

The controls check equality of both current-executable aliases and preserve
the original missing-path and unrelated-process refusals. The permission
control is specific to this sandbox and is not a portability claim. Normal
hosted runners must run the existing scripts without this wrapper.

The earlier full Python/native/TLA/graph receipts remain unchanged. Fresh
post-merge source/checksum/Class-C assembly/Class-D guard tests passed 149
checks before this supplemental packet was created. Its own checksum and
link integrity is checked separately. No old receipt is refreshed or deleted.

The raw audit log is losslessly compressed as lean-compat-audit.log.gz. Its
uncompressed digest is in bindings.json; preserve the final empty TSV axiom
column rather than stripping whitespace from the recorded output.

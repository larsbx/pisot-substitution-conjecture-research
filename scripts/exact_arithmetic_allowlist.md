# Exact Arithmetic Allowlist

Files that may contain floating-point types or literals. Each entry must have a
matching `QUARANTINED` row in section 6.1 of
`docs/rational-interval-arithmetic-spec.md`, and none of them may be imported
by a module that constructs, evaluates, or accepts certificate data.

Allowed implementation locations:

- none

The canonical Mojo kernel under `mojo/` is float-free by construction; keep it
that way rather than extending this list.

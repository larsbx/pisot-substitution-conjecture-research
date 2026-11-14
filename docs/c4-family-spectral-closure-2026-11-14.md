# Spectral closure for the literal C4 parameter family

## Result and formal boundary

For every natural `k >= 2`, the literal substitution

\[
\sigma_k(0)=1,\qquad \sigma_k(1)=0\,1^k\,2,\qquad \sigma_k(2)=001
\]

satisfies the arithmetic and balanced-pair hypotheses of
Barge--Stimac--Williams, Corollary 2. The assembled Lean endpoint is
`Psc.ParameterFamilyBridge.spectral_criterion_inputs` in
[`C4ParameterFamilyBridge.lean`](../proof/PscVerif/PscVerif/C4ParameterFamilyBridge.lean).
It has only the parameter and `2 <= k` as premises. The corresponding
substitution tiling action has pure discrete spectrum by the published
criterion and the standing-hypothesis argument below.

This is a family-specific mathematical conclusion using an external spectral
theorem. The Lean development proves the literal arithmetic and complete
factor condition; it does not contain the analytic/topological spectral
implication. No spectral axiom is added. The `k=1` case is already covered by
the published cubic trace-at-most-two theorem, so the external mathematical
family conclusion extends to `k>=1`. The new combined Lean endpoint retains
its honest `k>=2` scope.

The [pre-code decision](c4-family-pisot-bridge-stop-go-2026-11-14.md) records
the primary-source check and hypothesis boundaries. This result does not
promote universal BH, residual A1-prime, C4, G1 or PSC.

## 1. Actual incidence and primitive Pisot arithmetic

[`C4ParameterFamilyPisot.lean`](../proof/PscVerif/PscVerif/C4ParameterFamilyPisot.lean)
uses `Psc.Incidence.inc` on the actual words. Source letters index columns:

\[
M_k=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix},\quad
M_k^2=\begin{pmatrix}1&k+2&1\\k&k^2+2&k+2\\1&k&1\end{pmatrix}.
\]

The second matrix is strictly positive for `k>=1`, proving primitivity.
The same matrix has determinant two and characteristic polynomial

\[
f_k(X)=X^3-kX^2-2X-2.
\]

The proof binds this polynomial to the rational cast of the actual incidence
matrix. Monicity over the integers reduces a rational root to an integer
divisor of two; all candidates are excluded. The cubic is therefore
irreducible over the rationals.

An exact intermediate-value argument supplies a root `beta` between `2` and
`k+2`. Put `p=beta^2-k beta-2` and `d=beta-k`. The root equation gives

\[
\beta p=2,\qquad \beta d=p+2,\qquad 2d=p(p+2).
\]

These identities give `0<p<1` and `d^2<4p`. Every other complex root satisfies
`z^2+dz+p=0`; its real and imaginary parts then give

\[
\operatorname{Im}z\ne0,\qquad |z|^2=p=2/\beta<1.
\]

Thus `beta` is the expanding Perron root, an algebraic integer whose other
conjugates contract. The compiled proof also supplies its irrationality and
the positive left eigenvector

\[
w=(\beta,\beta^2,\beta+2),\qquad w^{\mathsf T}M_k=\beta w^{\mathsf T}.
\]

In particular the lengths of letters zero and one are rationally independent:
`a beta+b beta^2=0`, for rational `a,b`, would imply `a+b beta=0`, and hence
`a=b=0`. The chosen corollary already obtains the required independence from
characteristic-polynomial irreducibility; this explicit calculation explains
the literal seed's geometric suitability.

## 2. Exact single-seed factor correspondence

The accepted family carrier proves finite `ChildNC` reachability and
productivity for every reached state of `01/10`. The new general module
[`TerminationFactors.lean`](../proof/PscVerif/PscVerif/TerminationFactors.lean)
proves the complete correspondence with factors of actual iterates.

For any finite alphabet and irreducible balanced seed `T`, the existing
`TerminatesWithCoincidence s T` predicate is equivalent to both:

1. The set of all blocks in
   `red ((subst s)^[n] T.1) ((subst s)^[n] T.2)`, over all natural `n`, is finite.
2. Every such block `U` has some `m,a` for which `([a],[a])` occurs in the
   actual reduction of the `m`-th substituted top and bottom words of `U`.

A full child path ending at a noncoincident block is a `ChildNC` path.
Coincident irreducible blocks are singleton diagonals, of which there are only
finitely many. This proves the finiteness correspondence. For productivity,
a full path to a coincidence is truncated at its first diagonal. The proof
never equates the full and terminal reachable sets.

The general equivalence allows erasing substitutions and depth zero. All
literal family images are nonempty. If positive iterate depths are desired,
a depth-zero singleton coincidence can therefore be advanced one step; including
depth zero in the factor set strengthens its coverage.

`Psc.ParameterFamilyBridge.full_factor_termination` specializes this equivalence
to the literal family and seed. `spectral_criterion_inputs` combines it with
the independently proved arithmetic, without assuming any of the desired inputs.

## 3. Standing dynamical hypotheses and the external conclusion

Use the three positive entries of `w` as tile lengths. The eigenvector identity
gives the geometric inflation factor `beta`. Finite local complexity follows
because a bounded interval can contain only a bounded number of positive-length
tiles; finitely many letters then give finitely many labelled words up to
translation.

Aperiodicity has a direct reconstruction argument. A primitive substitution
system is minimal. If it contained a periodic point, the system would be its
finite shift orbit and would have a positive rational normalized letter-frequency
vector `q`. Substitution stays in this system, so
`M_k q = lambda q`, with rational average expansion
`lambda = sum_a q_a * length(sigma_k(a))`. Pairing with `w` gives
`(beta-lambda)(w dot q)=0`. The dot product is positive, contradicting the
proved irrationality of `beta`. These symbolic/geometric realization arguments
are mathematical prose, not assertions that the current Lean endpoint defines
or proves aperiodicity or finite local complexity.

[Barge--Stimac--Williams, section 3 and Corollary 2](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf)
now applies to `a=0,b=1`: the substitution is primitive Pisot, its incidence
characteristic polynomial is irreducible, and the balanced-pair algorithm for
the unequal-letter swap seed terminates with coincidence in the paper's full
factor sense. The resulting tiling action has pure discrete spectrum. This
criterion does not require unimodularity.

[Akiyama--Gahler--Lee, Proposition 2.2](https://dmtcs.episciences.org/en/articles/2089/download)
already gives the same spectral conclusion for primitive irreducible cubic
Pisot substitutions of trace at most two. It covers the first family member,
whose trace is one, and provides the known second-parameter control.

## 4. Controls and replay

- The new arithmetic control proves that parameter zero has no real
  characteristic root greater than two. It refutes dropping `k>=1` from that
  exact endpoint; it is not a standalone formal theorem saying zero is not Pisot.
- The existing `k=2` control retains the reached state with no immediate
  coincidence child, so the stronger immediate-exit theorem still needs `k>=3`.
- The identity substitution on two letters has a finite factor set from `01/10`
  but no coincidence. Finiteness cannot replace productivity.
- The existing Fibonacci control contains a full-iterate diagonal factor that
  is not terminal-child reachable. This guards the path-truncation argument.

The family gate compiles the complete required source closure in a fresh
workspace, checks all owned constants and exact literal endpoint types, and
rejects missing or wrong-typed endpoints. Run:

```sh
./tools/setup_lean.sh
./tools/check_c4_parameter_family.sh
./tools/check_lean.sh
```

The full-library gate remains separate. The predecessor source
`32015cfb9d0914cedc9867f3290ea4bcdbbbb3b7` passed both dedicated family jobs
and its full-library audit: 11,854 constants, 7,747 theorem constants and
3,774 named proofs. Those predecessor receipts do not substitute for acceptance
of the new arithmetic and correspondence modules. The accompanying PR records
the new revision's terminal results and preserves its publication-time status.

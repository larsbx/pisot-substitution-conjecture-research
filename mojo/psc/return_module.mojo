"""The return module of a substitution on three letters, decided exactly.

The return module is the subgroup of Z^3 spanned by the Parikh vectors of
the return words: pi(w) for every nonempty legal word w such that w w_1 is
legal, i.e. the lifted displacements between two occurrences of one letter.
Its index in Z^3 is hypothesis (R) of
docs/p1b-periodic-pair-fibre-literature-gate-2026-10-02.md, which is proved
there as Theorem R: the index is 1 for every primitive substitution whose
frequency vector has Q-independent coordinates, in particular for every PIP
substitution.

For primitive sigma the index is computed from the two-letter graph G (an
edge a -> c for each legal word ac), which is then strongly connected. A
character of Z^3 vanishes on the return module exactly when
it is a coboundary on the edges of G (Theorem R, step 1), so the return module
is the cycle lattice of G: the span of the letter-count vectors of the simple
cycles of G. On three vertices those are the loops, the two-cycles and the two
oriented triangles. The index is the gcd of the 3 x 3 minors of these vectors;
0 means the span has rank less than 3, which an irreducible incidence matrix
excludes (see the singular controls in tests/test_return_module.mojo).

Exact integer arithmetic only; the two-letter language is
`psc.overlap_collar.legal_factors`, not a second enumeration.
"""

from std.math import gcd
from psc.overlap_collar import legal_factors, word_key


def two_letter_graph(sigma: List[List[Int]]) raises -> List[List[Bool]]:
    """`edge[a][c]` is True exactly when `ac` is a legal word of `sigma`."""
    if len(sigma) != 3:
        raise Error("return module: the alphabet must be {0,1,2}")
    var legal = legal_factors(sigma, 2)
    var edge = List[List[Bool]]()
    for a in range(3):
        var row = List[Bool]()
        for c in range(3):
            row.append(word_key([a, c]) in legal)
        edge.append(row^)
    return edge^


def cycle_vectors(edge: List[List[Bool]]) -> List[List[Int]]:
    """Letter-count vectors of the simple cycles of a digraph on {0,1,2}."""
    var out = List[List[Int]]()
    for a in range(3):
        if edge[a][a]:
            var v: List[Int] = [0, 0, 0]
            v[a] = 1
            out.append(v^)
    for a in range(3):
        for c in range(a + 1, 3):
            if edge[a][c] and edge[c][a]:
                var v: List[Int] = [0, 0, 0]
                v[a] = 1
                v[c] = 1
                out.append(v^)
    if (edge[0][1] and edge[1][2] and edge[2][0]) or (edge[0][2] and edge[2][1] and edge[1][0]):
        out.append([1, 1, 1])
    return out^


def _det3(a: List[Int], b: List[Int], c: List[Int]) -> Int:
    return (
        a[0] * (b[1] * c[2] - b[2] * c[1])
        - a[1] * (b[0] * c[2] - b[2] * c[0])
        + a[2] * (b[0] * c[1] - b[1] * c[0])
    )


def lattice_index(vectors: List[List[Int]]) -> Int:
    """Index in Z^3 of the span of `vectors`: the gcd of their 3 x 3 minors,
    0 when the span has rank less than 3."""
    var g = 0
    var n = len(vectors)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                g = gcd(g, abs(_det3(vectors[i], vectors[j], vectors[k])))
    return g


def return_module_index(sigma: List[List[Int]]) raises -> Int:
    """Index of the return module of `sigma` in Z^3 (0: rank less than 3)."""
    return lattice_index(cycle_vectors(two_letter_graph(sigma)))

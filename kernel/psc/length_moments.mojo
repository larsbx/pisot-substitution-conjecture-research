"""Exact length observations of a supplied occurrence defect, not hit existence.

Arithmetic and rank come from the vendored generic exact packages. A full-rank
observation map is checked, never inferred from a caller's PIP assertion.
Offsets use bottom-start minus top-start, in integer Parikh coordinates.
"""
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_is_zero, q_int
from finite_linear_algebra.qlinalg import rank, matvec, is_zero_vec
from finite_linear_algebra.madic_ball import lift_square, qmat_pow
from substitution_dynamics.substitution import Substitution


def observation_rows(sigma: Substitution, period: Int = 1) raises -> List[List[Q]]:
    if sigma.size < 1 or sigma.size > 6:
        raise Error("length observation dimension must be 1..6")
    if period < 1 or period > 10000:
        raise Error("length observation period budget is 1..10000")
    var m = qmat_pow(lift_square(sigma.incidence(), sigma.size), period)
    var transpose = List[List[Q]]()
    for i in range(sigma.size):
        var column = List[Q]()
        for j in range(sigma.size):
            column.append(m[j][i].copy())
        transpose.append(column^)
    var row = List[Q]()
    for _ in range(sigma.size):
        row.append(Q.one())
    var out = List[List[Q]]()
    for _ in range(sigma.size):
        out.append(row.copy())
        row = matvec(transpose, row)
    return out^


struct LengthMomentTables(Copyable, Movable):
    var sigma: Substitution
    var matrix: List[List[Q]]
    var observations: List[List[Q]]

    def __init__(out self, images: List[List[Int]], period: Int = 1) raises:
        self.sigma = Substitution.checked(images)
        self.observations = observation_rows(self.sigma, period)
        if rank(self.observations) != self.sigma.size:
            raise Error("singular length observation map: equality cannot certify a defect")
        self.matrix = lift_square(self.sigma.incidence(), self.sigma.size)

    def moments(self, defect: List[Int]) raises -> List[Q]:
        if len(defect) != self.sigma.size:
            raise Error("defect dimension mismatch")
        var exact = List[Q]()
        for i in range(len(defect)):
            exact.append(q_int(defect[i]))
        return matvec(self.observations, exact)


struct MomentWitness(Copyable, Movable):
    var top: Int
    var bottom: Int
    var defect: List[Q]
    var moments: List[Q]

    def __init__(out self, top: Int, bottom: Int, defect: List[Q], moments: List[Q]):
        self.top = top
        self.bottom = bottom
        self.defect = defect.copy()
        self.moments = moments.copy()

    def boundary_hit(self) -> Bool:
        return is_zero_vec(self.moments)

    def coincidence(self) -> Bool:
        return self.boundary_hit() and self.top == self.bottom


def replay_moment_address(
    tables: LengthMomentTables, top: Int, bottom: Int, offset: List[Int],
    top_path: List[Int], bottom_path: List[Int], max_steps: Int = 10000,
) raises -> MomentWitness:
    """Replay proper-prefix indices from root to leaf; no search/coverage claim.

    A zero result for an actual overlap gives a common left boundary with
    positive interior intersection; unequal final letters are permitted for
    BH only. Starting seed reachability is an independent obligation.
    """
    var d = tables.sigma.size
    if top < 0 or top >= d or bottom < 0 or bottom >= d:
        raise Error("root letter outside alphabet")
    if len(offset) != d:
        raise Error("offset dimension mismatch")
    if len(top_path) != len(bottom_path):
        raise Error("paired addresses must have equal depth")
    if max_steps < 0 or len(top_path) > max_steps:
        raise Error("occurrence address budget exhausted")
    var defect = List[Q]()
    for i in range(d):
        defect.append(q_int(offset[i]))
    var a = top
    var b = bottom
    for k in range(len(top_path)):
        var i = top_path[k]
        var j = bottom_path[k]
        if i < 0 or i >= len(tables.sigma.images[a]) or j < 0 or j >= len(tables.sigma.images[b]):
            raise Error("address index is not a proper-prefix occurrence")
        defect = matvec(tables.matrix, defect)
        for p in range(i):
            var letter = tables.sigma.images[a][p]
            defect[letter] = defect[letter].sub(Q.one())
        for p in range(j):
            var letter = tables.sigma.images[b][p]
            defect[letter] = defect[letter].add(Q.one())
        a = tables.sigma.images[a][i]
        b = tables.sigma.images[b][j]
    return MomentWitness(a, b, defect, matvec(tables.observations, defect))

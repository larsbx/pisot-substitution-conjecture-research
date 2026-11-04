"""Bounded exact scaled-inverse certificate for an ordered mean-area lift.

If S Q = Q S = d I with integer Q and positive d, the unique rational
solution of S x = b is Qb/d. One indivisible coordinate excludes an
integral word mean-area lift. This does NOT establish word realizability,
a strict SCC, a Pisot spectrum, or general C4/PSC. The caller constructs
S and b from ALL ordered children. Caps are executable budgets only.
"""


def validate_lift_inverse(
    S: List[List[Int]], Q: List[List[Int]], denominator: Int,
) raises:
    var n = len(S)
    if n < 1 or n > 24 or len(Q) != n:
        raise Error("invalid exact lift certificate dimensions")
    if denominator < 1 or denominator > 1000000:
        raise Error("invalid exact lift certificate denominator")
    for i in range(n):
        if len(S[i]) != n or len(Q[i]) != n:
            raise Error("ragged exact lift certificate")
        for j in range(n):
            if S[i][j] < -1000000 or S[i][j] > 1000000:
                raise Error("operator coordinate exceeds safe budget")
            if Q[i][j] < -1000000 or Q[i][j] > 1000000:
                raise Error("inverse coordinate exceeds safe budget")
    # Every sum has <=24 terms of magnitude <=10^12: safe signed Int64.
    for i in range(n):
        for j in range(n):
            var sq = 0
            var qs = 0
            for k in range(n):
                sq += S[i][k] * Q[k][j]
                qs += Q[i][k] * S[k][j]
            var expected = 0
            if i == j:
                expected = denominator
            if sq != expected or qs != expected:
                raise Error("false two-sided scaled inverse certificate")


def lift_numerators(Q: List[List[Int]], rhs: List[Int]) raises -> List[Int]:
    """Use only after validate_lift_inverse; return exact numerators Qb."""
    var n = len(rhs)
    if n < 1 or n > 24 or len(Q) != n:
        raise Error("invalid lift RHS dimensions")
    for i in range(n):
        if len(Q[i]) != n or rhs[i] < -1000000 or rhs[i] > 1000000:
            raise Error("invalid lift RHS budget or shape")
        for j in range(n):
            if Q[i][j] < -1000000 or Q[i][j] > 1000000:
                raise Error("inverse coordinate exceeds safe budget")
    var result = List[Int]()
    for i in range(n):
        var value = 0
        for j in range(n):
            value += Q[i][j] * rhs[j]
        result.append(value)
    return result^

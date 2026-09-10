"""Exact necessary-condition census for hypothetical three-state degree-2 SCCs.

If a strict closed degree-2 SCC C has |C|=3, the Parikh and signed K2
intertwiners force

    N_C ~ M_sigma,        S_C ~ Lambda^2 M_sigma,

while N_C=A+B and S_C=A-B for nonnegative integer A,B. Hence for every k>=1

    tr(M^k) - tr((Lambda^2 M)^k)
      = 2 * sum_{words with odd B-count} tr(word(A,B)) >= 0.

For k=2 the difference is exactly 4 tr(A B), hence divisible by four.
This finite census first applies the mod-2 three-state parity sieve, then tests
these exact trace conditions on the established 4554 PIP corpus.

Finite evidence only: surviving/absent specimens do not prove a general theorem.
"""

from psc.bpa import substitution_incidence
from psc.mat3 import Mat3
from psc.pisot import is_pip


def image_words() -> List[List[Int]]:
    var out = List[List[Int]]()
    for a in range(3):
        var w1: List[Int] = [a]
        out.append(w1^)
    for a in range(3):
        for b in range(3):
            var w2: List[Int] = [a, b]
            out.append(w2^)
    for a in range(3):
        for b in range(3):
            for c in range(3):
                var w3: List[Int] = [a, b, c]
                out.append(w3^)
    return out^


def mod2(x: Int) -> Int:
    var r = x % 2
    return r if r >= 0 else r + 2


def parity_allows_three_states(t: Int, u: Int, d: Int) -> Bool:
    """Exactly the lcm-degree-3 rows of the merged mod-2 sieve."""
    var tp = mod2(t)
    var up = mod2(u)
    var dp = mod2(d)
    if tp != up:
        return False
    if tp == 0:
        return True
    return dp == 1


def traces_standard(t: Int, u: Int, d: Int, max_k: Int) -> List[Int]:
    """Power sums of roots of x^3 - t x^2 + u x - d."""
    var p = List[Int]()
    p.append(3)
    if max_k == 0:
        return p^
    p.append(t)
    if max_k == 1:
        return p^
    p.append(t * t - 2 * u)
    for k in range(3, max_k + 1):
        p.append(t * p[k - 1] - u * p[k - 2] + d * p[k - 3])
    return p^


def traces_exterior(t: Int, u: Int, d: Int, max_k: Int) -> List[Int]:
    """Power sums for Lambda^2 M, whose cubic is x^3-u x^2+d t x-d^2."""
    var q = List[Int]()
    q.append(3)
    if max_k == 0:
        return q^
    q.append(u)
    if max_k == 1:
        return q^
    q.append(u * u - 2 * d * t)
    for k in range(3, max_k + 1):
        q.append(u * q[k - 1] - d * t * q[k - 2] + d * d * q[k - 3])
    return q^


def main() raises:
    var words = image_words()
    var n_pip = 0
    var parity_survivors = 0
    var trace1_survivors = 0
    var trace2_survivors = 0
    var trace3_survivors = 0
    var trace6_survivors = 0
    var trace12_survivors = 0
    var first_trace_failure = List[Int]()
    for _ in range(13):
        first_trace_failure.append(0)

    var printed_survivor = False

    for i in range(len(words)):
        for j in range(len(words)):
            for k in range(len(words)):
                var sigma = List[List[Int]]()
                sigma.append(words[i].copy())
                sigma.append(words[j].copy())
                sigma.append(words[k].copy())
                var m = Mat3(substitution_incidence(sigma))
                if not is_pip(m):
                    continue
                n_pip += 1

                var chi = m.charpoly()
                var t = -chi[2]
                var u = chi[1]
                var d = -chi[0]
                if not parity_allows_three_states(t, u, d):
                    continue
                parity_survivors += 1

                var p = traces_standard(t, u, d, 12)
                var q = traces_exterior(t, u, d, 12)
                var first_fail = 0
                for power in range(1, 13):
                    if p[power] < q[power]:
                        first_fail = power
                        break
                    if power == 2 and (p[2] - q[2]) % 4 != 0:
                        first_fail = 2
                        break

                if p[1] >= q[1]:
                    trace1_survivors += 1
                if p[1] >= q[1] and p[2] >= q[2] and (p[2] - q[2]) % 4 == 0:
                    trace2_survivors += 1
                var ok3 = True
                for power in range(1, 4):
                    if p[power] < q[power]:
                        ok3 = False
                    if power == 2 and (p[2] - q[2]) % 4 != 0:
                        ok3 = False
                if ok3:
                    trace3_survivors += 1
                var ok6 = True
                for power in range(1, 7):
                    if p[power] < q[power]:
                        ok6 = False
                    if power == 2 and (p[2] - q[2]) % 4 != 0:
                        ok6 = False
                if ok6:
                    trace6_survivors += 1
                if first_fail == 0:
                    trace12_survivors += 1
                    if not printed_survivor:
                        print("TRACE12_SURVIVOR_JSON {\"i\":", i, ",\"j\":", j, ",\"k\":", k,
                              ",\"T\":", t, ",\"U\":", u, ",\"d\":", d, "}")
                        printed_survivor = True
                else:
                    first_trace_failure[first_fail] += 1

    print("C4 degree-2 three-state necessary-condition census")
    print("PIP specimens:", n_pip)
    print("three-state parity survivors:", parity_survivors)
    print("survive trace k<=1:", trace1_survivors)
    print("survive trace k<=2 plus mod4:", trace2_survivors)
    print("survive trace k<=3:", trace3_survivors)
    print("survive trace k<=6:", trace6_survivors)
    print("survive trace k<=12:", trace12_survivors)
    for power in range(1, 13):
        if first_trace_failure[power] > 0:
            print("first failure at k=" + String(power) + ": " + String(first_trace_failure[power]))

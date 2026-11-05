"""Positive equal-Parikh prefix certificates, independent of SCC templates.

The 021 run family has an unbounded paper proof. Executable budgets below
are not hypotheses of that proof. A missing/over-budget witness raises;
this module never turns search exhaustion into a noncoincidence verdict.
Reuse existing literal inflation and the existing run-family receipt type.
"""
from psc.bpa import apply_substitution
from psc.c4_third_level_coincidence_family import ClosedRunCoincidence, closed_run_middle_family


def verify_simultaneous_prefix_certificate(
    sigma: List[List[Int]], generation: Int, cut: Int,
    prefix: List[Int], next_letter: Int,
) raises -> List[Int]:
    if len(sigma) != 3 or generation < 1 or generation > 7:
        raise Error("invalid source alphabet or generation budget")
    if cut < 0 or cut > 500000 or len(prefix) != 3:
        raise Error("invalid common cut or prefix dimension")
    if next_letter < 0 or next_letter >= 3:
        raise Error("invalid common next letter")
    var total = 0
    for a in range(3):
        if prefix[a] < 0 or prefix[a] > 500000:
            raise Error("invalid prefix coordinate budget")
        total += prefix[a]
        if len(sigma[a]) == 0 or len(sigma[a]) > 32:
            raise Error("invalid nonerasing source image budget")
        for z in sigma[a]:
            if z < 0 or z >= 3:
                raise Error("invalid source letter before indexing")
    if total != cut:
        raise Error("prefix mass and physical index disagree")
    var lengths = List[Int]()
    for a in range(3):
        var word: List[Int] = [a]
        for _ in range(generation):
            var predicted = 0
            for z in word:
                predicted += len(sigma[z])
                if predicted > 500000:
                    raise Error("literal word budget exhausted, no verdict")
            word = apply_substitution(sigma, word)
        if cut >= len(word) or word[cut] != next_letter:
            raise Error("no advertised common next letter")
        var actual: List[Int] = [0,0,0]
        for j in range(cut):
            actual[word[j]] += 1
        if actual != prefix:
            raise Error("unequal actual Parikh prefix")
        lengths.append(len(word))
    return lengths^


def tail_021_run_family(a: Int, b: Int) raises -> List[List[Int]]:
    if a < 0 or b < 0 or a > 8 or b > 8:
        raise Error("021 family executable parameter budget")
    if a + b == 0 or a + b > 12:
        raise Error("021 family requires positive bounded total run")
    var original = closed_run_middle_family(a, b)
    return [[0,1], original[1].copy(), [0,2,1]]


def verify_tail_021_coincidence(a: Int, b: Int) raises -> ClosedRunCoincidence:
    var sigma = tail_021_run_family(a,b)
    var s = a+b
    var n = 5
    var p = 0
    var z = 0
    var Q: List[Int] = [0,0,0]
    if a == 0:
        n = 2
    elif b > 0:
        p = a * (s*s+s+3) + 1
        Q = [a+1, a*(s*s+1), a*(s+1)]
        z = 1
    elif a == 1:
        p = 16
        Q = [4,7,5]
    else:
        p = a*a*a + 2*a*a + 5*a + 6
        Q = [a+2, a*a*a+a*a+2*a+2, a*a+2*a+2]
    var lengths = verify_simultaneous_prefix_certificate(sigma,n,p,Q,z)
    return ClosedRunCoincidence(a,b,n,p,z,Q,lengths)

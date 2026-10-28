"""Exact finite profile of the class-C lines `(p,q,r) = (n+d, n, n-d+eps)`.

  sigma(x) = x y^(n+d) x,   sigma(c) = c y^n x,   sigma(y) = c y^(n-d+eps) c,   eps = +-1.

A member's record is the block of `psc.class_a_gap_dataset.substitution_block`:
the complete canonical swap-seed graph under the 20,000-state cap, stored as
its maximal typed k-intervals. A capped graph or a non-hitting vertex raises.
Only the three exact screening refusals of `screened_perron_field3` (a
reducible, non-Pisot or imprimitive member) mark a member as outside the PIP
domain; any other error propagates. Everything here is a finite observation;
nothing is uniform in `n` or `d`.
"""
from a1_normal_form_census import class_member, CLASS_C
from psc.class_a_gap_dataset import substitution_block

comptime SCREENING_REFUSALS: List[String] = [
    "the characteristic polynomial is reducible",
    "the characteristic polynomial is not Pisot",
    "the screened field needs a primitive matrix",
]


def check_line(d: Int, eps: Int) raises:
    if eps != 1 and eps != -1:
        raise Error("class-C line requires eps = +-1")
    if d < 1 or d > 64:
        raise Error("class-C profile requires 1 <= d <= 64")


def c_member(d: Int, eps: Int, n: Int) raises -> List[List[Int]]:
    check_line(d, eps)
    if n < 0 or n > 400:
        raise Error("class-C finite replay budget requires 0 <= n <= 400")
    if n - d + eps < 0:
        raise Error("class-C member outside the normal form: n-d+eps < 0")
    return class_member(CLASS_C, n + d, n, n - d + eps)


def is_screening_refusal(message: String) -> Bool:
    for s in materialize[SCREENING_REFUSALS]():
        if message == s:
            return True
    return False


def c_block(d: Int, eps: Int, n: Int) raises -> String:
    """The member's block, or `S n reason` for a screened non-PIP member."""
    var sigma = c_member(d, eps, n)
    try:
        return substitution_block(sigma, n)
    except e:
        if is_screening_refusal(String(e)):
            return "S " + String(n) + " " + String(e) + "\n"
        raise e^


def frozen_onset(d: Int, eps: Int) -> Int:
    """Observed onset of the frozen tail: `4d` (plus), `4d + 4` (minus)."""
    return 4 * d if eps == 1 else 4 * d + 4


def rows_of(block: String) -> String:
    """The `R` lines of a block: its exact label set, independent of `n`."""
    var out = String()
    for line in block.splitlines()[1:]:
        out += String(line) + "\n"
    return out^


def vertices_of(block: String) raises -> Int:
    var head = block.splitlines()[0].split(" ")
    if len(head) != 5 or String(head[0]) != "M":
        raise Error("not a member block")
    return Int(head[2])

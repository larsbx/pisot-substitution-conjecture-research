"""Gap forms and regimes: Lemma 1 and Lemma 2 against brute force, and every refusal."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.gap_form import GapForm, Regime, gap_const, gap_lin, quadrant_nonneg, KIND_LOW, KIND_HIGH, KIND_MIDDLE


def brute_nonneg(g: GapForm, l0: Int, d0: Int, span: Int) -> Bool:
    for l in range(l0, l0 + span):
        for d in range(d0, d0 + span):
            if g.at(l, d, 0) < 0:
                return False
    return True


def ceil_div(a: Int, b: Int) -> Int:
    var q = a // b
    return q + (1 if q * b < a else 0)


def refuses_div(reg: Regime, f: GapForm, ceil: Bool) -> Bool:
    try:
        if ceil:
            _ = reg.div_ceil(f)
        else:
            _ = reg.div_floor(f)
    except:
        return True
    return False


def check_division(reg: Regime, f: GapForm, ceil: Bool, span: Int) raises:
    """Whenever the regime decides a rounding, brute force over its members agrees;
    whenever brute force shows the rounding to vary, the regime refuses."""
    var decided = not refuses_div(reg, f, ceil)
    var seen = 1000000
    var varies = False
    for l in range(reg.l0, reg.l0 + 3):
        for d in range(reg.d0, reg.d0 + span):
            for r in range(d):
                if not reg.contains(l, d, r):
                    continue
                var n = f.at(l, d, r)
                var q = ceil_div(n, d) if ceil else n // d
                if decided:
                    var g = reg.div_ceil(f) if ceil else reg.div_floor(f)
                    assert_equal(g.at(l, d, r), q)
                var k = q - (f.cld * l + f.cd + (f.cr if reg.kind == KIND_HIGH else 0))
                if seen == 1000000:
                    seen = k
                elif seen != k:
                    varies = True
    if varies:
        assert_true(not decided)


def main() raises:
    # Lemma 1 against brute force on a grid of coefficient tuples and floors.
    var checked = 0
    for c1 in range(-6, 7, 3):
        for cl in range(-2, 3):
            for cd in range(-2, 3):
                for cld in range(-1, 2):
                    var g = GapForm(c1, cl, cd, cld, 0)
                    for l0 in [1, 5]:
                        for d0 in [1, 5, 9]:
                            var brute = brute_nonneg(g, l0, d0, 12)
                            var crit = quadrant_nonneg(g, l0, d0)
                            # The criterion is exact; brute force over a finite window can only
                            # fail to see a far-away sign change, so crit implies brute.
                            if crit:
                                assert_true(brute)
                            if not brute:
                                assert_true(not crit)
                            # When every slope condition holds the two agree exactly.
                            if cl + cld * d0 >= 0 and cd + cld * l0 >= 0 and cld >= 0:
                                assert_equal(crit, brute)
                            checked += 1
    assert_true(checked > 1000)
    # The regime reduction: r-dependent forms decided at the endpoints agree with brute force.
    var regimes = List[Regime]()
    regimes.append(Regime(-1, KIND_LOW, 0, 0, 5, 7))
    regimes.append(Regime(-1, KIND_LOW, 2, 0, 5, 7))
    regimes.append(Regime(1, KIND_HIGH, 1, 0, 5, 7))
    regimes.append(Regime(1, KIND_HIGH, 3, 0, 5, 9))
    regimes.append(Regime(-1, KIND_MIDDLE, 3, 4, 5, 7))
    regimes.append(Regime(1, KIND_MIDDLE, 5, 6, 5, 11))
    for reg in regimes:
        reg.check()
        for c1 in range(-9, 10, 3):
            for cr in range(-2, 3):
                for cd in range(-1, 2):
                    var f = GapForm(c1, 0, cd, 1, cr)
                    var brute = True
                    for l in range(reg.l0, reg.l0 + 6):
                        for d in range(reg.d0, reg.d0 + 8):
                            for r in range(d):
                                if reg.contains(l, d, r) and f.at(l, d, r) < 0:
                                    brute = False
                    if reg.nonneg(f):
                        assert_true(brute)
                    # le is consistent with nonneg.
                    var u = gap_lin(1, c1)
                    var v = GapForm(0, 0, 1, 1, cr)
                    var verdict = reg.le(u, v)
                    if verdict == 1:
                        assert_true(reg.nonneg(v.sub(u)))
                    if verdict == 0:
                        assert_true(reg.nonneg(u.sub(v).sub(gap_const(1))))
    # Lemma 2 against brute force, including every refusal.
    for reg in regimes:
        for c1 in range(-12, 13):
            for cr in range(-2, 3):
                for cd in range(-1, 2):
                    for cld in range(0, 2):
                        var f = GapForm(c1, 0, cd, cld, cr)
                        check_division(reg, f, True, 9)
                        check_division(reg, f, False, 9)
    # Lemma 2': the one-sided bounds never refuse and bracket the exact roundings at every member.
    for reg in regimes:
        for c1 in range(-12, 13, 2):
            for cr in range(-2, 3):
                for cd in range(-1, 2):
                    var f = GapForm(c1, 0, cd, 1, cr)
                    var lo = reg.div_ceil_lower(f)
                    var hi = reg.div_floor_upper(f)
                    for l in range(reg.l0, reg.l0 + 3):
                        for d in range(reg.d0, reg.d0 + 9):
                            for r in range(d):
                                if not reg.contains(l, d, r):
                                    continue
                                var n = f.at(l, d, r)
                                assert_true(lo.at(l, d, r) <= ceil_div(n, d))
                                assert_true(hi.at(l, d, r) >= n // d)
    # A pure l term, and an |r coefficient| >= 2 on the middle regime, refuse.
    assert_true(refuses_div(regimes[0], gap_lin(1, 0), True))
    assert_true(refuses_div(regimes[4], GapForm(0, 0, 0, 1, 2), True))
    # Known values: ceil((d + r)/d) on low r=0 is 1 for the quotient, and -7/d is undecided below d0 = 8.
    assert_equal(regimes[0].div_ceil(GapForm(0, 0, 1, 0, 1)), gap_lin(0, 1))
    assert_true(refuses_div(regimes[0], gap_const(-7), True))
    assert_equal(Regime(-1, KIND_LOW, 0, 0, 5, 8).div_ceil(gap_const(-7)), gap_const(0))
    # Run lengths and malformed regimes.
    assert_equal(regimes[0].run(0), GapForm(0, 0, 1, 1, 1))
    assert_equal(regimes[2].run(2), GapForm(1, 0, 0, 1, 1))
    var bad = False
    try:
        Regime(1, KIND_MIDDLE, 5, 6, 5, 10).check()
    except:
        bad = True
    assert_true(bad)
    require_contract("gap forms c1 + cl l + cd d + cld l d + cr r on class-A residue regimes: Lemma 1 (quadrant positivity) and the regime r-reduction agree with brute force; Lemma 2 (uniform division by d) agrees with brute force on every decided rounding and refuses every rounding that varies with d or r, a pure l term, and |cr| >= 2 on the middle regime; Lemma 2' one-sided bounds bracket every exact rounding at every member; malformed regimes refuse")

from std.sys import argv
from std.time import perf_counter_ns
from odd_letter_family_certificate import RunPattern, cover_pattern_guided, Y, Z

def alt(first: Int, n: Int) -> List[Int]:
    var out = List[Int]()
    var c = first
    for _ in range(n):
        out.append(c)
        c = Z if c == Y else Y
    return out^

def main() raises:
    # zruns s delta floor r1 r2 budget [qlift 0/1]
    var args = argv()
    var s = Int(String(args[1]))
    var d = Int(String(args[2]))
    var floor = Int(String(args[3]))
    var r1 = Int(String(args[4]))
    var r2 = Int(String(args[5]))
    var budget = Int(String(args[6]))
    var q_lift = len(args) > 7 and String(args[7]) == "1"
    var l2s = List[List[Int]]()
    l2s.append(List[Int]())
    for first in [Y, Z]:
        for n in range(1, r2 + 1):
            l2s.append(alt(first, n))
    var pats = 0
    var closed = 0
    var regions = 0
    for n1 in range(1, r1 + 1):
        for j in range(len(l2s)):
            var pat = RunPattern(alt(Z, n1), False, l2s[j].copy(), False)
            if s == 1:
                pat.tail_run1 = d
            var t0 = perf_counter_ns()
            var c = cover_pattern_guided(pat, s, d, budget, True, z_floor=floor, q_lift=q_lift)
            pats += 1
            regions += c.regions
            var ok = c.open == 0 and not c.budget_exhausted
            if ok:
                closed += 1
            print("   ", "closed" if ok else "OPEN  ", pat, " regions", c.regions, " open", c.open, " secs", (perf_counter_ns() - t0) // 1000000000, flush=True)
    print("s =", s, " |Delta| >=", abs(d), " Z_2 >=", floor, " runs <=", r1, r2, " q-lift" if q_lift else "", ": patterns", pats, " closed", closed, " regions", regions)

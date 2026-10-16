"""Paired canonical rational-root timings; -I . -I tests, no timing threshold."""
from std.time import perf_counter_ns
from std.testing import assert_equal
from psc.pisot_screen import has_rational_root
from rational_root_reference import has_rational_root as reference_root


def measure(name: String, corpus: List[List[Int]], repeats: Int) raises:
    for p in corpus:
        assert_equal(has_rational_root(p), reference_root(p))
    for trial in range(7):
        var sums = List[Int]()
        for path in range(2):
            var baseline = (trial + path) % 2 == 0
            var checksum = 0
            var start = perf_counter_ns()
            for _ in range(repeats):
                for p in corpus:
                    if baseline:
                        checksum += Int(reference_root(p))
                    else:
                        checksum += Int(has_rational_root(p))
            var elapsed = perf_counter_ns() - start
            print(name, "trial", trial, "baseline", baseline, "ns", elapsed, "calls", repeats * len(corpus), "checksum", checksum)
            sums.append(checksum)
        assert_equal(sums[0], sums[1])


def main() raises:
    var grid = List[List[Int]]()
    for a in range(-4, 5):
        for b in range(-4, 5):
            for c in range(-4, 5):
                grid.append([a, b, c, 1])
    measure("cubic_grid", grid, 2)
    var many = List[List[Int]]()
    many.append([5040, -100, 20, -5, 1])
    many.append([36, 0, 1])
    measure("many_divisors_no_root", many, 100)
    var large = List[List[Int]]()
    large.append([-1000003, 1, -1000003, 1])
    large.append([1000003, 1, 1000003, 1])
    measure("large_signed_roots", large, 100)
    var zero = List[List[Int]]()
    zero.append([0, -7, 0, 1])
    measure("zero_constant", zero, 10000)
    print("Exact per-polynomial results and all timed checksums agree")

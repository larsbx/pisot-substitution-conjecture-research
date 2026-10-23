"""Class-A gap datasets and regime fits: storage contract, agreement with proved carriers, refusals."""
from std.os import makedirs
from std.os.path import exists
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.class_a_gap_dataset import extend_dataset, header, load_dataset, members, typed_intervals
from psc.class_a_gap_regimes import LOW, MIDDLE, fit_regime
from psc.class_a_line import ALine
from psc.class_a_ray_tables import ray_tables, tabulated_rays

comptime DIR = "build/test-class-a-gap"


def read(path: String) raises -> String:
    with open(path, "r") as f:
        return f.read()


def write(path: String, text: String) raises:
    with open(path, "w") as f:
        f.write(text)


def refuses_load(path: String, d: Int, eps: Int) -> Bool:
    try:
        _ = load_dataset(path, d, eps)
    except:
        return True
    return False


def main() raises:
    if not exists(DIR):
        makedirs(DIR)
    # Storage contract: worker-count invariance, idempotent rerun, exact resume.
    var one = String(DIR) + "/w1"
    var four = String(DIR) + "/w4"
    for dir in [one, four]:
        if not exists(dir):
            makedirs(dir)
        write(dir + "/labels-d4-eps1.txt", header(4, 1))
    var wanted = members(4, 1, 5, 7)
    _ = extend_dataset(one + "/labels-d4-eps1.txt", 4, 1, wanted, 1, 64)
    _ = extend_dataset(four + "/labels-d4-eps1.txt", 4, 1, wanted, 4, 3)
    var full = read(four + "/labels-d4-eps1.txt")
    assert_equal(read(one + "/labels-d4-eps1.txt"), full)
    assert_equal(extend_dataset(four + "/labels-d4-eps1.txt", 4, 1, wanted, 4, 3), 0)
    var cut = full.find("M 25 ")
    write(one + "/labels-d4-eps1.txt", String(full[byte=0:cut]))
    assert_equal(extend_dataset(one + "/labels-d4-eps1.txt", 4, 1, wanted, 4, 3), 7)   # n = 25..31
    assert_equal(read(one + "/labels-d4-eps1.txt"), full)
    # Refusals: truncated block, foreign header, row lengths against the vertex count.
    var bad = String(DIR) + "/bad.txt"
    write(bad, String(full[byte=0:full.byte_length() - 30]))
    assert_true(refuses_load(bad, 4, 1))
    write(bad, full)
    assert_true(refuses_load(bad, 4, -1))
    write(bad, full.replace("M 20 288 ", "M 20 289 "))
    assert_true(refuses_load(bad, 4, 1))
    var dup = False
    try:
        _ = typed_intervals([[0, 0, 0, 0, 1], [0, 0, 0, 0, 1]])
    except:
        dup = True
    assert_true(dup)
    # Agreement with the proved d=4 carriers from every ray's floor: the stored
    # label set is the carrier evaluated at l.
    for eps in [1, -1]:
        var path = String(DIR) + "/labels-d4-eps" + String(eps) + ".txt"
        var floor = 0
        for spec in tabulated_rays():
            if spec[0] == 4 and spec[1] == eps:
                floor = max(floor, spec[3])
        var l_lo = (floor + 3) // 4
        _ = extend_dataset(path, 4, eps, members(4, eps, l_lo, l_lo + 1), 4, 16)
        var checked = 0
        for rec in load_dataset(path, 4, eps):
            var l = rec.n // 4
            var proved = List[List[Int]]()
            for row in ray_tables(ALine(4, eps, rec.n % 4))[0]:
                proved.append([row[0], row[1], row[2], row[3], row[4] * l + row[5], row[6] * l + row[7]])
            assert_equal(len(proved), len(rec.rows))
            for i in range(len(proved)):
                assert_equal(proved[i], rec.rows[i])
            checked += 1
        assert_equal(checked, 8)
    # Fitter: a single gap fits each regime; a corrupted endpoint refuses.
    var fit = fit_regime(1, LOW, 1, 0, 4, 4, 5, four)
    assert_true(fit.ok)
    assert_equal(fit.samples, 3)
    var corrupt = String(DIR) + "/corrupt"
    if not exists(corrupt):
        makedirs(corrupt)
    var lines = full.splitlines()
    var text = String()
    var in25 = False
    var bumped = False
    for line in lines:
        var s = String(line)
        if s.startswith("M "):
            in25 = s.startswith("M 25 ")
            if in25:
                var m = s.split(" ")
                s = "M 25 " + String(Int(m[2]) + 1) + " " + String(m[3]) + " " + String(m[4])
        elif in25 and not bumped and s.startswith("R "):
            var r = s.split(" ")
            s = "R " + String(r[1]) + " " + String(r[2]) + " " + String(r[3]) + " " + String(r[4]) + " " + String(r[5]) + " " + String(Int(r[6]) + 1)
            bumped = True
        text += s + "\n"
    write(corrupt + "/labels-d4-eps1.txt", text)
    var refused = fit_regime(1, LOW, 1, 0, 4, 4, 5, corrupt)
    assert_true(not refused.ok)
    assert_true("not affine" in refused.reason)
    assert_true(not fit_regime(1, MIDDLE, 9, 9, 4, 4, 5, four).ok)   # an empty regime is not a fit
    require_contract("class-A gap label datasets: complete-graph label sets stored losslessly as typed k-intervals, byte-identical at 1 and 4 workers, idempotent and exactly resumable, refusing truncated, foreign and inconsistent files; equal to the proved d=4 carriers from every ray's floor; regime fits solve every endpoint exactly over Q with integer coefficients and refuse a corrupted endpoint and an empty regime; finite observation, not uniform in d")

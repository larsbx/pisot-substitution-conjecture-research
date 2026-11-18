"""Census of the source seam ceiling over the unit members of the PIP corpus.

Each `positive:` line is a unit specimen whose ceiling is positive at an
order relevant to `epsilon = (det M)^m`: order one for `det M = +1`, orders
one or two for `det M = -1`. The summary lines are histograms keyed by
`8 * (ceiling + 4) + (whole + 4)` at orders one and two, split by sign of
the determinant. Finite corpus evidence only; no strict carrier is built.
"""

from psc.corpus import pip_corpus
from psc.histogram import Histogram
from psc.seam_correction_ceiling import seam_ceiling


def main() raises:
    var corpus = pip_corpus()
    var units = 0
    var interior = 0
    var relevant = 0
    var by_det = List[List[Histogram]]()
    for _ in range(2):
        by_det.append([Histogram(64), Histogram(64)])
    for s in range(len(corpus)):
        var det = corpus[s].incidence.det()
        if det != 1 and det != -1:
            continue
        units += 1
        var c = seam_ceiling(corpus[s].sigma)
        if len(c.periods) > 0:
            interior += 1
        var side = 0 if det == 1 else 1
        for d in range(1, 3):
            by_det[side][d - 1].record(8 * (c.at(c.ceiling, d) + 4) + c.at(c.whole, d) + 4)
        var hit = c.at(c.ceiling, 1) > 0 or (det == -1 and c.at(c.ceiling, 2) > 0)
        if hit:
            relevant += 1
            print(
                "positive:", corpus[s].label(), "det", det, "sigma", corpus[s].sigma,
                "periods", c.periods, "ceiling", c.ceiling, "whole", c.whole,
            )
    for side in range(2):
        for d in range(1, 3):
            print(by_det[side][d - 1].line(String("det", "+1" if side == 0 else "-1", " order ", d, " ceiling/whole")))
    print("units", units, "interior", interior, "relevant positive ceiling", relevant)

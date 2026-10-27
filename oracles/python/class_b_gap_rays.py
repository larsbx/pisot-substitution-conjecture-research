"""Fit class-B leftover-gap ray carriers (step 2b) from exact native label sets.

A proof *target*, not evidence: the carriers are certified, or refused, by
psc.class_b_ray_certificate. Each ray is fitted as in step 1
(class_b_label_rays.audit): the earliest floor whose first two members predict
every later member of the residue class. A fit must be checked on at least two
members beyond the two that synthesize it, or it refuses.

    python oracles/python/class_b_gap_rays.py LABELS_DIR plus:6-10 minus:4-7 --out carriers.json
"""
from pathlib import Path
import argparse
import json
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from class_b_label_rays import intervals, read  # noqa: E402
from class_b_regime_probe import fit_ray  # noqa: E402

MIN_CHECKS = 2


def main():
    p = argparse.ArgumentParser()
    p.add_argument('directory')
    p.add_argument('spans', nargs='+', help='BRANCH:GLO-GHI')
    p.add_argument('--out', required=True)
    a = p.parse_args()
    out = []
    for span in a.spans:
        branch, lo, hi = re.fullmatch(r'(plus|minus):(\d+)-(\d+)', span).groups()
        for gap in range(int(lo), int(hi) + 1):
            files = {int(re.search(r'-q(\d+)\.', f.name)[1]): f
                     for f in Path(a.directory).glob(f'{branch}-g{gap}-q*.labels')}
            for residue in range(gap):
                fit = fit_ray(files, gap, residue)
                if fit is None:
                    raise SystemExit(f'{branch} g={gap} r={residue}: no floor in the exported window')
                q0, members, rows = fit
                if members - 2 < MIN_CHECKS:
                    raise SystemExit(f'{branch} g={gap} r={residue}: fit checked on {members - 2} members')
                first, second = intervals(read(files[q0])[1]), intervals(read(files[q0 + gap])[1])
                slope = sum((y[5] - x[5]) - (y[4] - x[4]) for x, y in zip(first, second))
                out.append(dict(branch=branch, gap=gap, residue=residue, floor=q0, checked=members - 2,
                                qmax=max(files), slope=slope, carrier=rows))
                print(branch, gap, residue, 'floor', q0, 'checked', members - 2, 'rows', len(rows), 'slope', slope)
    Path(a.out).write_text(json.dumps(out, indent=1) + '\n')


if __name__ == '__main__':
    main()

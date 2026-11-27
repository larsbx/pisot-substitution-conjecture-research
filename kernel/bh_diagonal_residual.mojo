"""Deterministic finite residual ranks for independent exact replay.

Run from kernel: mojo run -I . bh_diagonal_residual.mojo > residual-ranks.csv
The 10,000-state and 30,000-edge per-parameter caps refuse without a verdict.
Rows include uncovered square states; they are not coincidence refutations.
"""
from psc.bh_diagonal_residual import (
    build_residual_certificate, pair_index, verify_residual_certificate,
)


def main() raises:
    print("r,z,y,rank,next_t")
    for r in [12, 13, 15, 16, 18, 20, 32]:
        var certificate = build_residual_certificate(r, 10000, 30000)
        _ = verify_residual_certificate(certificate)
        for z in range(-r, r + 1):
            for y in range(-r, r + 1):
                var i = pair_index(r, z, y)
                print(r, z, y, certificate.ranks[i], certificate.next_t[i], sep=",")

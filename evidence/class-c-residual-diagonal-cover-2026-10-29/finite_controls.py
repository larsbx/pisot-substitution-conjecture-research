#!/usr/bin/env python3
"""Independent finite class-C residual diagonal controls, not uniform BH.

All graphs use the exact, unoptimized rational-interval oracle introduced
in the previous PR. Sample coverage alone proves nothing beyond these
specific (d,n), and different counts disprove a globally constant label
set across a line, not BH.
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent /
                       "class-c-residual-domain-2026-10-29"))
from exact_oracle import ExactClassC, pip_claim

EXPECTED = {
    (1,2): (204,204,204),
    (1,3): (228,228,228),
    (1,4): (180,180,180),
    (1,5): (196,196,196),
    (1,6): (270,278,278),
    (1,7): (286,268,276),
    (-1,2): (222,222,222),
    (-1,3): (238,238,238),
    (-1,4): (212,212,212),
    (-1,5): (226,226,226),
    (-1,6): (260,254,252),
    (-1,7): (262,256,250),
}
# Typed row counts for j=2..5, independent from the vertex counts.
TYPED = {
    (1,2): 85, (1,3): 103, (1,4): 85, (1,5): 101,
    (-1,2): 89, (-1,3): 105, (-1,4): 109, (-1,5): 115,
}
# Fixed-format SHA256 receipts of the full concatenated R-lines at d=6.
DIGEST = {
    (1,2): "10c245fe80787d678dfd7be845444218e8bb46a4447f1af6b55faf067485456b",
    (1,3): "68619dff994399aca463e4bdc418e272fb2afcd01ab48982d2ca2c036275260a",
    (1,4): "3a5deff107688ff744e14f786c2e58dc5f5ac98c179dd14aa2f24cbefe0669f2",
    (1,5): "83135c604d7d7a9c4da9c56ffb33ff7dc9da46a1593f3737a9a145a500df58ab",
    (-1,2): "82c463df520d7c44d68e5aa13595c57a784b6a2d2ee4441822ff451e2c6be929",
    (-1,3): "0039c33002de729bbf76a115cf3ad330ace64ff9b0775eaae3d49480bb72267b",
    (-1,4): "4d56bc1090b32923a78ae8b8541db17ea38f0fa18101f02344c224988616e45d",
    (-1,5): "7702098a326ad5516056d3ddf18b348ce1b376983222671993f8fcb687ad04c3",
}

def main():
    import hashlib
    for eps in (1,-1):
        for j in range(2,8):
            baseline = None
            seen = []
            for i,d in enumerate((6,7,8)):
                n = 4*d+(4 if eps==-1 else 0)-j
                assert pip_claim(d,eps,n)["pip"]
                graph = ExactClassC(d,eps,n).graph()
                assert graph["all_hit"] and graph["unhit"]==0
                assert graph["vertices"]==EXPECTED[(eps,j)][i]
                if j<=5:
                    assert graph["typed_rows"]==TYPED[(eps,j)]
                    assert graph["label_digest"]==DIGEST[(eps,j)]
                    if baseline is None:baseline=graph["rows_text"]
                    else:assert graph["rows_text"]==baseline
                seen.append((d,n,graph["vertices"],graph["typed_rows"],
                             hashlib.sha256(graph["rows_text"].encode()).hexdigest()[:16]))
            if j>=6:
                assert seen[0][2]!=seen[1][2], "negative control must truly vary"
            print("FINITE_ONLY",eps,j,seen,flush=True)
    print("PASS: 36 finite BH graphs, 24 full-label equalities, four variable-label controls")

if __name__=="__main__":
    main()

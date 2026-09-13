"""EXPLORATORY (not a certificate): for a sample of the PIP corpus, find the
least prefix length k <= KMAX such that every non-coincidence overlap type of
the Sirvent--Solomyak graph G_O(T, x(W)), W = u[:k], u a fixed point of a
prolongable power of sigma, is a vertex type of the seed-patch graph O_sigma.
Level-0 types come from a finite prefix of u (uncertified factor set).
Usage: python3 scripts/oa_type_inclusion_explore.py [stride] [kmax]"""
import sys, time
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1] / 'src'))
from psc_research.pip_screen import pip_corpus
from psc_research.oa_overlap_graph import type_inclusion_report

stride = int(sys.argv[1]) if len(sys.argv) > 1 else 10
kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 8
corpus = pip_corpus()
sample = corpus[::stride]
print("sample size:", len(sample), "kmax:", kmax, flush=True)
t0 = time.time(); hist = {}; none = []
for idx, sigma in enumerate(sample):
    found = None
    for k in range(1, kmax + 1):
        r = type_inclusion_report(sigma, k=k, prefix_len=6000, window=14)
        assert r["oa_all_productive"], ("nonproductive G_O type", sigma, k)
        if r["oa_minus_seed_noncoincidence"] == 0:
            found = k
            break
    hist[found] = hist.get(found, 0) + 1
    if found is None:
        none.append(sigma); print("NO INCLUSION up to kmax:", sigma, flush=True)
    if idx % 50 == 0:
        print("progress", idx, "elapsed", round(time.time() - t0), "s", flush=True)
print("least k with type inclusion (None = not found up to kmax):", sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0])))
print("specimens without inclusion up to kmax:", len(none))

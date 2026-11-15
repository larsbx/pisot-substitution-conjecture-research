"""Export the exact physical mass and loss of every retained overlap."""

from psc.c4_overlap_physical_mass import certify_physical_mass
from psc.c4_pair_overlap_new_incidence import build_new_incidence_graph


def main() raises:
    print("schema c4-overlap-physical-mass-v1")
    for source in range(12):
        var graph = build_new_incidence_graph(source)
        var report = certify_physical_mass(graph)
        var mass = report[0].copy()
        var deficit = report[1].copy()
        var witnesses = report[2].copy()
        var losses = 0
        var edges = 0
        for i in range(len(graph.states)):
            var m = mass[i].copy()
            var d = deficit[i].copy()
            if d[0] != 0 or d[1] != 0 or d[2] != 0:
                losses += 1
            edges += len(graph.rows[i])
            print("row", source, i, m[0], m[1], m[2], d[0], d[1], d[2])
        for witness in witnesses:
            print("block", source, witness[0], witness[1], witness[2])
        print("graph", source, len(graph.states), edges, losses, len(witnesses))

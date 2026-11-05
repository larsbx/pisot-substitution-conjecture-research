"""Canonical paired-overlap SCC certificate driver."""

from psc.c4_pair_overlap_new_incidence import build_new_incidence_graph
from psc.c4_overlap_scc_obstruction import (
    PositiveSpectralWitness, analyze_overlap_system, declared_roots_zero,
    make_overlap_scale,
)


def main() raises:
    var spectral_scale = make_overlap_scale()
    print("schema c4-overlap-scc-obstruction-v1")
    print("scale 1 -4 5 -7 1 63 10 32 5")
    print("budget 768 101 103 107")
    for source in range(12):
        var graph = build_new_incidence_graph(source)
        var report = analyze_overlap_system(graph.rows,[0,1,2],spectral_scale,List[PositiveSpectralWitness]())
        if not declared_roots_zero(report):
            raise Error("new source remains unresolved by SCC certificates; inconclusive")
        var partition = report.partition.copy()
        var largest = 0
        var degree_count = 0
        var modular_count = 0
        var unresolved = 0
        var zero_states = 0
        var edges = 0
        for row in graph.rows:
            edges += len(row)
        for c in range(len(partition.members)):
            var size = len(partition.members[c])
            if size > largest:
                largest = size
            if report.exclusion[c] == 1:
                degree_count += 1
            elif report.exclusion[c] == 2:
                modular_count += 1
            elif report.spectral[c] == 0:
                unresolved += 1
            if report.zero[c]:
                zero_states += size
        print("graph",source,len(graph.states),edges,graph.residue_rejections,graph.box_rejections,graph.carrier_rejections,len(partition.members),largest,degree_count,modular_count,unresolved,zero_states,1 if report.zero[partition.component_of[0]] else 0,1 if report.zero[partition.component_of[1]] else 0,1 if report.zero[partition.component_of[2]] else 0)
        for vertex in range(len(graph.states)):
            var state = graph.states[vertex].copy()
            print("node",source,vertex,state[0],state[1],state[2],state[3],state[4])
            var row = String("row ")+String(source)+String(" ")+String(vertex)+String(" ")+String(len(graph.rows[vertex]))
            for target in graph.rows[vertex]:
                row += String(" ")+String(target)
            print(row)
        for c in range(len(partition.members)):
            print("component",source,c,len(partition.members[c]),report.exclusion[c],report.spectral[c],1 if report.zero[c] else 0,1 if report.budget_refused[c] else 0,len(report.attempts[c]))
            var members = String("members ")+String(source)+String(" ")+String(c)+String(" ")+String(len(partition.members[c]))
            for vertex in partition.members[c]:
                members += String(" ")+String(vertex)
            print(members)
            var dag = String("dag ")+String(source)+String(" ")+String(c)+String(" ")+String(len(partition.outgoing[c]))
            for target in partition.outgoing[c]:
                dag += String(" ")+String(target)
            print(dag)
            for attempt in report.attempts[c]:
                print("modtry",source,c,attempt.prime,attempt.rank,attempt.determinant)

"""Complete native packet for all 18 source orders, including prefix period three."""
from psc.c4_pair_overlap_graph import (
    build_source_class_graph, source_class_step, construct_weights_at_rate,
)


def main() raises:
    print("schema c4-pair-overlap-source-class-v1")
    for index in range(18):
        var step = source_class_step(index)
        var numerator = 102 if step == 2 else 233
        var graph = build_source_class_graph(index)
        var result = construct_weights_at_rate(graph,numerator,step)
        var weights = result[0].copy()
        var edges = 0
        for i in range(len(graph.rows)):
            edges += len(graph.rows[i])
        print("graph",index,step,len(graph.states),edges,graph.residue_rejections,graph.box_rejections,numerator,20)
        for i in range(len(graph.states)):
            var s = graph.states[i].copy()
            print("node",index,i,s[0],s[1],s[2],s[3],s[4],weights[i])
            var line = String("row ")+String(index)+String(" ")+String(i)+String(" ")+String(len(graph.rows[i]))
            for j in graph.rows[i]:
                line += String(" ")+String(j)
            print(line)

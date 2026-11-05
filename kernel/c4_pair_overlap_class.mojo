"""Full canonical packet for all 18 checked source-word orders."""
from psc.c4_pair_overlap_attractor import build_source_order_graph, construct_attractor_weights


def main() raises:
    print("schema c4-pair-overlap-class-v1")
    for index in range(18):
        var graph = build_source_order_graph(index)
        var result = construct_attractor_weights(graph,4000)
        var weights = result[0].copy()
        var edges = 0
        for i in range(len(graph.rows)):
            edges += len(graph.rows[i])
        print("graph",index,len(graph.states),edges,graph.residue_rejections,graph.box_rejections,result[1],102,20)
        for i in range(len(graph.states)):
            var state = graph.states[i].copy()
            print("node",index,i,state[0],state[1],state[2],state[3],state[4],weights[i])
            var line = String("row ")+String(index)+String(" ")+String(i)+String(" ")+String(len(graph.rows[i]))
            for j in graph.rows[i]:
                line += String(" ")+String(j)
            print(line)

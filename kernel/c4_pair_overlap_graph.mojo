"""Full deterministic native packet; no SC witness or arbitrary density input."""
from psc.c4_pair_overlap_graph import build_pair_graph, construct_pair_weights


def main() raises:
    print("schema c4-pair-overlap-graph-v1")
    for fixture in range(2):
        var graph = build_pair_graph(fixture)
        var result = construct_pair_weights(graph)
        var weights = result[0].copy()
        var iterations = result[1]
        var edges = 0
        for i in range(len(graph.rows)):
            edges += len(graph.rows[i])
        var numerator = 99 if fixture == 0 else 101
        print("graph",fixture,len(graph.states),edges,graph.residue_rejections,graph.box_rejections,iterations,numerator,20)
        for i in range(len(graph.states)):
            var state = graph.states[i].copy()
            print("node",fixture,i,state[0],state[1],state[2],state[3],state[4],weights[i])
            var line = String("row ")+String(fixture)+String(" ")+String(i)+String(" ")+String(len(graph.rows[i]))
            for j in graph.rows[i]:
                line += String(" ")+String(j)
            print(line)

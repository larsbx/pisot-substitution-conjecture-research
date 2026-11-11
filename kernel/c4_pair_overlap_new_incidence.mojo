"""Complete native packet for the twelve-source x^3-x^2-3x-2 class."""

from psc.c4_pair_overlap_new_incidence import (
    NEW_RATE_DENOMINATOR, NEW_RATE_NUMERATOR, build_new_incidence_graph,
    certify_uniform_upper_tenth, construct_new_weights, make_new_model,
)


def main() raises:
    var model = make_new_model()
    certify_uniform_upper_tenth()
    print("schema c4-pair-overlap-new-incidence-v1")
    print("model",model.rx,model.ry,12,556693,556694,398160,398161,1000000)
    var pair = 0
    for first in range(3):
        for second in range(first,3):
            var box = model.carriers[pair].copy()
            print("carrier",first,second,box.lower[0],box.upper[0],box.lower[1],box.upper[1],box.lower[2],box.upper[2],box.capacity)
            pair += 1
    for index in range(12):
        var graph = build_new_incidence_graph(index)
        var result = construct_new_weights(graph)
        var weights = result[0].copy()
        var edges = 0
        for row in graph.rows:
            edges += len(row)
        print("graph",index,len(graph.states),edges,graph.residue_rejections,graph.box_rejections,graph.carrier_rejections,result[1],NEW_RATE_NUMERATOR,NEW_RATE_DENOMINATOR)
        for i in range(len(graph.states)):
            var state = graph.states[i].copy()
            print("node",index,i,state[0],state[1],state[2],state[3],state[4],weights[i])
            var line = String("row ")+String(index)+String(" ")+String(i)+String(" ")+String(len(graph.rows[i]))
            for target in graph.rows[i]:
                line += String(" ")+String(target)
            print(line)

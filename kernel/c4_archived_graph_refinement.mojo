"""Complete named graph/address/ancestry packet for independent replay."""
from psc.c4_archived_graph_refinement import build_archived_refinement, verify_archived_contraction
from psc.c4_pair_overlap_graph import construct_pair_weights


def main() raises:
    print("schema c4-archived-graph-refinement-v1")
    for fixture in range(2):
        var binding = build_archived_refinement(fixture)
        var result = construct_pair_weights(binding.graph)
        var weights = result[0].copy()
        var iterations = result[1]
        var gap = verify_archived_contraction(binding,weights)
        var maximum_depth = 0
        for depth in binding.depths:
            if depth > maximum_depth:
                maximum_depth = depth
        print("graph",fixture,binding.period,binding.radii[0],binding.radii[1],binding.direction,len(binding.graph.states),binding.edges,binding.graph.residue_rejections,binding.graph.box_rejections,binding.swapped,binding.repeated,maximum_depth,iterations,gap)
        for parent in range(3):
            var line = String("image ")+String(fixture)+String(" ")+String(parent)+String(" ")+String(len(binding.images[parent]))
            for letter in binding.images[parent]:
                line += String(" ")+String(letter)
            print(line)
        for i in range(len(binding.digits)):
            var line = String("digit ")+String(fixture)+String(" ")+String(i)
            for value in binding.digits[i]:
                line += String(" ")+String(value)
            print(line)
        for i in range(len(binding.graph.states)):
            var state = binding.graph.states[i].copy()
            print("node",fixture,i,state[0],state[1],state[2],state[3],state[4],weights[i],binding.births[i][0],binding.births[i][1],binding.depths[i])
            print("row",fixture,i,len(binding.slots[i]))
            for ordinal in range(len(binding.slots[i])):
                var slot = binding.slots[i][ordinal].copy()
                print("slot",fixture,i,ordinal,slot[0],slot[1],slot[2],slot[3])

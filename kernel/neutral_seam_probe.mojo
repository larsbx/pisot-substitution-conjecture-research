"""Bounded exact source-graph probe; no strict-component existence verdict.

Enumerates the standing 4554-specimen PIP corpus in canonical order, retaining
unit specimens with source eventual-range Betti number at least two. Uses the
complete certified prototile box for each retained source and reports source
product seam corrections. This is not the correction of a strict carrier.
"""

from psc.corpus import pip_corpus
from psc.c4_geometric_f import PrototileMap, StableRadiiCache, decide_geometric_f_with, interior_address
from psc.rank_two_parity import er_graph_map
from psc.neutral_seam_budget import source_orbit_budget


def main() raises:
    var corpus = pip_corpus()
    var boxes = StableRadiiCache()
    var screened = 0
    var plus_positive = 0
    var minus_selected_positive = 0
    var plus_budget_positive = 0
    var minus_budget_positive = 0
    var plus_omitted_negative = 0
    for specimen in corpus:
        var det = specimen.incidence.det()
        if det != 1 and det != -1:
            continue
        var graph = er_graph_map(specimen.sigma)
        if graph.betti() < 2:
            continue
        screened += 1
        var m = PrototileMap(specimen.sigma)
        var verdict = decide_geometric_f_with(m, boxes)
        var plus = 0
        var minus = 0
        var plus_bound = 0
        var minus_bound = 0
        var periods = List[Int]()
        for cycle in verdict.cycles:
            var q = cycle.period()
            periods.append(q)
            var bp = source_orbit_budget(graph, q, 1)
            var bm = source_orbit_budget(graph, q, -1)
            plus += bp
            minus += bm
            plus_bound += max(0, bp)
            minus_bound += max(0, bm)
        plus_budget_positive += Int(plus_bound > 0)
        minus_budget_positive += Int(det == -1 and minus_bound > 0)
        if plus_bound > max(0, plus):
            plus_omitted_negative += 1
            if plus_omitted_negative <= 3:
                print("omitted_negative_orbit", specimen.index, specimen.label(), specimen.sigma,
                      "det", det, "betti", graph.betti(), "periods", periods,
                      "correction", plus, minus, "optional", plus_bound, minus_bound,
                      "ER", graph.edges, "edge_map", graph.edge_image, "vertices", graph.vertices,
                      "vertex_map", graph.vertex_image)
                for cycle in verdict.cycles:
                    var address = interior_address(m, cycle)
                    print("omission_witness", "states", cycle.states, "indices", cycle.indices,
                          "letter", address.letter, "v", address.vector, "period", address.period,
                          "prefix_parikh", address.prefix_parikh, "prefix_length", address.prefix_length,
                          "image_length", address.image_length)
        if plus > 0 or (det == -1 and minus > 0):
            plus_positive += Int(plus > 0)
            minus_selected_positive += Int(det == -1 and minus > 0)
            if plus_positive + minus_selected_positive <= 12:
                print("positive_source_product", specimen.index, specimen.label(), specimen.sigma,
                      "det", det, "betti", graph.betti(), "periods", periods,
                      "correction", plus, minus, "optional", plus_bound, minus_bound,
                      "ER", graph.edges, "edge_map", graph.edge_image, "vertices", graph.vertices,
                      "vertex_map", graph.vertex_image)
                for cycle in verdict.cycles:
                    var address = interior_address(m, cycle)
                    print("witness", "states", cycle.states, "indices", cycle.indices,
                          "letter", address.letter, "v", address.vector, "period", address.period,
                          "prefix_parikh", address.prefix_parikh, "prefix_length", address.prefix_length,
                          "image_length", address.image_length)
    print("complete", "corpus", len(corpus), "unit_betti_at_least_two", screened,
          "plus_positive", plus_positive, "det_minus_minus_positive", minus_selected_positive,
          "plus_optional_positive", plus_budget_positive, "det_minus_minus_optional_positive", minus_budget_positive,
          "plus_omitted_negative", plus_omitted_negative,
          "certified_matrices", boxes.distinct_matrices())

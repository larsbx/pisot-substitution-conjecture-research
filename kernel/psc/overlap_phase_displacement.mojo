"""Exact support measurements for cyclic phases of a PIP3 overlap component.

The necessary bounds for closed diagonal-free phases are proved in
docs/overlap-phase-displacement-2026-11-17.md. Phase measurement also applies
to open recurrent subgraphs, which do not satisfy the closure hypothesis.
"""

from finite_graph.signing import SignedEdge, cyclic_classes, directed_period, positive_edge
from psc.overlap_seed_patch import SeedOverlapAutomaton
from psc.perron_field3 import CubicElt, TileLengths3, cubic_add_checked, cubic_sub_checked


struct DisplacementPhase(Copyable, Movable):
    var distinct_offsets: Int
    var aligned: Bool
    # For a connected support, widths in the three integral coordinates.
    # An empty list records disconnected support.
    var widths: List[Int]

    def __init__(out self, distinct_offsets: Int, aligned: Bool, var widths: List[Int]):
        self.distinct_offsets = distinct_offsets
        self.aligned = aligned
        self.widths = widths^

    def meets_necessary_support(self) -> Bool:
        """Necessary for a closed diagonal-free phase under the PIP3 hypotheses."""
        if len(self.widths) != 3:
            return False
        var minimum = 1
        for width in self.widths:
            if width < 2:
                return False
            minimum += width
        if not self.aligned:
            minimum = max(minimum, 8)
        return self.distinct_offsets >= minimum


def measure_displacement_support(
    offsets: List[CubicElt], lengths: TileLengths3
) raises -> DisplacementPhase:
    """Measure relative lattice coordinates by walking exact unit steps.

    The three lengths must encode the lattice injectively. Relative
    coordinates suffice because the widths are translation invariant.
    """
    if len(offsets) == 0:
        raise Error("cyclic displacement phase must be nonempty")
    var support = Dict[CubicElt, List[Int]]()
    for offset in offsets:
        support[offset] = List[Int]()
    var aligned = CubicElt() in support
    var queue: List[CubicElt] = [offsets[0]]
    support[offsets[0]] = [0, 0, 0]
    var minima: List[Int] = [0, 0, 0]
    var maxima: List[Int] = [0, 0, 0]
    var head = 0
    while head < len(queue):
        var current = queue[head]
        head += 1
        var point = support[current].copy()
        for axis in range(3):
            var length = lengths.at(axis)
            for step in [-1, 1]:
                var next = cubic_add_checked(current, length) if step == 1 else cubic_sub_checked(current, length)
                if next not in support or len(support[next]) != 0:
                    continue
                var moved = point.copy()
                moved[axis] += step
                minima[axis] = min(minima[axis], moved[axis])
                maxima[axis] = max(maxima[axis], moved[axis])
                support[next] = moved^
                queue.append(next)

    var widths = List[Int]()
    if len(queue) == len(support):
        for axis in range(3):
            widths.append(maxima[axis] - minima[axis])
    return DisplacementPhase(len(support), aligned, widths^)


def overlap_phase_displacements(
    graph: SeedOverlapAutomaton, lengths: TileLengths3, component: List[Int]
) raises -> List[DisplacementPhase]:
    """Use the induced edges of a supplied nonempty recurrent SCC or subgraph.

    An open subgraph can have small support. For the theorem's contrapositive
    the supplied component must be closed in the full literal graph.
    """
    if graph.capped or len(component) == 0:
        raise Error("phase measurement requires a complete graph and a nonempty component")
    var indices = Dict[Int, Int]()
    for i in range(len(component)):
        var source = component[i]
        if source < 0 or source >= graph.size() or source in indices:
            raise Error("invalid phase component index")
        indices[source] = i
    var edges = List[SignedEdge]()
    for source in component:
        for target in graph.adj[source]:
            if target in indices:
                edges.append(positive_edge(indices[source], indices[target]))

    var period = directed_period(len(component), edges)
    var classes = cyclic_classes(len(component), edges, period)
    var offsets = List[List[CubicElt]]()
    for _ in range(period):
        offsets.append(List[CubicElt]())
    for i in range(len(component)):
        offsets[classes[i]].append(graph.states[component[i]].shift)
    var out = List[DisplacementPhase]()
    for phase in offsets:
        out.append(measure_displacement_support(phase, lengths))
    return out^

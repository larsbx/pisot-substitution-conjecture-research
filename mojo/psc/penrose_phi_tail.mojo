"""Exact Penrose H_tail prefix-Phi increment cocycle.

Source import from the closed Penrose pilot:

  E_short -> E_minus -> E_plus -> E_short
  O_short -> O_minus -> O_plus -> O_short

On both branch-preserving 3-cycles the exact prefix-Phi increments are

  1, 1, 2 - phi.

The three-step loop gain is therefore 4 - phi.

Important: this is an EDGE COCYCLE on the recurrent quotient, not a
single-valued state potential on H_tail. A nonzero loop gain rules out a
single-valued potential whose edge differences are these increments. The
exact-prefix lift remembers the accumulated height across repeated laps.

Coordinates use the integral basis (1, phi) with phi^2 = phi + 1.
No floating point or angle language is used.
"""


struct PenrosePhiElt(
    ImplicitlyCopyable, Copyable, Movable, Equatable, Hashable, Writable
):
    var a0: Int
    var a1: Int

    def __init__(out self, a0: Int = 0, a1: Int = 0):
        self.a0 = a0
        self.a1 = a1

    def __eq__(self, other: PenrosePhiElt) -> Bool:
        return self.a0 == other.a0 and self.a1 == other.a1

    def __ne__(self, other: PenrosePhiElt) -> Bool:
        return not (self == other)

    def __add__(self, other: PenrosePhiElt) -> PenrosePhiElt:
        return PenrosePhiElt(self.a0 + other.a0, self.a1 + other.a1)

    def __sub__(self, other: PenrosePhiElt) -> PenrosePhiElt:
        return PenrosePhiElt(self.a0 - other.a0, self.a1 - other.a1)

    def is_zero(self) -> Bool:
        return self.a0 == 0 and self.a1 == 0

    def norm(self) -> Int:
        """Field norm a^2 + a*b - b^2 in Z[phi]."""
        return self.a0 * self.a0 + self.a0 * self.a1 - self.a1 * self.a1

    def write_to[W: Writer](self, mut w: W):
        w.write("(", self.a0, ",", self.a1, ")")


alias E_SHORT = 0
alias E_MINUS = 1
alias E_PLUS = 2
alias O_SHORT = 3
alias O_MINUS = 4
alias O_PLUS = 5


struct PenrosePhiEdge(ImplicitlyCopyable, Copyable, Movable):
    var source: Int
    var target: Int
    var gain: PenrosePhiElt

    def __init__(out self, source: Int, target: Int, gain: PenrosePhiElt):
        self.source = source
        self.target = target
        self.gain = gain


def h_tail_phi_edges() -> List[PenrosePhiEdge]:
    """The source-grounded Phi-increment channel on both H_tail components."""
    var one = PenrosePhiElt(1, 0)
    var two_minus_phi = PenrosePhiElt(2, -1)
    return [
        PenrosePhiEdge(E_SHORT, E_MINUS, one),
        PenrosePhiEdge(E_MINUS, E_PLUS, one),
        PenrosePhiEdge(E_PLUS, E_SHORT, two_minus_phi),
        PenrosePhiEdge(O_SHORT, O_MINUS, one),
        PenrosePhiEdge(O_MINUS, O_PLUS, one),
        PenrosePhiEdge(O_PLUS, O_SHORT, two_minus_phi),
    ]


def h_tail_branch_cycle(branch: Int) raises -> List[PenrosePhiEdge]:
    var edges = h_tail_phi_edges()
    var out = List[PenrosePhiEdge]()
    if branch == 0:
        for i in range(3):
            out.append(edges[i])
        return out^
    if branch == 1:
        for i in range(3, 6):
            out.append(edges[i])
        return out^
    raise Error("Penrose H_tail branch must be 0 (EQ) or 1 (OPP)")


def cycle_gain(edges: List[PenrosePhiEdge]) -> PenrosePhiElt:
    var total = PenrosePhiElt()
    for i in range(len(edges)):
        total = total + edges[i].gain
    return total


def h_tail_period_gain() -> PenrosePhiElt:
    """Exact gain of either recurrent three-step H_tail loop: 4 - phi."""
    return PenrosePhiElt(4, -1)


def phi_state_potential_obstruction() -> Bool:
    """Nonzero recurrent loop gain forbids these increments being state differences."""
    return not h_tail_period_gain().is_zero()

"""Lean data for the ordered double cover of a complete forward BPA."""

from psc.target_packet_report import ints_json
from substitution_dynamics.automaton import Automaton
from substitution_dynamics.balanced_pairs import decompose, seed_states
from substitution_dynamics.substitution import Substitution
from substitution_dynamics.words import Pair


def word_literal(word: List[Int]) -> String:
    var out = String('"')
    for i in range(len(word)):
        out += String(word[i])
    return out + '"'


def ordered_pair(p: Pair) -> String:
    return "decodePair " + word_literal(p.u) + " " + word_literal(p.v)


def emit_forward_row(sigma: Substitution, source: Pair, orbit: Int, reversed: Bool):
    var row = String("  ⟨") + String(orbit) + ", " + ("true" if reversed else "false") + ", "
    row += ordered_pair(source) + ", ["
    if not source.is_coincidence():
        var children = decompose(sigma.apply(source.u), sigma.apply(source.v), sigma.size)
        for i in range(len(children)):
            if i != 0:
                row += ", "
            row += ordered_pair(children[i])
    print(row + "]⟩,")


def emit_forward_carrier(sigma: Substitution, graph: Automaton):
    print("import PscVerif.ForwardCarrier")
    print("open Psc.ForwardCarrier")
    print("def carrier : Certificate := ⟨[", end="")
    for i in range(sigma.size):
        if i != 0:
            print(", ", end="")
        print(ints_json(sigma.images[i]), end="")
    print("], [")
    var seeds = seed_states(sigma.size)
    for i in range(len(seeds)):
        print("  " + ordered_pair(seeds[i]) + ",")
        print("  " + ordered_pair(Pair(seeds[i].v, seeds[i].u)) + ",")
    print("], [")
    for i in range(len(graph.states)):
        ref state = graph.states[i]
        emit_forward_row(sigma, state, i, False)
        if not state.is_coincidence():
            emit_forward_row(sigma, Pair(state.v, state.u), i, True)
    print("]⟩")

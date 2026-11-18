"""Guard literal terminal-child closure and bounded native export semantics."""

from mojo_smoke.claims import require_contract
from psc.forward_carrier import ForwardCarrier, build_forward_carrier, check_carrier, normalized_count, longest_state
from substitution_dynamics.words import Pair


def main() raises:
    var fib: List[List[Int]] = [[0, 1], [0]]
    var tm: List[List[Int]] = [[0, 1], [1, 0]]
    var f = build_forward_carrier(fib, 20, 20)
    assert check_carrier(fib, f)
    assert normalized_count(f) == 2
    assert len(f.states) == 3
    assert longest_state(f) == 2
    # A complete finite Thue-Morse carrier gives no productivity verdict.
    var t = build_forward_carrier(tm, 20, 20)
    assert check_carrier(tm, t)
    assert normalized_count(t) == 1
    assert len(t.states) == 2
    assert len(t.rows[0]) == 2 and len(t.rows[1]) == 2

    var missing_seed = f.copy()
    missing_seed.states[1] = Pair([1], [1])
    assert not check_carrier(fib, missing_seed)
    var missing_exit = f.copy()
    missing_exit.states[2] = Pair([1], [1])
    assert not check_carrier(fib, missing_exit)
    var terminal_edge = f.copy()
    terminal_edge.rows[2].append(0)
    assert not check_carrier(fib, terminal_edge)
    var omitted = f.copy()
    _ = omitted.rows[0].pop()
    assert not check_carrier(fib, omitted)
    var reordered = f.copy()
    var old_first = reordered.rows[0][0]
    reordered.rows[0][0] = reordered.rows[0][1]
    reordered.rows[0][1] = old_first
    assert not check_carrier(fib, reordered)
    var wrong_orientation = t.copy()
    wrong_orientation.rows[0][0] = 1 - wrong_orientation.rows[0][0]
    assert not check_carrier(tm, wrong_orientation)
    var invalid_index = f.copy()
    invalid_index.rows[0][0] = -1
    assert not check_carrier(fib, invalid_index)
    var invalid_letter = f.copy()
    invalid_letter.states[0].u[0] = 2
    assert not check_carrier(fib, invalid_letter)
    var duplicate_factor = f.copy()
    duplicate_factor.rows[0].append(duplicate_factor.rows[0][0])
    assert not check_carrier(fib, duplicate_factor)
    # Exact discovery is deliberately unnecessary: one extra terminal state
    # gives a valid closed superset. It has no outgoing ChildNC edges.
    var superset = f.copy()
    superset.states.append(Pair([1], [1]))
    superset.rows.append(List[Int]())
    assert check_carrier(fib, superset)

    var state_refused = False
    try:
        _ = build_forward_carrier(fib, 1, 20)
    except:
        state_refused = True
    assert state_refused
    var length_refused = False
    try:
        _ = build_forward_carrier(fib, 20, 1)
    except:
        length_refused = True
    assert length_refused
    var zero_refused = False
    try:
        _ = build_forward_carrier(fib, 0, 20)
    except:
        zero_refused = True
    assert zero_refused
    print("forward_carrier controls: 2 baselines, 9 row/state mutations, 1 closed superset, 3 budget refusals passed")
    require_contract("Literal ordered forward carrier: all swap seeds, complete actual rows, terminal coincidences and bounded refusal")

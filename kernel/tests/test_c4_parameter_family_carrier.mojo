"""Canonical exact controls for the ordered 01/10 family carrier."""

from mojo_smoke.claims import require_contract
from psc.forward_carrier import build_forward_carrier
from substitution_dynamics.words import Pair


def family_images(k: Int) -> List[List[Int]]:
    var image: List[Int] = [0]
    for _ in range(k):
        image.append(1)
    image.append(2)
    return [[1], image^, [0, 0, 1]]


def main() raises:
    for k in [2, 3, 4, 5, 8, 16, 30, 64, 137]:
        # The canonical engine constructs all six seeds and verifies literal rows.
        # Slice that closed graph from the requested ordered seed.
        var carrier = build_forward_carrier(family_images(k), 250, 2000)
        var seed = Pair([0, 1], [1, 0])
        var start = -1
        for i in range(len(carrier.states)):
            if carrier.states[i] == seed:
                start = i
                break
        if start < 0:
            raise Error("closed carrier omitted the ordered control seed")

        var seen = List[Bool](length=len(carrier.states), fill=False)
        var queue: List[Int] = [start]
        seen[start] = True
        var head = 0
        var longest = 0
        var occurrences = 0
        while head < len(queue):
            var i = queue[head]
            head += 1
            longest = max(longest, carrier.states[i].length())
            occurrences += len(carrier.rows[i])
            for j in carrier.rows[i]:
                if not seen[j]:
                    seen[j] = True
                    queue.append(j)

        var expected_states = 128 if k == 2 else 60 if k == 3 else 48
        var expected_longest = 53 if k == 2 else 22 if k == 3 else 3 * k + 14
        if len(queue) != expected_states or longest != expected_longest:
            raise Error("unexpected ordered reachable carrier at k=" + String(k))
        print(k, len(queue), longest, occurrences)

    require_contract("complete ordered 01/10 ChildNC closure at the sampled family parameters")

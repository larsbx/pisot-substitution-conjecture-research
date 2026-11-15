"""Complete strict physical-overlap closure of #487's aligned return roots.

No guessed delta box: intern ALL overlapping occurrence children until the
queue exhausts. Exceeding any budget raises and yields no closure receipt.
The 1134-state count and register range are outputs, never search cutoffs.
No arbitrary-exterior-prefix, general C4, G1 or PSC theorem is claimed.
"""
from psc.c4_return_boundary_carrier import ReturnBoundaryCarrier


def verify_perron_enclosure() raises:
    # f(3+t)=t^3+5t^2+7t+1. Shifted exact numerators fit signed Int64.
    var scale = 1000000
    for q in [2839286, 2839287]:
        var t = q - 3 * scale
        var numerator = t*t*t + 5*t*t*scale + 7*t*scale*scale + scale*scale*scale
        if q == 2839286 and numerator != -4131286074344:
            raise Error("lower Perron root sign certificate changed")
        if q == 2839287 and numerator != 1339065412903:
            raise Error("upper Perron root sign certificate changed")
    var qlo = 2839286
    var qhi = 2839287
    var lower_l2 = (qlo*qlo)//scale - 3*qhi + 2*scale
    var upper_l2 = (qhi*qhi+scale-1)//scale - 3*qlo + 2*scale
    if lower_l2 != 1543683 or upper_l2 != 1543693:
        raise Error("outward Perron length bounds changed")
    # f' and f'' are positive on [14/5,3], hence the bracket contains one root.
    # M is primitive; this positive root is its Perron root.


def perron_sign(v: List[Int]) raises -> Int:
    if len(v) != 3:
        raise Error("Perron sign requires three integer coordinates")
    for x in v:
        if x < -1000 or x > 1000:
            raise Error("exact sign arithmetic budget exhausted; no verdict")
    if v == [0, 0, 0]:
        return 0
    # ell=(1,beta-1,beta^2-3beta+2). Outward integer enclosures / 10^6.
    var lo: List[Int] = [1000000, 1839286, 1543683]
    var hi: List[Int] = [1000000, 1839287, 1543693]
    var lower = 0
    var upper = 0
    for i in range(3):
        if v[i] >= 0:
            lower += v[i] * lo[i]
            upper += v[i] * hi[i]
        else:
            lower += v[i] * hi[i]
            upper += v[i] * lo[i]
    if lower > 0:
        return 1
    if upper < 0:
        return -1
    raise Error("Perron interval cannot certify sign; refine rather than discard")


def strict_physical_overlap(x: Int, y: Int, delta: List[Int]) raises -> Bool:
    if x < 0 or x >= 3 or y < 0 or y >= 3 or len(delta) != 3:
        raise Error("invalid physical overlap input")
    var right = delta.copy()
    var left = delta.copy()
    right[y] -= 1
    left[x] += 1
    # Top [ell.delta, ell.delta+ell[x]], bottom [0,ell[y]].
    # Equality at an endpoint is NOT a positive-length overlap.
    return perron_sign(right) < 0 and perron_sign(left) > 0


def _prefix_count(word: List[Int], stop: Int) -> List[Int]:
    var counts: List[Int] = [0, 0, 0]
    for i in range(stop):
        counts[word[i]] += 1
    return counts^


def _find(states: List[List[Int]], state: List[Int]) -> Int:
    for i in range(len(states)):
        if states[i] == state:
            return i
    return -1


struct ReturnOverlapClosure(Copyable, Movable):
    # State row: [top_point_id,bottom_point_id,delta0,delta1,delta2].
    # Edge row: [top_child_ordinal,bottom_child_ordinal,target_state_id].
    var states: List[List[Int]]
    var edges: List[List[List[Int]]]
    var distance: List[Int]
    var initial_count: Int
    var next_letter: List[Int]
    var child_points: List[List[Int]]

    def __init__(out self, cap: Int = 2048) raises:
        if cap < 1 or cap > 2048:
            raise Error("invalid exact saturation budget")
        verify_perron_enclosure()
        var c = ReturnBoundaryCarrier()
        if c.sigma != [[0,1],[1,2,1],[0,1,2]]:
            raise Error("source differs from certified incidence and root")
        self.states = List[List[Int]]()
        self.edges = List[List[List[Int]]]()
        self.distance = List[Int]()
        self.next_letter = List[Int]()
        self.child_points = c.lifted_images()
        self.initial_count = 0
        var mass = List[List[Int]]()
        for j in range(4):
            for d in range(len(c.words[j])):
                self.next_letter.append(c.words[j][d])
                mass.append(_prefix_count(c.words[j], d))
        if len(self.next_letter) != 28 or len(self.child_points) != 28:
            raise Error("parent carrier has changed")
        for top in range(28):
            for bottom in range(28):
                var delta: List[Int] = [
                    mass[top][0]-mass[bottom][0],
                    mass[top][1]-mass[bottom][1],
                    mass[top][2]-mass[bottom][2],
                ]
                if strict_physical_overlap(self.next_letter[top], self.next_letter[bottom], delta):
                    if len(self.states) >= cap:
                        raise Error("initial overlap cap exhausted; no closure")
                    self.states.append([top,bottom,delta[0],delta[1],delta[2]])
        self.initial_count = len(self.states)
        var pos = 0
        while pos < len(self.states):
            var s = self.states[pos].copy()
            var top = s[0]
            var bottom = s[1]
            var x = self.next_letter[top]
            var y = self.next_letter[bottom]
            var md: List[Int] = [s[2]+s[4], s[2]+2*s[3]+s[4], s[3]+s[4]]
            var row = List[List[Int]]()
            for t in range(len(c.sigma[x])):
                var a = _prefix_count(c.sigma[x], t)
                for u in range(len(c.sigma[y])):
                    var b = _prefix_count(c.sigma[y], u)
                    var delta: List[Int] = [md[0]+a[0]-b[0], md[1]+a[1]-b[1], md[2]+a[2]-b[2]]
                    var tp = self.child_points[top][t]
                    var bp = self.child_points[bottom][u]
                    if not strict_physical_overlap(self.next_letter[tp], self.next_letter[bp], delta):
                        continue
                    var target: List[Int] = [tp,bp,delta[0],delta[1],delta[2]]
                    var idx = _find(self.states, target)
                    if idx < 0:
                        if len(self.states) >= cap:
                            raise Error("state cap exhausted; no finite closure verdict")
                        idx = len(self.states)
                        self.states.append(target^)
                    row.append([t,u,idx])
            self.edges.append(row^)
            pos += 1
        # The queue has genuinely exhausted; no depth or coordinate pruning.
        for i in range(len(self.states)):
            var s = self.states[i].copy()
            if self.next_letter[s[0]] == self.next_letter[s[1]] and s[2] == 0 and s[3] == 0 and s[4] == 0:
                self.distance.append(0)
            else:
                self.distance.append(-1)
        var changed = True
        while changed:
            changed = False
            var new_dist = self.distance.copy()
            for i in range(len(self.states)):
                for e in self.edges[i]:
                    var d = self.distance[e[2]]
                    if d >= 0 and (new_dist[i] < 0 or d + 1 < new_dist[i]):
                        new_dist[i] = d + 1
                        changed = True
            self.distance = new_dist^

    def verify_productivity(self) raises:
        if len(self.edges) != len(self.states) or len(self.distance) != len(self.states):
            raise Error("incomplete state/edge/distance table")
        var c = ReturnBoundaryCarrier()
        for i in range(len(self.states)):
            var s = self.states[i].copy()
            var x = self.next_letter[s[0]]
            var y = self.next_letter[s[1]]
            var delta: List[Int] = [s[2],s[3],s[4]]
            if not strict_physical_overlap(x, y, delta):
                raise Error("non-overlap in finite closure")
            var expected = List[List[Int]]()
            var md: List[Int] = [s[2]+s[4],s[2]+2*s[3]+s[4],s[3]+s[4]]
            for t in range(len(c.sigma[x])):
                var a = _prefix_count(c.sigma[x], t)
                for u in range(len(c.sigma[y])):
                    var b = _prefix_count(c.sigma[y], u)
                    var dd: List[Int] = [md[0]+a[0]-b[0],md[1]+a[1]-b[1],md[2]+a[2]-b[2]]
                    var tp = self.child_points[s[0]][t]
                    var bp = self.child_points[s[1]][u]
                    if strict_physical_overlap(self.next_letter[tp], self.next_letter[bp], dd):
                        var target: List[Int] = [tp,bp,dd[0],dd[1],dd[2]]
                        var idx = _find(self.states, target)
                        if idx < 0:
                            raise Error("missing actual overlapping child state")
                        expected.append([t,u,idx])
            if expected != self.edges[i]:
                raise Error("missing, duplicate or altered child occurrence")
            var goal = x == y and delta == [0,0,0]
            if (self.distance[i] == 0) != goal or self.distance[i] < 0:
                raise Error("unproductive or falsely coincident state")
            if not goal:
                var best = -1
                for e in self.edges[i]:
                    var d = self.distance[e[2]]
                    if d >= 0 and (best < 0 or d + 1 < best):
                        best = d + 1
                if best != self.distance[i]:
                    raise Error("minimum coincidence depth fails actual edge recurrence")

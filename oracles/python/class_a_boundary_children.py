"""Independent exact finite oracle for the canonical Mojo seed-star contract.

Integer polynomial coordinates and fractions.Fraction enclosures only.
This is not the universally quantified certificate or the canonical algorithm.
"""
from fractions import Fraction as F


class Geometry:
    def __init__(self, eps, k, t):
        if eps not in (-1, 1) or min(k, t) < 0:
            raise ValueError("outside boundary chambers")
        self.eps, self.k, self.t = eps, k, t
        self.n = n = k + 3 + t if eps == -1 else 2 * (k + 2) + t
        self.d = d = 2 * n + 6 * eps + 5 - k
        self.words = ((0,) + (2,) * (n+d) + (0,),
                      (1,) + (2,) * n + (0,),
                      (0,) + (2,) * (n+eps) + (1,))
        self.chi = (-2*eps, n-d+2+3*eps, -(n+3+eps))
        self.lo, self.hi = (F(n+2), F(n+3)) if eps == -1 else (F(n+4), F(n+6))
        assert self.polynomial(self.lo) < 0 < self.polynomial(self.hi)
        # Common positive scale beta*(beta-1): Ly=beta*(beta-1),
        # Lc=(beta-eps)*(beta-1), Lx=Lc+d*beta.
        self.lengths = ((eps, d-1-eps, 1), (eps, -1-eps, 1), (0, -1, 1))
        self.prefixes = []
        for word in self.words:
            counts = [0, 0, 0]
            prefixes = []
            for letter in word:
                prefixes.append(tuple(counts))
                counts[letter] += 1
            self.prefixes.append(tuple(prefixes))
        self.cache = {}
        for p, word in enumerate(self.words):
            total = (0, 0, 0)
            for letter in word:
                total = add(total, self.lengths[letter])
            assert total == self.times_beta(self.lengths[p])
            assert self.sign(self.lengths[p]) > 0

    def polynomial(self, x):
        c, b, a = self.chi
        return ((x+a)*x+b)*x+c

    def times_beta(self, p):
        c, b, a = self.chi
        return (-c*p[2], p[0]-b*p[2], p[1]-a*p[2])

    def sign(self, p):
        if p in self.cache:
            return self.cache[p]
        if p == (0, 0, 0):
            return 0
        # Fixed resource budget; failure is inconclusive, never a guessed sign.
        for _ in range(512):
            low = high = F(0)
            for coefficient in reversed(p):
                products = (low*self.lo, low*self.hi, high*self.lo, high*self.hi)
                low, high = min(products)+coefficient, max(products)+coefficient
            if low > 0 or high < 0:
                answer = 1 if low > 0 else -1
                self.cache[p] = answer
                return answer
            midpoint = (self.lo+self.hi)/2
            value = self.polynomial(midpoint)
            if value == 0:
                raise AssertionError("unexpected rational Perron root")
            if value < 0:
                self.lo = midpoint
            else:
                self.hi = midpoint
        raise RuntimeError("exact sign budget exhausted")

    def shift(self, label):
        return tuple(sum(w*l[q] for w, l in zip(label[2:], self.lengths)) for q in range(3))

    def interior(self, label):
        top, bottom = label[:2]
        shift = self.shift(label)
        return self.sign(add(shift, self.lengths[bottom])) > 0 and self.sign(
            sub(shift, self.lengths[top])) < 0

    def child(self, label, i, j):
        top, bottom, x, c, y = label
        if not (0 <= i < len(self.words[top]) and 0 <= j < len(self.words[bottom])):
            raise ValueError("nonexistent occurrence")
        a, b = self.prefixes[top][i], self.prefixes[bottom][j]
        w = (2*x+c+y, c+y, (self.n+self.d)*x+self.n*c+(self.n+self.eps)*y)
        target = (self.words[top][i], self.words[bottom][j],
                  *(w[q]+b[q]-a[q] for q in range(3)))
        # Independent geometric affine recurrence, with all literal prefixes.
        geometric = add(self.times_beta(self.shift(label)), sub(
            self.shift((0, 0, *b)), self.shift((0, 0, *a))))
        assert geometric == self.shift(target)
        return target

    def edges(self, label):
        for i in range(len(self.words[label[0]])):
            for j in range(len(self.words[label[1]])):
                target = self.child(label, i, j)
                if self.interior(target):
                    yield (i, j, target)


def add(p, q):
    return tuple(a+b for a, b in zip(p, q))


def sub(p, q):
    return tuple(a-b for a, b in zip(p, q))


def expected_star(eps, k, n):
    r = 2 if eps == 1 and k <= 3 else 1
    out = {(0, 0, (0, 1, 0, 0, 0))}
    out.update((0, j, (0, 2, 0, 1, j-1)) for j in range(1, r+2))
    out.update((i, i+m, (2, 2, -1, 1, m))
               for m in (r, r+1) for i in range(1, n-m+1))
    out.update((i, n+1, (2, 0, -1, 1, n-i+1))
               for i in range(n-r, n+(3 if eps == -1 else 2)))
    return out


def probe():
    rows = []
    for eps in (-1, 1):
        for k in range(7):
            for t in range(4):
                g = Geometry(eps, k, t)
                actual = set(g.edges((0, 1, 0, 0, 0)))
                assert actual == expected_star(eps, k, g.n)
                r = 2 if eps == 1 and k <= 3 else 1
                assert len(actual) == 2*g.n+(4 if eps == -1 else 3)
                labels = {edge[2] for edge in actual}
                assert len(labels) == 2*r+(7 if eps == -1 else 6)
                row = dict(eps=eps, k=k, t=t, n=g.n, d=g.d,
                           pairs=len(g.words[0])*len(g.words[1]),
                           occurrences=len(actual), labels=len(labels))
                if t == 0 and (k == 0 or (eps == 1 and k == 4)):
                    successors = [(label, i, j, target) for label in sorted(labels)
                                  if label[:2] == (2, 2) for i, j, target in g.edges(label)]
                    assert successors and all(target not in labels for _, _, _, target in successors)
                    assert all(target[3] == label[4]+1 for label, _, _, target in successors)
                    row["T_m_successor_occurrences"] = len(successors)
                    row["first_escape"] = successors[0]
                rows.append(row)
    return dict(scope="finite independent replay; not closed carrier or BH",
                members=len(rows), pairs=sum(row["pairs"] for row in rows), rows=rows)


if __name__ == "__main__":
    import json
    print(json.dumps(probe(), indent=2, sort_keys=True))

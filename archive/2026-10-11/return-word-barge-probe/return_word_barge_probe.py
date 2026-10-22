"""Return-word derivation against Barge's class on Theorem K's family (exploratory).

Family: sigma(o) = y, sigma(y) = o w1 o, sigma(z) = o w2 o, w1, w2 over {y, z}.
Budget: |w1|, |w2| <= 4; derivation power k <= 9 (sigma^k(c) must begin with c);
fixed-point prefix of 3,000 letters; derived powers n = 1, 2.
Screens: primitivity exact (integer matrix power); |det M| = 2 exact (integer
determinant); Pisot by numpy eigenvalue moduli (FLOAT, tolerance 1e-9).
A return word missing from the prefix raises (budget exhausted), never a verdict.
Provenance only, not a certificate (AGENTS.md); run: python3 return_word_barge_probe.py
"""
import itertools
import numpy as np

LETTERS, MAX_WORD, MAX_K, PREFIX, POWERS = "oyz", 4, 9, 3000, (1, 2)


def apply(s, w):
    return "".join(s[x] for x in w)


def power(s, k):
    t = {a: a for a in s}
    for _ in range(k):
        t = {a: apply(s, t[a]) for a in s}
    return t


def matrix(s, alphabet):
    return np.array([[s[b].count(a) for b in alphabet] for a in alphabet], dtype=np.int64)


def det3(m):
    return int(m[0, 0] * (m[1, 1] * m[2, 2] - m[1, 2] * m[2, 1]) - m[0, 1] * (m[1, 0] * m[2, 2] - m[1, 2] * m[2, 0])
               + m[0, 2] * (m[1, 0] * m[2, 1] - m[1, 1] * m[2, 0]))


def primitive(s):
    m = (matrix(s, LETTERS) > 0).astype(np.int64)
    return bool((np.linalg.matrix_power(m, 9) > 0).all())


def pisot_float(s):
    ev = sorted(np.abs(np.linalg.eigvals(matrix(s, sorted(s)).astype(float))), reverse=True)
    return ev[0] > 1 and all(e < 1 - 1e-9 for e in ev[1:])


def barge(s):
    f, g = [s[a][0] for a in s], [s[a][-1] for a in s]
    inj, const = (lambda v: len(set(v)) == len(s)), (lambda v: len(set(v)) == 1)
    return ("B" if inj(f) and const(g) else "") + ("M" if const(f) and inj(g) else "")


def derive(s, c):
    """Durand's derived substitution on return words to c, or None if no sigma^k(c) begins with c."""
    k = next((k for k in range(1, MAX_K + 1) if power(s, k)[c][0] == c), None)
    if k is None:
        return None
    t, u = power(s, k), c
    while len(u) < PREFIX:
        u = apply(t, u)
    idx = [i for i, x in enumerate(u) if x == c]
    words = list(dict.fromkeys(u[i:j] for i, j in zip(idx, idx[1:])))
    label = {r: chr(ord("a") + i) for i, r in enumerate(words)}

    def code(w):
        cut = [i for i, x in enumerate(w) if x == c] + [len(w)]
        pieces = [w[i:j] for i, j in zip(cut, cut[1:])]
        missing = [p for p in pieces if p not in label]
        if missing:
            raise RuntimeError(f"budget exhausted: return word {missing[0]!r} not in the {PREFIX}-letter prefix")
        return "".join(label[p] for p in pieces)

    return k, {label[r]: code(apply(t, r)) for r in words}


def main():
    words = ["".join(p) for n in range(MAX_WORD + 1) for p in itertools.product("yz", repeat=n)]
    members = hits = 0
    for w1, w2 in itertools.product(words, repeat=2):
        s = {"o": "y", "y": "o" + w1 + "o", "z": "o" + w2 + "o"}
        if not primitive(s) or abs(det3(matrix(s, LETTERS))) != 2 or not pisot_float(s):
            continue
        members += 1
        verdicts, witnessed = [], False
        for c in LETTERS:
            d = derive(s, c)
            if d is None:
                verdicts.append(f"{c}:not-derivable(k<={MAX_K})")
                continue
            k, ds = d
            found = [n for n in POWERS if barge(power(ds, n))]
            verdicts.append(f"{c}:k={k},returns={len(ds)},barge_powers={found or '-'}")
            witnessed |= bool(found)
        hits += witnessed
        print(f"w1={w1 or 'ε'} w2={w2 or 'ε'}  " + "  ".join(verdicts))
    print(f"members {members}  members with a derived Barge or mirror witness {hits}")


if __name__ == "__main__":
    main()

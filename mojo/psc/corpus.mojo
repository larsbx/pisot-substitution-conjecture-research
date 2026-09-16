"""The alphabet-3 short-image PIP corpus as a first-class census object.

Every census and catalogue driver in this repository surveys the same finite
corpus: the primitive irreducible Pisot substitutions on `{0,1,2}` whose three
images have length 1, 2 or 3. `image_words` enumerates the 39 candidate images
in the deterministic order every driver has always used (by length, then
lexicographically), `pip_corpus` screens the `39^3 = 59319` triples once with
the exact decision procedure of `psc.pisot`, and a `Specimen` carries the
indices, the images and the incidence matrix so that no driver recomputes
them. A specimen's `label` (`i j k`) and `json_fields` are the replayable
identity printed by every diagnostic line.

The corpus is finite evidence only: its 4554 members prove nothing about the
general PIP regime.
"""

from finite_linear_algebra.mat3 import Mat3
from psc.bpa import substitution_incidence
from psc.pisot import is_pip
from psc.words import ALPHABET

comptime MAX_IMAGE_LENGTH = 3
comptime PROGRESS_STRIDE = 500

# Fail-closed state cap shared by every balanced-pair and overlap-graph census.
comptime STATE_CAP = 20000

# Arithmetic regime of the incidence cubic, as printed by the C4 census.
comptime REGIME_NONUNIMODULAR = 0
comptime REGIME_UNIMODULAR_REAL = 1
comptime REGIME_UNIMODULAR_COMPLEX = 2
comptime REGIME_ZERO_DISCRIMINANT = 3


struct Specimen(Copyable, Movable):
    """One corpus member: image indices into `image_words`, images, incidence."""

    var index: Int
    var i: Int
    var j: Int
    var k: Int
    var sigma: List[List[Int]]
    var incidence: Mat3

    def __init__(
        out self,
        index: Int,
        i: Int,
        j: Int,
        k: Int,
        var sigma: List[List[Int]],
        var incidence: Mat3,
    ):
        self.index = index
        self.i = i
        self.j = j
        self.k = k
        self.sigma = sigma^
        self.incidence = incidence^

    def label(self) -> String:
        """`i j k`: the image indices, as every diagnostic line prints them."""
        return String(self.i) + " " + String(self.j) + " " + String(self.k)

    def json_fields(self) -> String:
        """`"i":i,"j":j,"k":k`, the specimen identity inside a JSON record."""
        return (
            "\"i\":" + String(self.i)
            + ",\"j\":" + String(self.j)
            + ",\"k\":" + String(self.k)
        )


def words_of_length(n: Int) -> List[List[Int]]:
    """Every word of length `n` over `{0,1,2}`, lexicographically."""
    var out: List[List[Int]] = [List[Int]()]
    for _ in range(n):
        var longer = List[List[Int]]()
        for w in range(len(out)):
            for a in range(ALPHABET):
                var ext = out[w].copy()
                ext.append(a)
                longer.append(ext^)
        out = longer^
    return out^


def image_words() -> List[List[Int]]:
    """The 39 candidate images: every word of length 1, 2 or 3 over `{0,1,2}`."""
    var out = List[List[Int]]()
    for n in range(1, MAX_IMAGE_LENGTH + 1):
        var words = words_of_length(n)
        for w in range(len(words)):
            out.append(words[w].copy())
    return out^


def substitution_of(words: List[List[Int]], i: Int, j: Int, k: Int) -> List[List[Int]]:
    """`0 -> words[i]`, `1 -> words[j]`, `2 -> words[k]`."""
    var sigma = List[List[Int]]()
    sigma.append(words[i].copy())
    sigma.append(words[j].copy())
    sigma.append(words[k].copy())
    return sigma^


def pip_corpus() -> List[Specimen]:
    """The 4554 PIP specimens with images of length at most 3, screened exactly
    and returned in the canonical `(i, j, k)` order."""
    var words = image_words()
    var out = List[Specimen]()
    for i in range(len(words)):
        for j in range(len(words)):
            for k in range(len(words)):
                var sigma = substitution_of(words, i, j, k)
                var m = Mat3(substitution_incidence(sigma))
                if is_pip(m):
                    out.append(Specimen(len(out), i, j, k, sigma^, m^))
    return out^


def report_progress(done: Int, stride: Int = PROGRESS_STRIDE):
    """One `progress:` line every `stride` specimens, for long censuses."""
    if done % stride == 0:
        print("progress:", done)


def cubic_discriminant(poly: List[Int]) -> Int:
    """Discriminant of the monic cubic `c0 + c1 x + c2 x^2 + x^3`."""
    var c = poly[0]
    var b = poly[1]
    var a = poly[2]
    return (
        a * a * b * b
        - 4 * b * b * b
        - 4 * a * a * a * c
        - 27 * c * c
        + 18 * a * b * c
    )


def arithmetic_regime(m: Mat3) -> Int:
    """`|det M| > 1`, or unimodular with three real roots, a complex pair, or a
    repeated root (a zero discriminant, impossible for an irreducible cubic and
    reported so that the census fails loudly rather than misclassifying)."""
    if abs(m.det()) != 1:
        return REGIME_NONUNIMODULAR
    var disc = cubic_discriminant(m.charpoly())
    if disc < 0:
        return REGIME_UNIMODULAR_COMPLEX
    if disc > 0:
        return REGIME_UNIMODULAR_REAL
    return REGIME_ZERO_DISCRIMINANT

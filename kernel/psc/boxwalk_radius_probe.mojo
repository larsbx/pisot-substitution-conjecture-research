"""Exact finite-depth aligned-prefix radius probe for a historical box-walk candidate.

This measures ONE fully specified quantity: max ||Parikh(u[:q])-Parikh(v[:q])||_infty
at common aligned cuts q in sigma^depth(01) versus sigma^depth(10), for
sigma = (001,22,220). It does NOT assert box-walk transition closure,
saturation, exhaustive search over substitutions, or the original unrecorded
constrained-enumeration statistic.

The result is a finite negative control for a claimed universal radius 8.
This is deterministic; the observation budget is explicit and exceeded
budgets raise an error, never silently certify saturation.
"""


struct RadiusObservation(Copyable, Movable):
    var depth: Int
    var word_length: Int
    var radius: Int
    var first_cut: Int
    var d0: Int
    var d1: Int
    var d2: Int

    def __init__(out self, depth: Int, length: Int):
        self.depth = depth
        self.word_length = length
        self.radius = 0
        self.first_cut = 0
        self.d0 = 0
        self.d1 = 0
        self.d2 = 0


def inflate_historical(word: List[Int]) raises -> List[Int]:
    """Images of 0 -> 001, 1 -> 22, 2 -> 220."""
    var out = List[Int]()
    for a in word:
        if a == 0:
            out.append(0)
            out.append(0)
            out.append(1)
        elif a == 1:
            out.append(2)
            out.append(2)
        elif a == 2:
            out.append(2)
            out.append(2)
            out.append(0)
        else:
            raise Error("probe word contains letter outside 0..2")
    return out^


def aligned_prefix_radius(top: List[Int], bottom: List[Int], depth: Int) raises -> RadiusObservation:
    """Exhaust every aligned cut in this ONE finite inflated swap pair."""
    if len(top) != len(bottom):
        raise Error("probe needs equal word lengths")
    var obs = RadiusObservation(depth, len(top))
    var d0 = 0
    var d1 = 0
    var d2 = 0
    for i in range(len(top)):
        var a = top[i]
        var b = bottom[i]
        if a == 0:
            d0 += 1
        elif a == 1:
            d1 += 1
        elif a == 2:
            d2 += 1
        else:
            raise Error("top word contains invalid letter")
        if b == 0:
            d0 -= 1
        elif b == 1:
            d1 -= 1
        elif b == 2:
            d2 -= 1
        else:
            raise Error("bottom word contains invalid letter")
        var r = max(abs(d0), max(abs(d1), abs(d2)))
        if r > obs.radius:
            obs.radius = r
            obs.first_cut = i + 1
            obs.d0 = d0
            obs.d1 = d1
            obs.d2 = d2
    if d0 != 0 or d1 != 0 or d2 != 0:
        raise Error("inflated swap pair failed the balanced-endpoint check")
    return obs^


def historical_swap_probe(max_depth: Int, max_word_length: Int) raises -> List[RadiusObservation]:
    """Complete each visited depth, but NEVER infer future-depth saturation.

    max_depth is inclusive. max_word_length is a hard per-side budget.
    A budget refusal raises rather than returning a mathematical verdict.
    """
    if max_depth < 0 or max_word_length < 2:
        raise Error("invalid depth or per-side word-length budget")
    var top: List[Int] = [0, 1]
    var bottom: List[Int] = [1, 0]
    var rows = List[RadiusObservation]()
    for depth in range(max_depth + 1):
        if len(top) > max_word_length or len(bottom) > max_word_length:
            raise Error("BUDGET_EXHAUSTED: word length exceeded")
        rows.append(aligned_prefix_radius(top, bottom, depth))
        if depth < max_depth:
            top = inflate_historical(top)
            bottom = inflate_historical(bottom)
    return rows^

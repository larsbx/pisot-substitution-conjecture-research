"""Exact word identities for the determinant-three BPA carrier.

Run lengths are affine in n = k - 9. The auxiliary letter IMAGE_ONE
stands for the entire word 0 1^k 2. No operation expands a symbolic run.
"""

from finite_exact.checked_int import checked_add, checked_sub

comptime IMAGE_ONE = 3
comptime FIRST_SYMBOLIC_K = 9


@fieldwise_init
struct Length(ImplicitlyCopyable, Equatable):
    var slope: Int
    var base: Int

    def __eq__(self, rhs: Length) -> Bool:
        return self.slope == rhs.slope and self.base == rhs.base

    def nonnegative(self) -> Bool:
        return self.slope >= 0 and self.base >= 0

    def positive(self) -> Bool:
        return self.slope >= 0 and self.base > 0

    def plus(self, rhs: Length) raises -> Length:
        return Length(checked_add(self.slope, rhs.slope), checked_add(self.base, rhs.base))

    def minus(self, rhs: Length) raises -> Length:
        return Length(checked_sub(self.slope, rhs.slope), checked_sub(self.base, rhs.base))


@fieldwise_init
struct Run(ImplicitlyCopyable, Equatable):
    var letter: Int
    var size: Length

    def __eq__(self, rhs: Run) -> Bool:
        return self.letter == rhs.letter and self.size == rhs.size


def append_run(mut word: List[Run], run: Run) raises:
    if not run.size.nonnegative():
        raise Error("symbolic length must be nonnegative")
    if run.size == Length(0, 0):
        return
    if len(word) > 0 and word[len(word) - 1].letter == run.letter:
        word[len(word) - 1].size = word[len(word) - 1].size.plus(run.size)
    else:
        word.append(run)


def template(text: String) raises -> List[Run]:
    var word = List[Run]()
    for ch in text.as_bytes():
        if ch == 73 or ch == 72:  # I = 1^k, H = 1^(k-3).
            append_run(word, Run(1, Length(1, FIRST_SYMBOLIC_K if ch == 73 else FIRST_SYMBOLIC_K - 3)))
        elif ch >= 48 and ch <= 50:
            append_run(word, Run(Int(ch) - 48, Length(0, 1)))
        else:
            raise Error("unknown carrier template letter")
    return word^


def fold_images(word: List[Run]) raises -> List[Run]:
    """Coalesce runs and contract each recorded literal 0 1^k 2 to IMAGE_ONE."""
    var out = List[Run]()
    var pending = List[Run]()
    for run in word:
        append_run(pending, run)
    for run in pending:
        if run.letter == 2 and len(out) >= 2 \
                and out[len(out) - 1] == Run(1, Length(1, FIRST_SYMBOLIC_K)) and out[len(out) - 2].letter == 0:
            if not run.size.positive() or not out[len(out) - 2].size.positive():
                raise Error("image contraction needs both endpoint letters")
            _ = out.pop()
            var zeroes = out.pop().size.minus(Length(0, 1))
            append_run(out, Run(0, zeroes))
            append_run(out, Run(IMAGE_ONE, Length(0, 1)))
            append_run(out, Run(2, run.size.minus(Length(0, 1))))
        else:
            append_run(out, run)
    return out^


def inflate(word: List[Run]) raises -> List[Run]:
    var out = List[Run]()
    for run in word:
        if run.letter == 0:
            append_run(out, Run(1, run.size))
        elif run.letter == 1:
            append_run(out, Run(IMAGE_ONE, run.size))
        else:
            if run.letter != 2 or run.size.slope != 0:
                raise Error("unexpected variable run of the third letter")
            for _ in range(run.size.base):
                append_run(out, Run(0, Length(0, 3)))
                append_run(out, Run(1, Length(0, 1)))
    return fold_images(out)


def append_power(mut out: List[Run], word: List[Run], count: Length) raises:
    """For symbolic powers verify YX=IMAGE_ONE and use (XY)^m=X(YX)^(m-1)Y."""
    if not count.positive():
        raise Error("every listed repeat must occur")
    if count.slope == 0:
        for _ in range(count.base):
            for run in word:
                append_run(out, run)
        return
    var cut = -1
    for i in range(len(word)):
        if word[i].letter == 0:
            if cut >= 0 or word[i].size != Length(0, 1):
                raise Error("repeated block must have one zero")
            cut = i
    if cut < 0:
        raise Error("repeated block has no zero")
    var rotation = List[Run]()
    for i in range(len(word)):
        append_run(rotation, word[(cut + i) % len(word)])
    if fold_images(rotation) != [Run(IMAGE_ONE, Length(0, 1))]:
        raise Error("repeat rotation differs from IMAGE_ONE")
    for i in range(cut):
        append_run(out, word[i])
    append_run(out, Run(IMAGE_ONE, count.minus(Length(0, 1))))
    for i in range(cut, len(word)):
        append_run(out, word[i])


def uniformly_nonzero(delta: List[Length]) -> Bool:
    for d in delta:
        if d.positive() or (d.slope <= 0 and d.base < 0):
            return True
    return False


def check_irreducible(upper: List[Run], lower: List[Run]) raises:
    """Check all proper prefixes and the final zero by aligned affine runs."""
    if len(upper) == 0 or len(lower) == 0:
        raise Error("empty carrier word")
    var i = 0
    var j = 0
    var left = upper[0].size
    var right = lower[0].size
    var delta: List[Length] = [Length(0, 0), Length(0, 0), Length(0, 0)]
    while i < len(upper) and j < len(lower):
        var top = upper[i].letter
        var bottom = lower[j].letter
        var span = left if right.minus(left).nonnegative() else right
        left = left.minus(span)
        right = right.minus(span)
        if not span.positive() or not left.nonnegative() or not right.nonnegative():
            raise Error("no single positive run alignment valid on k >= 9")
        if left == Length(0, 0):
            i += 1
            if i < len(upper):
                left = upper[i].size
        if right == Length(0, 0):
            j += 1
            if j < len(lower):
                right = lower[j].size
        var last = i == len(upper) and j == len(lower)
        if top == bottom:
            if last or not uniformly_nonzero(delta):
                raise Error("equal-letter span contains a premature cut or lacks a final cut")
        else:
            if span.slope != 0:
                raise Error("unequal-letter span must have constant length")
            for offset in range(span.base):
                delta[top] = delta[top].plus(Length(0, 1))
                delta[bottom] = delta[bottom].minus(Length(0, 1))
                if last and offset + 1 == span.base:
                    if delta != [Length(0, 0), Length(0, 0), Length(0, 0)]:
                        raise Error("missing final cut")
                elif not uniformly_nonzero(delta):
                    raise Error("no fixed sign proves this prefix is unequal")
    if i != len(upper) or j != len(lower):
        raise Error("carrier track lengths differ")

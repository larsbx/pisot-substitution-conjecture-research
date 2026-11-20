"""Native symbolic certificate for the high-determinant forward carrier."""

from std.testing import assert_true, assert_false, assert_equal
from finite_exact.checked_int import checked_add
from mojo_smoke.claims import require_contract
from psc.c4_polynomial_word import Word, letter
from psc.poly_line import Poly, poly_const, poly_from_aff

# Every token in a track is one letter or atom, optionally with a power.
# Every row token is an oriented child, possibly with preceding diagonals
# and a repeat. Parentheses group repeated sequences of such tokens.
comptime CERTIFICATE = """
0 1 | 1 0 | 0' G:2
1 | 1 | -
1 2 | 2 1 | 3 4'
0 | 0 | -
0^r-1 1 A | B C | 5' F:6 E:7*k-2 E:8
0 1^r-1 | 1^r-1 0 | 0' G:9*r-2 G:2
1^r-1 2 1 0 | 2 0 1^r | 3 10' G:2'
1^r 2 0 | 2 0 1^r | 3 11'
1^r 2 A C | 2 C 1^r A | 3 12' F:6' E:7'*k-2 E:8'
1 2 0 | 2 0 1 | 3 13'
0^r-1 1 1 A^r-1 0 | B A^r-2 C 0 1 | 5' F:14 F:6 ( E:7*k-3 E:15 )*r-2 E:7*k-3 E:16
0^r-1 1 1 A^r | B A^r-1 C 1 | 5' F:14 F:6 ( E:7*k-3 E:15 )*r-1 E:7*k-3 E:17
0^r-1 1^r+1 A^r 0 | B A^r-1 C 1 0 1^r-1 | 5' F:14*r F:6 ( E:7*k-r-2 E:18 )*r-1 E:7*k-r-2 E:19
0^r-1 1 1 A | B C 1 | 5' F:14 F:6 E:7*k-3 E:17
1^r-1 2 0 | 2 0 1^r-1 | 3 20'
1^r 2 A^2 C 1 0 | 2 C 1 A^2 0 1^r | 3 21' E:7'*k-r+2 22' E:7'*k-r+2 23' G:9' G:2'
1^r 2 A^2 C 1 | 2 C 1^r A 1 A | 3 12' F:6' E:7'*k-2 E:24' F:6' E:7'*k-3 E:17'
1^r 2 A^2 C | 2 C 1^r A^2 | 3 12' F:6' E:7'*k-2 E:25' E:7'*k-2 E:8'
1^r 2 A^r+1 C 1 0 | 2 C 1 A^r+1 0 1^r | 3 21' ( E:7'*k-r+2 22' )*r E:7'*k-r+2 23' G:9' G:2'
1^r 2 A^r+1 C 1 | 2 C 1^r A^2 1 A^r-1 | 3 12' F:6' E:7'*k-2 E:25' E:7'*k-2 E:24' F:6' ( E:7'*k-3 E:15' )*r-2 E:7'*k-3 E:17'
0^r-1 1 1 A^r-1 | B A^r-2 C 1 | 5' F:14 F:6 ( E:7*k-3 E:15 )*r-2 E:7*k-3 E:17
0^r-1 1^r+1 A^2 1 A^r-2 0 | B A^r-1 C 1 0 1^r | 5' F:14*r F:6 E:7*k-r-2 E:18 E:7*k-r-2 E:26 F:6 ( E:7*k-r-3 E:27 )*r-3 E:7*k-r-3 E:28
0^r-1 1 1 A^r-2 0 | 1^k-r 2 A^r-3 C 1 0 1^r | 5' F:14 F:6 ( E:7*k-r-3 E:27 )*r-3 E:7*k-r-3 E:28
0^r-1 1 1 A^r-2 0 | 1^k-r 2 A^r-3 C 1^r 0 1 | 5' F:14 F:6 ( E:7*k-r-3 E:27 )*r-3 E:7*k-r-3 E:29
1^r 2 A C 0 | 2 C 1 A 0 1^r-1 | 3 21' E:7'*k-r+2 23' G:2'
1^r 2 A C 1 0 | 2 C 1 A 0 1^r | 3 21' E:7'*k-r+2 23' G:9' G:2'
1^r 2 A^r+1 C 0 | 2 C 1 A^r+1 0 1^r-1 | 3 21' ( E:7'*k-r+2 22' )*r E:7'*k-r+2 23' G:2'
1^r 2 A^r+2 C 1 0 | 2 C 1 A^r+2 0 1^r | 3 21' ( E:7'*k-r+2 22' )*r+1 E:7'*k-r+2 23' G:9' G:2'
1^r 2 A^r+2 C 1 | 2 C 1^r A^2 1 A^r | 3 12' F:6' E:7'*k-2 E:25' E:7'*k-2 E:24' F:6' ( E:7'*k-3 E:15' )*r-1 E:7'*k-3 E:17'
1^r 2 A^r+2 C 1 | 2 C 1^r A^r+1 1 A | 3 12' F:6' ( E:7'*k-2 E:25' )*r E:7'*k-2 E:24' F:6' E:7'*k-3 E:17'
"""


def power(token: String) raises -> Poly:
    # r = 4 + u, k = 7 + u + v on the whole domain u,v >= 0.
    var prefix: Int
    var slope_u = 0
    var slope_v = 0
    var base: Int
    if token.startswith("k-r"):
        prefix = 3
        slope_v = 1
        base = 3
    elif token.startswith("k"):
        prefix = 1
        slope_u = 1
        slope_v = 1
        base = 7
    elif token.startswith("r"):
        prefix = 1
        slope_u = 1
        base = 4
    else:
        return poly_const(Int(token))
    if token.byte_length() > prefix:
        var suffix = String(token[byte=prefix:])
        if suffix.startswith("+"):
            suffix = String(token[byte=prefix+1:])
        base = checked_add(base, Int(suffix))
    return poly_from_aff([base, slope_u, slope_v])


def track(source: String, letters: Dict[String, Word]) raises -> Word:
    var out = Word()
    for token in source.split(" "):
        var fields = String(token).split("^")
        assert_true(len(fields) <= 2)
        var name = String(fields[0])
        var count = power(String(fields[1])) if len(fields) == 2 else poly_const(1)
        out = out.then(letters[name].repeated(count))
    return out^


def add_atoms(mut letters: Dict[String, Word]) raises:
    letters["A"] = track("0 1^k 2", letters)
    letters["B"] = track("1^k 2", letters)
    letters["C"] = track("0^r 1", letters)


def child_track(source: String, orientation: Int, tracks: List[List[Word]],
                diagonals: Dict[String, Word]) raises -> Word:
    var stack: List[Word] = [Word()]
    for token in source.split(" "):
        var text = String(token)
        if text == "(":
            stack.append(Word())
        elif text.startswith(")*"):
            assert_true(len(stack) > 1)
            var block = stack.pop().repeated(power(String(text[byte=2:])))
            var at = len(stack) - 1
            stack[at] = stack[at].then(block)
        else:
            var segments = text.split(":")
            assert_true(len(segments) <= 2)
            var ref_text = String(segments[len(segments) - 1])
            var fields = ref_text.split("*")
            assert_true(len(fields) <= 2)
            var name = String(fields[0])
            var reversed = name.endswith("'")
            var end = name.byte_length() - Int(reversed)
            var index = Int(String(name[byte=0:end]))
            assert_true(0 <= index < len(tracks))
            var child = tracks[index][orientation ^ Int(reversed)].copy()
            if len(segments) == 2:
                var prefix = diagonals[String(segments[0])].then(child)
                child = prefix^
            var count = power(String(fields[1])) if len(fields) == 2 else poly_const(1)
            var at = len(stack) - 1
            stack[at] = stack[at].then(child.repeated(count))
    assert_equal(len(stack), 1)
    return stack.pop()


def main() raises:
    var letters = Dict[String, Word]()
    for a in range(3):
        letters[String(a)] = letter(a)
    add_atoms(letters)
    var inflated = Dict[String, Word]()
    inflated["0"] = letters["1"].copy()
    inflated["1"] = letters["A"].copy()
    inflated["2"] = letters["C"].copy()
    add_atoms(inflated)
    var diagonals = Dict[String, Word]()
    diagonals["E"] = track("1^k-r", letters)
    diagonals["F"] = track("1^k-r+1", letters)
    diagonals["G"] = track("1^k-1", letters)
    var tracks = List[List[Word]]()
    var templates = List[List[String]]()
    var rows = List[String]()
    var bound = track("A^r+2 1^r+2 1^r+2", letters).length.copy()
    for line in CERTIFICATE.split("\n"):
        if line.byte_length() == 0:
            continue
        var fields = String(line).split(" | ")
        assert_equal(len(fields), 3)
        var upper = String(fields[0])
        var lower = String(fields[1])
        var top = track(upper, letters)
        var bottom = track(lower, letters)
        assert_true(top.nonempty_everywhere() and bottom.nonempty_everywhere())
        assert_true(top.balanced_with(bottom))
        for term in top.length.terms.items():
            assert_true(term.value <= bound.terms.get(term.key, 0))
        tracks.append([top^, bottom^])
        templates.append([upper^, lower^])
        rows.append(String(fields[2]))
    assert_equal(len(tracks), 30)
    assert_true(tracks[0][0].equals(track("0 1", letters)))
    assert_true(tracks[0][1].equals(track("1 0", letters)))
    for i in range(len(tracks)):
        if rows[i] == "-":
            assert_true(i == 1 or i == 3)
            var singleton = letter(1 if i == 1 else 0)
            assert_true(tracks[i][0].equals(singleton))
            assert_true(tracks[i][1].equals(singleton))
        else:
            for side in range(2):
                var image = track(templates[i][side], inflated)
                var children = child_track(rows[i], side, tracks, diagonals)
                assert_true(children.equals(image), "literal word identity fails at row " + String(i))

    # Same Parikh vectors are insufficient to validate a literal row.
    assert_false(child_track("0 G:2", 0, tracks, diagonals).equals(track("0 1", inflated)))
    assert_false(child_track("G:2 0'", 0, tracks, diagonals).equals(track("0 1", inflated)))
    assert_false(child_track("0' E:2", 0, tracks, diagonals).equals(track("0 1", inflated)))
    var negative_repeat_rejected = False
    try:
        _ = track("1^k-r-4", letters)
    except:
        negative_repeat_rejected = True
    assert_true(negative_repeat_rejected)
    # 00 and 0 both have zero letter polynomial. Length remains essential.
    assert_false(track("0 0", letters).equals(track("0", letters)))
    require_contract("The two-parameter seed has a bounded balanced refinement for r >= 4 and k >= r+3")

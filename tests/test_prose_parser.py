import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from prose_parser import HOLE, STAR, Opt, Quote, Rep, Seq, match, parse, phrase, words  # noqa: E402


def shape(text: str) -> list[list[str]]:
    """Blocks as lists of clause texts (quotes rendered as «…»)."""

    def render(item) -> str:
        if isinstance(item, Quote):
            return "«" + " ".join(render(i) for i in item.items) + "»"
        return item.text

    return [[" ".join(render(i) for i in c.items) for c in block] for block in parse(text)]


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        ("A b; c d. E f", [["A b", "c d", "E f"]]),
        ("A, we b, and the c, or d", [["A", "we b", "and the c , or d"]]),
        ("Never describe x, y, or PSC as proved.", [["Never describe x , y , or PSC as proved"]]),
        ("a: b. 2.5 c", [["a", "b", "2.5 c"]]),
        ('The "x; y. z" is false.', [["The «x ; y . z» is false"]]),
        ("“a. b” c", [["«a . b» c"]]),
        ('An "unclosed quote; here', [['An " unclosed quote', "here"]]),
        ("a\n\nb", [["a"], ["b"]]),
        ("- a\n- b", [["- a"], ["- b"]]),
        ("| x | y |", [["x", "y"]]),
        (r"P_C\,N_C = M_\sigma\,P_C", [[r"P_C N_C = M_ \sigma P_C"]]),
        ("**bold** `code; x` $m$", [["bold `code; x` m"]]),
    ],
)
def test_parse_shape(text: str, expected: list[list[str]]) -> None:
    assert shape(text) == expected


def test_parse_tracks_sentences() -> None:
    (block,) = parse("a; b. c")
    assert [c.sentence for c in block] == [0, 0, 1]


def test_parse_is_total_on_arbitrary_markup() -> None:
    for text in ["", "\n\n\n", "”“\"''``", ";;;", "...", "\\", "`"]:
        parse(text)


def items(text: str):
    """Tokens of a one-clause text with the token ``C`` replaced by HOLE."""
    ((clause,),) = parse(text)
    return tuple(HOLE if getattr(i, "text", "") == "C" else i for i in clause.items)


@pytest.mark.parametrize(
    ("production", "text", "expected"),
    [
        (Seq((STAR, HOLE, STAR)), "a C b", True),
        (Seq((STAR, HOLE, STAR)), "a b", False),
        (Seq((words("a"), Opt(words("x")), HOLE)), "a C", True),
        (Seq((words("a"), Opt(words("x")), HOLE)), "a x C", True),
        (Seq((words("a"), Rep(words("x"), 0, 2), HOLE)), "a x x C", True),
        (Seq((words("a"), Rep(words("x"), 0, 2), HOLE)), "a x x x C", False),
        (Seq((phrase("no longer"), HOLE)), "No longer C", True),
        (Seq((phrase("no longer"), HOLE)), "no C", False),
    ],
)
def test_match_is_exact(production, text: str, expected: bool) -> None:
    assert match(production, items(text)) is expected


def test_parse_nests_straight_quotes_inside_curly_quotes() -> None:
    assert shape('“a "b; c" d.” e') == [['«a «b ; c» d .» e']]

"""Every relative link in a tracked Markdown file resolves, so a directory move cannot strand a reference.

archive/ is excluded: its records are verbatim and may name paths of the layout they were written in.
Fenced blocks and inline code spans are excluded: they are not rendered as links, and commands such as
``o['f'](pathlib.Path('x'))`` would otherwise read as one.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\]\(([^)#\s]+)(?:#[^)]*)?\)")
EXTERNAL = re.compile(r"[A-Za-z][A-Za-z0-9+.-]*:|<")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
INLINE_CODE = re.compile(r"(?<!`)(`+)(?!`)(.*?)(?<!`)\1(?!`)")


def markdown() -> list[Path]:
    out = subprocess.run(["git", "ls-files", "*.md"], cwd=ROOT, capture_output=True, text=True, check=True).stdout
    return [ROOT / rel for rel in out.split() if not rel.startswith("archive/")]


def links(text: str) -> list[tuple[int, str]]:
    """(line number, target) of links outside fences and same-line code spans."""
    found, fence = [], None
    for number, line in enumerate(text.splitlines(), 1):
        opener = FENCE.match(line)
        if fence is None and opener:
            fence = opener.group(1)
        elif fence is not None:
            if opener and opener.group(1)[0] == fence[0] and len(opener.group(1)) >= len(fence) \
                    and not line.strip()[len(opener.group(1)):].strip():
                fence = None
        else:
            found += [(number, target) for target in LINK.findall(INLINE_CODE.sub("", line))]
    return found


def test_links_skip_fenced_and_inline_code():
    text = "\n".join([
        "[a](a.md)",
        "```sh",
        "python -c \"o['f'](pathlib.Path('x'))\"",
        "~~~",            # a different fence character does not close a backtick fence
        "[b](b.md)",
        "```",
        "[c](c.md)",
        "~~~~",
        "[d](d.md)",
        "~~~",            # shorter than the opener: does not close
        "~~~~",
        "[e](e.md) `](not-a-link)` [f](f.md)",
    ])
    assert links(text) == [(1, "a.md"), (7, "c.md"), (12, "e.md"), (12, "f.md")]


def test_inline_code_delimiters_preserve_real_links():
    assert links("``a ` ](fake.md)`` [`real`](real.md) ` unmatched [b](b.md)") == [
        (1, "real.md"), (1, "b.md"),
    ]


def test_inline_code_delimiters_and_real_neighbor_links():
    assert links("``o['f'](pathlib.Path('x')) `tick` `` [a](a.md)") == [(1, "a.md")]
    assert links("`unclosed [a](a.md)") == [(1, "a.md")]
    assert links("`one`` [a](a.md)") == [(1, "a.md")]
    assert links("[a](a.md) `](fake)` [b](b.md)") == [(1, "a.md"), (1, "b.md")]

def test_relative_links_resolve():
    broken = [
        f"{path.relative_to(ROOT)}:{number}: {target}"
        for path in markdown()
        for number, target in links(path.read_text(encoding="utf-8", errors="replace"))
        if not EXTERNAL.match(target) and not (path.parent / target).exists()
    ]
    assert not broken, "\n".join(broken)

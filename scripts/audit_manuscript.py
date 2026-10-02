#!/usr/bin/env python3
"""Audit PSC manuscript sources for stale or overclaiming formulations.

The audit is intentionally conservative: it catches phrases that caused
version drift during the v11 -> v12.1 transition. It is not a LaTeX prover;
it is a CI guardrail against known bad claims.
"""
from __future__ import annotations

import argparse
import re
import sys
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

TEXT_SUFFIXES = {".tex", ".md", ".txt", ".rst"}
DEFAULT_SKIP_DIRS = {
    ".git",
    ".pytest_cache",
    "__pycache__",
    "dist",
    "build",
    ".venv",
    "venv",
}

CURRENT_SURFACE = {
    "README.md",
    "docs/proof-ladder.md",
    "docs/conjecture-ledger.md",
    "docs/boundary-synchronization.md",
    "docs/automation-protocol.md",
}


# Every accepted transpose suffix: ^T, ^\T, ^\top, bare \top, with optional TeX braces.
TRANSPOSE = r"(?:\^\{?\s*(?:T|\\T|\\top)\s*\}?|\\top)(?![A-Za-z])"
BAD_ASSIGNMENT = r"N[_ ]?C\s*=\s*M[_ ]?sigma"
# Inter-token spacing, including TeX thin/medium/thick/negative spaces.
SEP = r"(?:\s|\\[,;:! ])*"
PARIKH_C = r"(?<![A-Za-z])P[_ ]?C(?![A-Za-z0-9])"

# Clause and sentence boundaries: terminal punctuation followed by whitespace
# (so TeX ``\,`` and decimals do not split), or a new list item / table row.
_ITEM = r"|\n(?=[ \t]*(?:[-*+|#]|\d+\.)\s)"
CLAUSE_END = re.compile(r"[.;:!?](?=\s|$)" + _ITEM)
SENTENCE_END = re.compile(r"[.!?](?=\s|$)" + _ITEM)

# Meta-text markers.  Each is anchored to the matched occurrence: a marker
# elsewhere on the line or in the paragraph never exempts it.
#   STALE_QUOTE      -- "stale/not/instead of <match>" (marker within 3 tokens).
#   NEGATED_FRAMING  -- "never describe ... <match>", "do not cite ... as <match>",
#                       "no longer <match>", "forbids describing <match>", with no
#                       independent clause between the negation and the match.
#   RETRACTED_AFTER  -- "<match> is false/withdrawn/...", predicated of the match itself.
#   RETRACTED_NEXT   -- "<match>; that premise is withdrawn" (demonstrative anaphor).
STALE_QUOTE = re.compile(
    r"\b(?:stale|old|retired|wrong|incorrect|not|never|instead\s+of|replace[sd]?)\W+(?:\S+\s+){0,2}$",
    re.IGNORECASE,
)
_RETRACTED = r"(?:false|retired|withdrawn|refuted|retracted)\b"
_FRAMING_VERB = (
    r"(?:cite|claim|assert|state|describe|use|treat|assume|say|write|present"
    r"|prove|show|establish|frame|call|regard|consider)\w*"
)
_INDEPENDENT_CLAUSE = r",\s*(?:and|but|yet|so|we|i|they|it|this|that|which|hence|thus)\b"
NEGATED_FRAMING = re.compile(
    rf"(?:\b(?:never|not|\w+n['’]t)\s+(?:\w+ly\s+)?{_FRAMING_VERB}"
    rf"|\bno\s+longer|\bforbid(?:s|ding)?\s+\w+ing)\b"
    rf"(?:(?!{_INDEPENDENT_CLAUSE}).){{0,160}}$",
    re.IGNORECASE,
)
RETRACTED_AFTER = re.compile(
    r"^\w*[\"'”’`)*]*\s*(?:and\s+)?(?:is|are|was|were|has\s+been|have\s+been)\s+"
    rf"(?:(?:now|also|thus|therefore)\s+)?{_RETRACTED}",
    re.IGNORECASE,
)
RETRACTED_NEXT = re.compile(
    r"^(?:that|this|such\s+an?)\s+(?:[\w-]+\s+){0,2}?(?:premise|target|claim|statement|assertion)\s+"
    rf"(?:is|was|has\s+been)\s+(?:now\s+)?{_RETRACTED}",
    re.IGNORECASE,
)

# Exact documentation lines known to quote a retired claim as reported speech.
# The exemption is keyed by (root-relative path, rule, whole stripped line), so
# any edit to the line -- or the same line in another file -- is audited again.
KNOWN_META_LINES: frozenset[tuple[str, str, str]] = frozenset(
    ("docs/audit-2026-09-27.md", "psc-closed-premise", line)
    for line in (
        "The repository currently has **two different notions of “PSC is closed”** and they are not reconciled.",
        "2. **Project-management premise: closed.** Issue #151 and the latest comments on #84 say the project "
        "now *treats* general PSC as closed and has moved to Tier 2. Issues #84 and #138 were manually closed "
        "on 2026-09-26.",
        "| issue #151 | “General PSC is treated as closed for this project.” |",
        "| issue #84 | **closed manually** 2026-09-26; latest project-status comment says PSC is treated as "
        "closed and #84 becomes structural Tier 2 research |",
    )
)


def _flat(s: str) -> str:
    return " ".join(s.split())


def _unit(text: str, start: int, end: int, boundary: re.Pattern[str]) -> tuple[int, int]:
    """Bounds of the clause/sentence spanning ``[start, end)``, clipped to its paragraph."""
    brk = text.rfind("\n\n", 0, start)
    para_start = 0 if brk == -1 else brk + 2
    para_end = text.find("\n\n", end)
    para_end = len(text) if para_end == -1 else para_end
    starts = [b.end() for b in boundary.finditer(text, para_start, start)]
    stop = boundary.search(text, end, para_end)
    return (starts[-1] if starts else para_start), (stop.start() if stop else para_end)


def _is_parikh_intertwiner(text: str, m: re.Match[str]) -> bool:
    """``m`` is the middle of P_C N_C = M_sigma P_C, not merely beside it."""
    return bool(
        re.search(PARIKH_C + SEP + r"$", text[max(0, m.start() - 32):m.start()], re.IGNORECASE)
        and re.match(SEP + PARIKH_C, text[m.end():], re.IGNORECASE)
    )


def _is_stale_quote(text: str, m: re.Match[str]) -> bool:
    """``m`` itself is marked stale and its sentence supplies the transposed replacement."""
    c_start, _ = _unit(text, m.start(), m.end(), CLAUSE_END)
    s_start, s_end = _unit(text, m.start(), m.end(), SENTENCE_END)
    replacement = re.compile(BAD_ASSIGNMENT + r"\s*" + TRANSPOSE, re.IGNORECASE)
    return bool(
        STALE_QUOTE.search(_flat(text[c_start:m.start()]) + " ")
        and replacement.search(text, s_start, s_end)
    )


def _is_retracted(text: str, m: re.Match[str]) -> bool:
    """``m`` is governed by a framing negation, predicated false, or retracted anaphorically."""
    c_start, c_end = _unit(text, m.start(), m.end(), CLAUSE_END)
    _, n_end = _unit(text, c_end + 1, c_end + 1, CLAUSE_END) if c_end < len(text) else (c_end, c_end)
    return bool(
        NEGATED_FRAMING.search(_flat(text[c_start:m.start()]) + " ")
        or RETRACTED_AFTER.search(_flat(text[m.end():c_end]))
        or RETRACTED_NEXT.search(_flat(text[c_end + 1:n_end]))
    )


@dataclass(frozen=True)
class Rule:
    name: str
    pattern: re.Pattern[str]
    message: str
    exemptions: tuple[Callable[[str, re.Match[str]], bool], ...] = ()


RULES: tuple[Rule, ...] = (
    Rule(
        name="synthetic-countermodel-transpose",
        pattern=re.compile(BAD_ASSIGNMENT + rf"(?!\s*{TRANSPOSE})", re.IGNORECASE),
        message="Synthetic countermodel must be N_C = M_sigma^T, P = I; not N_C = M_sigma.",
        exemptions=(_is_parikh_intertwiner, _is_stale_quote),
    ),
    Rule(
        name="old-cycle-exclusion-target",
        pattern=re.compile(r"no recurrent noncoincident cycle", re.IGNORECASE),
        message="Cycle-exclusion is a retired false target; use SCC Producer / nonsynchronizing trap framing.",
        exemptions=(_is_retracted,),
    ),
    Rule(
        name="future-replacement-overclaim",
        pattern=re.compile(r"self-contained replacement is in preparation", re.IGNORECASE),
        message="Do not promise a self-contained replacement; state the precise open conjecture instead.",
    ),
    Rule(
        name="unconditional-main-theorem",
        pattern=re.compile(
            r"Then\s+(?:the\s+)?associated\s+tiling\s+dynamical\s+system\s+has\s+pure\s+discrete\s+spectrum(?![^.]{0,120}\bconditional)",
            re.IGNORECASE | re.DOTALL,
        ),
        message="Main PDS claim must be explicitly conditional unless SCC Producer is proved.",
    ),
    Rule(
        name="psc-closed-premise",
        pattern=re.compile(
            r"(?i:\b(?:PSC|Pisot\s+Substitution\s+Conjecture)\b(?:\s+[\w-]+){0,2}?"
            r"\s+(?:is|as|was|has\s+been)\s+(?:(?:now|treated\s+as|considered)\s+)?"
            r"(?:closed|proved|proven|settled|resolved)\b)"
            r"|(?<![\w/-])post-PSC(?![\w-])"
        ),
        message="PSC is open (one open premise, OP_seed / #84); do not state or premise it as proved or closed.",
        exemptions=(_is_retracted,),
    ),
    Rule(
        name="loose-subblock-language",
        pattern=re.compile(r"contains\s+M[_ ]?sigma\s+as\s+an\s+invariant\s+sub-?block", re.IGNORECASE),
        message="Use 'acts on an invariant subspace as a similar copy of M_sigma' instead of loose sub-block language.",
    ),
)


def iter_text_files(root: Path, strict_current: bool = False):
    if strict_current:
        base = root.resolve()
        for rel in sorted(CURRENT_SURFACE):
            path = base / rel
            if path.exists():
                yield path
        return

    for path in root.rglob("*"):
        if path.is_dir():
            continue
        if any(part in DEFAULT_SKIP_DIRS for part in path.parts):
            continue
        if path.suffix.lower() in TEXT_SUFFIXES:
            yield path


def _is_known_meta_line(rel: str, rule: Rule, text: str, m: re.Match[str]) -> bool:
    line_start = text.rfind("\n", 0, m.start()) + 1
    line_end = text.find("\n", m.end())
    line = text[line_start:len(text) if line_end == -1 else line_end].strip()
    return (rel, rule.name, line) in KNOWN_META_LINES


def audit_file(path: Path, root: Path | None = None) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    rel = (path.resolve().relative_to(root.resolve()) if root else path).as_posix()
    return [
        f"{path}:{text.count(chr(10), 0, m.start()) + 1}: {rule.name}: {rule.message} "
        f"[matched: {_flat(m.group(0))!r}]"
        for rule in RULES
        for m in rule.pattern.finditer(text)
        if not (
            any(exempt(text, m) for exempt in rule.exemptions)
            or _is_known_meta_line(rel, rule, text, m)
        )
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="repository root to audit")
    parser.add_argument(
        "--strict-current",
        action="store_true",
        help="audit only the canonical current manuscript/research surface, not archives",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    failures: list[str] = []
    for path in iter_text_files(root, strict_current=args.strict_current):
        failures.extend(audit_file(path, root))

    if failures:
        print("PSC manuscript/source audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("PSC manuscript/source audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

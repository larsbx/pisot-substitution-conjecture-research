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

# Clause boundaries (for local markers) and sentence boundaries (for replacements).
CLAUSE_END = re.compile(r"[.;!?](?=\s|$)")
SENTENCE_END = re.compile(r"[.!?](?=\s|$)")

STALE_MARKER = re.compile(
    r"\b(?:stale|old|wrong|incorrect|not|never|no|instead\s+of|replace)\b[^.;!?]{0,40}$",
    re.IGNORECASE,
)
CYCLE_NEGATED_BEFORE = re.compile(
    r"(?:\b(?:no\s+longer|do\s+not|don't|never)\b[^.;!?]{0,80}"
    r"|\b(?:retired|refuted|withdrawn|false)\b[^.;!?\w]{0,4}(?:[\w-]+[^.;!?\w]{1,4}){0,3})$",
    re.IGNORECASE,
)
CYCLE_NEGATED_AFTER = re.compile(
    # The copula must predicate the target itself, not a later subordinate clause.
    r"^(?:(?!\b(?:which|that|why|because|since|so|hence|thus|but|while|whereas|although)\b)"
    r"[^.;!?]){0,80}?\b(?:is|are|was|were)\s+(?:(?:now|also|thus|therefore)\s+)?"
    r"(?:false|retired|withdrawn|refuted)\b",
    re.IGNORECASE,
)
CYCLE_NEGATED_NEXT = re.compile(
    r"^\s*(?:That|This|The|Such\s+an?)\s+(?:[\w-]+\s+){0,2}?(?:target|statement|claim|theorem)"
    r"\s+(?:is|was)\s+(?:\w+\s+)?(?:false|retired|withdrawn|refuted)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Rule:
    name: str
    pattern: re.Pattern[str]
    message: str


RULES: tuple[Rule, ...] = (
    Rule(
        name="synthetic-countermodel-transpose",
        pattern=re.compile(BAD_ASSIGNMENT + rf"(?!\s*{TRANSPOSE})", re.IGNORECASE),
        message="Synthetic countermodel must be N_C = M_sigma^T, P = I; not N_C = M_sigma.",
    ),
    Rule(
        name="old-cycle-exclusion-target",
        pattern=re.compile(r"no recurrent noncoincident cycle", re.IGNORECASE),
        message="Cycle-exclusion is a retired false target; use SCC Producer / nonsynchronizing trap framing.",
    ),
    Rule(
        name="future-replacement-overclaim",
        pattern=re.compile(r"self-contained replacement is in preparation", re.IGNORECASE),
        message="Do not promise a self-contained replacement; state the precise open conjecture instead.",
    ),
    Rule(
        name="unconditional-main-theorem",
        pattern=re.compile(
            r"Then\s+(?:the\s+)?associated\s+tiling\s+dynamical\s+system\s+has\s+pure\s+discrete\s+spectrum(?![^.]{0,120}conditional)",
            re.IGNORECASE | re.DOTALL,
        ),
        message="Main PDS claim must be explicitly conditional unless SCC Producer is proved.",
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


def _span(text: str, pos: int, end: re.Pattern[str]) -> tuple[int, int]:
    """Bounds of the unit (clause/sentence) around ``pos``, clipped to its paragraph."""
    brk = text.rfind("\n\n", 0, pos)
    para_start = 0 if brk == -1 else brk + 2
    para_end = text.find("\n\n", pos)
    para_end = len(text) if para_end == -1 else para_end
    starts = [m.end() for m in end.finditer(text, para_start, pos)]
    stop = end.search(text, pos, para_end)
    return (starts[-1] if starts else para_start), (stop.end() if stop else para_end)


def _flat(s: str) -> str:
    return " ".join(s.split())


def _is_parikh_intertwiner(text: str, m: re.Match[str]) -> bool:
    """``m`` is the middle of P_C N_C = M_sigma P_C, not merely beside it."""
    return bool(
        re.search(PARIKH_C + SEP + r"$", text[max(0, m.start() - 32):m.start()], re.IGNORECASE)
        and re.match(SEP + PARIKH_C, text[m.end():], re.IGNORECASE)
    )


def _is_stale_quote(text: str, m: re.Match[str]) -> bool:
    """``m`` itself is marked stale and its sentence supplies a transposed replacement."""
    c_start, _ = _span(text, m.start(), CLAUSE_END)
    s_start, s_end = _span(text, m.start(), SENTENCE_END)
    replacement = re.compile(BAD_ASSIGNMENT + r"\s*" + TRANSPOSE, re.IGNORECASE)
    return bool(
        STALE_MARKER.search(_flat(text[c_start:m.start()]))
        and replacement.search(text, s_start, s_end)
    )


def _is_negated_cycle_claim(text: str, m: re.Match[str]) -> bool:
    """``m`` is itself marked false/retired in its clause, or by an anaphoric next sentence."""
    c_start, c_end = _span(text, m.start(), CLAUSE_END)
    _, s_end = _span(text, m.start(), SENTENCE_END)
    _, n_end = _span(text, s_end, SENTENCE_END) if s_end < len(text) else (s_end, s_end)
    return bool(
        CYCLE_NEGATED_BEFORE.search(_flat(text[c_start:m.start()]))
        or CYCLE_NEGATED_AFTER.search(_flat(text[m.end():c_end]))
        or CYCLE_NEGATED_NEXT.search(_flat(text[s_end:n_end]))
    )


EXEMPTIONS = {
    "synthetic-countermodel-transpose": (_is_parikh_intertwiner, _is_stale_quote),
    "old-cycle-exclusion-target": (_is_negated_cycle_claim,),
}


def audit_file(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    return [
        f"{path}:{text.count(chr(10), 0, m.start()) + 1}: {rule.name}: {rule.message} "
        f"[matched: {_flat(m.group(0))!r}]"
        for rule in RULES
        for m in rule.pattern.finditer(text)
        if not any(exempt(text, m) for exempt in EXEMPTIONS.get(rule.name, ()))
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
        failures.extend(audit_file(path))

    if failures:
        print("PSC manuscript/source audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("PSC manuscript/source audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

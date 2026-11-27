#!/usr/bin/env python3
"""Audit PSC manuscript sources for stale or overclaiming formulations.

The audit catches known stale formulations, not arbitrary mathematical errors.
By default it checks live text and excludes the explicit historical roots below.
Use --report-history for a separate, nonblocking report of preserved artifacts.
It does not compare rendered PDF text with TeX or validate citation keys.
"""
from __future__ import annotations

import argparse
import os
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
    ".lake",
    ".pixi",
    "node_modules",
}

# These are preserved records, not live assertions. Do not silence dated files
# in docs/ by filename: those remain live unless moved into a historical root.
HISTORICAL_ROOTS = {
    "archive": "preserved historical snapshots",
    "sources": "imported source/provenance records",
    "evidence": "recorded execution and acceptance artifacts",
}

CURRENT_SURFACE = {
    "README.md",
    "docs/proof-ladder.md",
    "docs/conjecture-ledger.md",
    "docs/boundary-synchronization.md",
    "docs/automation-protocol.md",
}


@dataclass(frozen=True)
class Rule:
    name: str
    pattern: re.Pattern[str]
    message: str


# Deliberately bounded notation support; this is not a TeX parser. Keeping the
# spellings explicit makes the negative controls and the audit's limits clear.
_C1 = r"\bC(?:1|_1|_\{1\})(?!\w)"
_C4 = r"\bC(?:4|_4|_\{4\})(?!\w)"
_MATH_SPACE = r"[\s$`]*"
_IFF = (
    r"(?:<=>|<->|⇔|↔|\\(?:Longleftrightarrow|Leftrightarrow|iff)\b"
    r"|\biff\b|\b(?:is\s+)?equivalent\s+to\b)"
)
_N_C = r"N(?:_C|_\{C\}|C)(?!\w)"
_Q2 = r"Q(?:2|_2|_\{2\})(?!\w)"
_Q3 = r"Q(?:3|_3|_\{3\})(?!\w)"
# A corrected unsigned equation may include extra terms (for example +2 Q2 B).
# Only the complete legacy RHS is the known-bad general normalized interface.
_NO_EXTRA_TERM = r"(?![\s$`]*(?:[+\-−×*/]|\\(?:pm|mp|cdot|times)\b))"


RULES: tuple[Rule, ...] = (
    Rule(
        name="c1-c4-equivalence",
        pattern=re.compile(
            rf"(?:{_C1}{_MATH_SPACE}{_IFF}{_MATH_SPACE}{_C4}"
            rf"|{_C4}{_MATH_SPACE}{_IFF}{_MATH_SPACE}{_C1})",
            re.IGNORECASE,
        ),
        message="The C4/C1 dependency is one-way: preserve the G1 extraction premise and do not assert equivalence.",
    ),
    Rule(
        name="unsigned-normalized-transfer",
        pattern=re.compile(
            rf"(?:\b{_Q2}{_MATH_SPACE}{_N_C}\s*=\s*"
            rf"(?:\\?Lambda|Λ)\s*\^?\{{?2\}}?\s*\([^()\n=]+\)\s*{_Q2}"
            rf"|\b{_Q3}{_MATH_SPACE}{_N_C}\s*=\s*"
            rf"(?:\\?Phi|Φ)\s*_?\{{?3\}}?(?:\s*\([^()\n=]+\))?\s*{_Q3})"
            + _NO_EXTRA_TERM,
            re.IGNORECASE,
        ),
        message="Normalized degree-2/3 transfer uses signed S=A-B, not unsigned N_C=A+B.",
    ),
    Rule(
        name="predecessor-contraction-g1",
        pattern=re.compile(
            r"\bpredecessor[-\s]+contraction(?:\s+(?:argument|alone))?\s+"
            r"(?:(?:proves?|establishes|implies|yields|gives|settles)\s+"
            r"|(?:=>|⇒|\\Rightarrow)\s*|(?:is\s+a\s+)?proof\s+of\s+)"
            r"(?:G(?:1|_1|_\{1\})(?!\w)|BPA\s+finiteness\b|finite\s+BPA\b)",
            re.IGNORECASE,
        ),
        message="Predecessor contraction is a withdrawn G1 argument; it does not prove forward BPA finiteness.",
    ),
    Rule(
        name="synthetic-countermodel-transpose",
        pattern=re.compile(r"N[_ ]?C\s*=\s*M[_ ]?sigma(?!\s*(?:\^T|\\top|\^\\top|\^\\T))", re.IGNORECASE),
        message="Synthetic countermodel must be N_C = M_sigma^T, P = I; not N_C = M_sigma.",
    ),
    Rule(
        name="old-cycle-exclusion-target",
        pattern=re.compile(r"no recurrent noncoincident cycles?\b", re.IGNORECASE),
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
        name="psc-closed-premise",
        pattern=re.compile(
            r"(?i:\b(?:PSC|Pisot\s+Substitution\s+Conjecture)\b(?:\s+[\w-]+){0,2}?"
            r"\s+(?:is|as|was|has\s+been)\s+(?:(?:now|treated\s+as|considered)\s+)?"
            r"(?:closed|proved|proven|settled|resolved)\b)"
            r"|(?<![\w/-])post-PSC(?![\w-])"
        ),
        message="PSC is open (one open premise, OP_seed / #84); do not state or premise it as proved or closed.",
    ),
    Rule(
        name="loose-subblock-language",
        pattern=re.compile(r"contains\s+M[_ ]?sigma\s+as\s+an\s+invariant\s+sub-?block", re.IGNORECASE),
        message="Use 'acts on an invariant subspace as a similar copy of M_sigma' instead of loose sub-block language.",
    ),
)


def iter_text_files(root: Path, strict_current: bool = False, historical: bool = False):
    if strict_current:
        base = root.resolve()
        for rel in sorted(CURRENT_SURFACE):
            path = base / rel
            if path.exists():
                yield path
        return

    # Prune toolchain/dependency trees before visiting them. Sorting both levels
    # makes output stable, and paths are classified relative to the audit root.
    for parent, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in DEFAULT_SKIP_DIRS)
        for name in sorted(files):
            path = Path(parent) / name
            relative = path.relative_to(root)
            if (relative.parts[0] in HISTORICAL_ROOTS) != historical:
                continue
            if path.suffix.lower() in TEXT_SUFFIXES:
                yield path


def claim_context(text: str, start: int, end: int) -> tuple[str, str]:
    """The surrounding clause, without borrowing a negation from another claim."""
    boundary = (
        r"[.!?;,]|\n\s*\n|\n[ \t]*(?:[-*+]|\d+[.)])[ \t]+"
        r"|\b(?:but|however|nevertheless|while)\b"
    )
    before = re.split(boundary, text[:start], flags=re.IGNORECASE)[-1]
    after = re.split(boundary, text[end:], flags=re.IGNORECASE)[0]

    def plain(value: str) -> str:
        value = re.sub(r"\\(?:emph|textbf|textit|texttt)\{([^{}]*)\}", r"\1", value)
        return " ".join(re.sub(r"[`*$\"'“”‘’{}]", "", value).split())

    return plain(before), plain(after)


def explicitly_rejected(text: str, start: int, end: int, *, allow_chain: bool = False) -> bool:
    before, after = claim_context(text, start, end)
    # Historical dating alone is not a retraction. Require an actual rejection
    # directly attached to the matched assertion. A different argument being
    # false, or a rejection itself being negated, must not silence this claim.
    qualifiers = r"(?:(?:the|a|an|earlier|historical|old|universal|normalized|unsigned|following)\s+)*"
    subject = r"(?:(?:claim|equivalence|identity|formula|statement|argument|proof|conclusion|step|target|formulation)\s*)?"
    rejected = re.search(
        r"\b(?:false|retired|withdrawn|incorrect|invalid|unsupported|unproved|"
        r"reject(?:s|ed)?|refute(?:s|d)?|defeats?|avoid)\s*"
        + qualifiers + subject + r"(?:(?:that|of)\s*)?(?:there\s+(?:is|are)\s*)?$",
        before,
        re.IGNORECASE,
    )
    if rejected and not re.search(
        r"\b(?:not|never)(?:\s+(?:a|an|the))?$", before[:rejected.start()].strip(), re.IGNORECASE
    ):
        return True
    if re.search(
        r"\b(?:(?:do not|don't|never|must not)\s+(?:claim|assert|infer|use|revive|promote|accept|conclude)\s*"
        r"|not\s*|no longer\s+(?:there\s+(?:is|are)\s*)?)$",
        before,
        re.IGNORECASE,
    ):
        return True
    if allow_chain:
        after = re.sub(r"^(?:(?:->|=>|→|⇒)\s*[\w()+-]+\s*)+", "", after)
    return bool(re.match(
        r"^(?:and\s+)?(?:is|was|remains|are|were|has been)\s+(?:now\s+)?"
        r"(?:false|retired|withdrawn|incorrect|invalid|rejected|refuted|unproved|"
        r"not\s+(?:established|proved|valid|correct|true))\b",
        after,
        re.IGNORECASE,
    ))


def audit_file(path: Path) -> list[str]:
    try:
        text = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return []
    failures: list[str] = []
    for rule in RULES:
        for match in rule.pattern.finditer(text):
            # Use paragraph context so ordinary TeX/Markdown line wrapping does
            # not change the semantic audit result.
            para_break = text.rfind("\n\n", 0, match.start())
            para_start = 0 if para_break == -1 else para_break + 2
            para_end = text.find("\n\n", match.end())
            if para_end == -1:
                para_end = len(text)
            paragraph = " ".join(text[para_start:para_end].split())

            if rule.name in {
                "c1-c4-equivalence",
                "unsigned-normalized-transfer",
                "predecessor-contraction-g1",
            } and explicitly_rejected(text, match.start(), match.end()):
                continue

            if rule.name == "synthetic-countermodel-transpose":
                # Exempt only the exact occurrence that is syntactically the
                # middle of the proved Parikh intertwiner
                # P_C N_C = M_sigma P_C.  A second bad assignment elsewhere
                # on the same line/paragraph must still be rejected.
                before = text[max(0, match.start() - 32):match.start()]
                after = text[match.end():match.end() + 32]
                if (
                    re.search(r"P[_ ]?C\s*$", before, re.IGNORECASE)
                    and re.match(r"\s+P[_ ]?C\b", after, re.IGNORECASE)
                ):
                    continue

                # Guidance may quote the stale form if it explicitly requires
                # a supported transposed replacement.  Match all transpose
                # spellings accepted by the base rule.
                transpose = (
                    r"N[_ ]?C\s*=\s*M[_ ]?sigma"
                    r"\s*(?:\^T|\\top|\^\\top|\^\\T)"
                )
                if (
                    re.search(transpose, paragraph, re.IGNORECASE)
                    and re.search(
                        r"\b(?:must|instead|stale|replace|replacement|should)\b",
                        paragraph,
                        re.IGNORECASE,
                    )
                ):
                    continue

            if rule.name == "old-cycle-exclusion-target":
                # Permit only explicit rejection/retirement of the matched
                # target.  Mere historical framing such as "earlier work
                # proves ..." is still an affirmative false claim and fails.
                if explicitly_rejected(text, match.start(), match.end(), allow_chain=True):
                    continue

            if rule.name == "psc-closed-premise":
                # The project's final human review is after closure; stating
                # that timing does not assert that closure already happened.
                before, after = claim_context(text, match.start(), match.end())
                if (
                    match.group(0) == "post-PSC"
                    and re.search(r"\bHuman (?:mathematical )?(?:review|validation) (?:is|remains)$", before)
                    and not after
                ):
                    continue
                # Permit only guidance or retraction that negates the claim,
                # e.g. "Never describe ... PSC as proved" or "... is withdrawn".
                # A Markdown list is read together with the colon-terminated
                # lead-in paragraph that introduces it ("Avoid these ...:").
                context = paragraph
                if re.match(r"[-*+]\s|\d+[.)]\s", paragraph):
                    lead_end = para_start - 2 if para_break != -1 else -1
                    lead_break = text.rfind("\n\n", 0, max(lead_end, 0))
                    lead = " ".join(text[lead_break + 2 if lead_break != -1 else 0:max(lead_end, 0)].split())
                    if lead.endswith(":"):
                        context = f"{lead} {paragraph}"
                if re.search(
                    r"\b(?:never|not|withdrawn|false|retired|no longer|avoid)\b",
                    context,
                    re.IGNORECASE,
                ):
                    continue

            line = text.count("\n", 0, match.start()) + 1
            snippet = " ".join(match.group(0).split())
            failures.append(f"{path}:{line}: {rule.name}: {rule.message} [matched: {snippet!r}]")
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="repository root to audit")
    parser.add_argument(
        "--strict-current",
        action="store_true",
        help="audit only the canonical current manuscript/research surface, not archives",
    )
    parser.add_argument(
        "--report-history",
        action="store_true",
        help="separately report findings in archive/, sources/ and evidence/ without failing live acceptance",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    failures: list[str] = []
    for path in iter_text_files(root, strict_current=args.strict_current):
        failures.extend(audit_file(path))

    if args.report_history:
        historical = [
            finding
            for path in iter_text_files(root, historical=True)
            for finding in audit_file(path)
        ]
        print(f"Historical manuscript/source findings (nonblocking): {len(historical)}")
        for finding in historical:
            print(f"  - {finding}")

    if failures:
        print("PSC manuscript/source audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"  - {failure}", file=sys.stderr)
        return 1
    print("PSC manuscript/source audit passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

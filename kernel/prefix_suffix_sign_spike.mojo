"""Deterministic Mojo exploratory spike: Branch B vs endpoint profiles.

This is a finite *prefix* of the canonical PIP corpus in its fixed enumeration
order, not random data and not a theorem. To cover all 4554 use --limit 4554.
Any capped BPA is counted as inconclusive, not a negative Branch-B result.

Replay:
    cd kernel
    pixi run mojo run -I . prefix_suffix_sign_spike.mojo --limit 4554 --state-cap 20000
"""

from std.sys import argv
from psc.corpus import pip_corpus, STATE_CAP, report_progress
from psc.endpoint_sign_spike import SpikeTotals, audit_specimen


def read_budget(text: String) raises -> Int:
    if text.byte_length() == 0 or text.byte_length() > 8:
        raise Error("budget must be 1..8 ASCII digits")
    for digit in text.codepoint_slices():
        if String(digit) < "0" or String(digit) > "9":
            raise Error("budget must be an unsigned integer")
    var n = atol(text)
    if n <= 0:
        raise Error("budget must be positive")
    return n


def main() raises:
    var args = argv()
    var limit = 4554
    var cap = STATE_CAP
    var witnesses = False
    var i = 1
    while i < len(args):
        if args[i] == "--help":
            print("prefix_suffix_sign_spike.mojo [--limit 4554] [--state-cap 20000] [--witnesses]")
            print("Deterministic finite corpus prefix, no universal claim; caps inconclusive.")
            return
        if args[i] == "--witnesses":
            witnesses = True
            i += 1
            continue
        if i + 1 >= len(args):
            raise Error("missing command option value")
        var value = read_budget(args[i + 1])
        if args[i] == "--limit":
            limit = value
        elif args[i] == "--state-cap":
            cap = value
        else:
            raise Error("unknown spike option")
        i += 2

    var corpus = pip_corpus()
    if limit > len(corpus):
        raise Error("requested limit exceeds the 4554-member canonical corpus")
    var tally = SpikeTotals()
    print("ENDPOINT_SIGN_SPIKE_START corpus_prefix=", limit, " state_cap=", cap)
    for k in range(limit):
        ref spec = corpus[k]
        audit_specimen(spec.sigma, cap, spec.label(), tally, witnesses)
        if (k + 1) % 500 == 0:
            report_progress(k + 1)
    tally.print_summary()
    if tally.visited != limit:
        raise Error("census prefix coverage mismatch")
    if tally.branch_a + tally.branch_b + tally.branch_c != tally.closed:
        raise Error("closed SCC branch taxonomy did not partition")
    if tally.biinjective_a + tally.biinjective_b + tally.biinjective_c != tally.biinjective_closed:
        raise Error("bi-injective branch taxonomy did not partition")
    if tally.b_endpoint_diagonal + tally.b_no_endpoint_diagonal != tally.branch_b:
        raise Error("Branch-B diagonal totals did not partition")
    if tally.b_endpoint_gauge + tally.b_no_endpoint_gauge != tally.branch_b:
        raise Error("Branch-B gauge totals did not partition")
    print("ENDPOINT_SIGN_SPIKE_COMPLETE finite_evidence_only=1 capped=", tally.capped)

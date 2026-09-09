#!/usr/bin/env bash
# Run every verification layer. Each layer is skipped, with a notice, if its
# toolchain is absent -- so a partial environment reports honestly rather than
# passing vacuously.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)
status=0
ran=0
skipped=0

section() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }
ok()      { printf '  \033[32mPASS\033[0m  %s\n' "$1"; ran=$((ran+1)); }
bad()     { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; status=1; ran=$((ran+1)); }
skip()    { printf '  \033[33mSKIP\033[0m  %s (%s)\n' "$1" "$2"; skipped=$((skipped+1)); }

section "Python reference implementation"
if command -v pytest >/dev/null 2>&1; then
    if pytest -q >/dev/null 2>&1; then ok "pytest"; else bad "pytest"; fi
else
    skip "pytest" "not installed; pip install -e .[dev]"
fi

section "Mojo exact kernel"
if command -v pixi >/dev/null 2>&1; then
    cd "$ROOT/mojo"
    if pixi run mojo run -I . tests/test_kernel.mojo 2>&1 | tail -1 | grep -q "tests passed"; then
        ok "kernel regression tests"
    else
        bad "kernel regression tests"
    fi
    if pixi run mojo run -I . verify.mojo 2>&1 | tail -1 | grep -q "checks passed"; then
        ok "certificate checks (verify.mojo)"
    else
        bad "certificate checks (verify.mojo)"
    fi

    census_out=$(pixi run mojo run -I . census.mojo 2>&1)
    if grep -Eq 'PIP specimens \(images of length <= 3\):[[:space:]]+4554' <<<"$census_out" \
       && grep -Eq 'B_sigma construction terminated:[[:space:]]+4554.*capped:[[:space:]]+0' <<<"$census_out" \
       && grep -Eq 'productive:[[:space:]]+4554.*non-productive:[[:space:]]+0' <<<"$census_out"; then
        ok "alphabet-3 census (4554 PIP; 0 capped; 0 nonproductive)"
    else
        bad "alphabet-3 census regression"
        tail -20 <<<"$census_out"
    fi
    cd "$ROOT"
else
    skip "Mojo layer" "pixi not installed; curl -fsSL https://pixi.sh/install.sh | bash"
fi

section "TLA+ models"
JAR="${TLA_TOOLS:-$ROOT/tla/tla2tools.jar}"
if command -v java >/dev/null 2>&1 && [ -f "$JAR" ]; then
    if TLA_TOOLS="$JAR" ./tla/check.sh; then ok "all models"; else bad "some model"; fi
else
    skip "TLA+ layer" "need java and tla2tools.jar (set TLA_TOOLS, or download into tla/)"
fi

section "Lean 4 proofs"
if command -v lake >/dev/null 2>&1; then
    cd "$ROOT/PscVerif"
    out=$(lake build PscVerif 2>&1)
    if grep -q "Build completed successfully" <<<"$out"; then
        if grep -q "sorryAx" <<<"$out"; then
            bad "lake build (sorryAx present)"
        else
            ok "lake build + axiom audit"
        fi
    else
        bad "lake build"
        tail -20 <<<"$out"
    fi
    cd "$ROOT"
else
    skip "Lean layer" "lake not on PATH; install elan"
fi

printf '\n%d checks run, %d skipped. ' "$ran" "$skipped"
if [ $status -eq 0 ]; then printf 'All run checks passed.\n'; else printf 'FAILURES above.\n'; fi
exit $status
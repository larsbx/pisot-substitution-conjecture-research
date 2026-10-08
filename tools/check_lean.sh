#!/usr/bin/env bash
# Always replay the audit, including when Lake reuses every compiled module.
set -euo pipefail
PSC_ROOT=$(cd "$(dirname "$0")/.." && pwd -P)
python3 "$PSC_ROOT/tools/make_proof_bank.py" --check
PSC_AUDIT_LOG=$(mktemp)
trap 'rm -f "$PSC_AUDIT_LOG"' EXIT
cd "$PSC_ROOT/proof/PscVerif"
lake build PscVerif
lake env lean ProofBankAudit.lean | tee "$PSC_AUDIT_LOG"
python3 "$PSC_ROOT/tools/make_proof_bank.py" --check --audit-log "$PSC_AUDIT_LOG"

#!/usr/bin/env bash
# APEX certification gate: build must already be done (lake build).
# 1. run every `#print axioms` target; 2. compare with the accepted-theorem registry; 3. reject non-standard axioms,
# missing/extra targets, empty reports, Lean errors; 4. reject forbidden constructs in comment-stripped sources.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
lean_dir="${APEX_LEAN_DIR:-$here/Lean}"
report="$(mktemp)"
trap 'rm -f "$report"' EXIT
( cd "$lean_dir" && lake env lean scripts/Axioms.lean ) > "$report" 2>&1 || { cat "$report"; echo "FAIL: lean exited non-zero"; exit 1; }
cat "$report"
python3 -I "$here/cert_check.py" "$report" "$here/Audit/ACCEPTED_THEOREMS.txt" "$lean_dir/scripts/Axioms.lean" "$lean_dir/APEX"

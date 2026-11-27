#!/usr/bin/env bash
# Local / CI check: every #print axioms target uses only propext, Classical.choice, Quot.sound,
# and no accepted source contains sorry / admit / native_decide / axiom declarations.
set -euo pipefail
cd "${APEX_LEAN_DIR:-$(dirname "$0")/Lean}"
out=$(lake env lean scripts/Axioms.lean)
echo "$out"
n=$(echo "$out" | grep -c "depends on axioms" || true)
flat=$(echo "$out" | tr '\n' ' ' | sed 's/ \+/ /g')
bad=$(echo "$flat" | grep -oE "depends on axioms: \[[^]]*\]" | grep -vE "^depends on axioms: \[(propext|Classical.choice|Quot.sound)(, (propext|Classical.choice|Quot.sound))*\]$" || true)
if [ -n "$bad" ]; then echo "NON-STANDARD AXIOMS: $bad"; exit 1; fi
if grep -rnE "^\s*(axiom|sorry|admit)\b|\bsorry\b|native_decide" APEX --include=*.lean | grep -v -- "--\|no \`native_decide\`" ; then echo "FORBIDDEN TOKEN"; exit 1; fi
echo "OK: $n targets, standard axioms only"

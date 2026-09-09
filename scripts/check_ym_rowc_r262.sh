#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Physics/YangMills/BalabanCMP116PhysicalDecoupledComparisonRound261Exact.agda
  DASHI/Physics/YangMills/BalabanPreferredRowCFrontierRound262Exact.agda
  DASHI/Physics/YangMills/BalabanRowC262FocusedValidation.agda
)

FORBIDDEN_PATTERN='(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Row-C R262 source missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "Row-C R262 source contains forbidden proof escape hatch: $file" >&2
    exit 1
  fi
done

# Compile only when Agda is available.  This is deliberately a focused cone:
# it avoids replaying the full historical YM rollup on constrained machines.
if command -v agda >/dev/null 2>&1; then
  agda -i . -i /usr/share/agda-stdlib \
    DASHI/Physics/YangMills/BalabanRowC262FocusedValidation.agda
fi

echo "YM Row-C R261 physical-decoupled comparison / R260 anchor / R262 frontier source gate passed"

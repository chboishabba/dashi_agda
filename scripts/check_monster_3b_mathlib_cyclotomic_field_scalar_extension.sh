#!/usr/bin/env bash
set -euo pipefail
ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BMathlibCyclotomicFieldScalarExtensionExact.agda"
[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }
required=(
  "record MathlibCyclotomicFieldCoordinate"
  "Mathlib/NumberTheory/Cyclotomic/Basic.lean"
  "CyclotomicField 3 ℚ"
  "AlgebraicClosure (CyclotomicField 3 ℚ)"
  "record DashiCyclotomic3ToMathlibCyclotomicFieldTransport"
  "dashiPairPresentationIsCyclotomicField"
  "algebraicClosureTargetIsAlgClosed"
  "pairPresentationDoesNotFollowFromDimensionTwo"
  "A005052"
)
for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || { echo "missing mathlib cyclotomic scalar extension marker: $needle" >&2; exit 1; }
done
echo "monster 3B mathlib cyclotomic scalar extension check: ok"

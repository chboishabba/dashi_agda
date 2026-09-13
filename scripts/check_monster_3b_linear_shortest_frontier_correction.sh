#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BLinearShortestFrontierCorrectionExact.agda"

required=(
  "record LinearShortest3BFrontierSource"
  "historicalFiniteBasisCapstone"
  "linearZetaSector"
  "linearMultiplicityHomSpace"
  "finiteBasisChartStillValid"
  "pureFinNinetyInertiaRouteRefuted"
  "actualLinearSameActionStillRequired"
  "twelveSeventyEightCharacterAlreadyPaid"
  "genericIsotypicCompilerStillNeedsKernelReceipt"
  "finiteChartDoesNotCreateLinearMultiplicityAction"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing corrected linear shortest-frontier surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B corrected linear shortest frontier check: ok"

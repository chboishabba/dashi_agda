#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact.agda"

required=(
  "record CanonicalLinearMultiplicityRoute"
  "record PermutationBasisPromotionReceipt"
  "linearRouteDoesNotRequirePermutationBasis"
  "oldFinNinetyRouteRequiresBasisPreservation"
  "characterEvidenceDoesNotPayPermutationReceipt"
  "import DASHI.Foundations.TernaryGolay.CodeBoundary as GolayBoundary"
  "import DASHI.Geometry.HilbertLorentzForcing as Linear"
  "linearCarrier : Linear.HilbertLift"
  "linearAction : Linear.LinearAction linearCarrier"
  "golayBoundaryCrossPollination"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing required WrongType correction surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B multiplicity basis-vs-linear WrongType check: ok"

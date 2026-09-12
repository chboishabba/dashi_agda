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

# Run the bounded linear-multiplicity frontier as one pre-GAP static tranche.
# These checks deliberately validate source/proof-route surfaces only; they do
# not claim Agda kernel certification.
bash "$ROOT/scripts/check_monster_3b_suzuki_90_not_permutation_character.sh"
bash "$ROOT/scripts/check_monster_3b_linear_multiplicity_hom_space.sh"
bash "$ROOT/scripts/check_monster_3b_linear_zeta_sector_restriction.sh"
bash "$ROOT/scripts/check_graded_representation_linear_realisation.sh"
bash "$ROOT/scripts/check_monster_weight_two_linear_action_bridge.sh"
bash "$ROOT/scripts/check_graded_voa_homogeneous_linear_realisation.sh"
bash "$ROOT/scripts/check_monster_3b_actual_linear_multiplicity_acquisition.sh"

echo "monster 3B linear multiplicity frontier static tranche: ok"

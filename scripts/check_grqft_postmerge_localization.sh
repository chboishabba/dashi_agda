#!/usr/bin/env bash
set -euo pipefail

files=(
  DASHI/Physics/Closure/DrellYanRatioAbsoluteDefectLocalizationExact.agda
  DASHI/Physics/Closure/DrellYanRatioAbsoluteDefectLocalizationValidation.agda
  DASHI/Physics/Closure/ColliderChiSquareScopeMatrixExact.agda
  DASHI/Physics/Closure/ColliderChiSquareScopeMatrixValidation.agda
  DASHI/Physics/Foundations/CMP119PinnedYMGRQFTSectorStressBridgeExact.agda
  DASHI/Physics/Foundations/CMP119PinnedYMGRQFTSectorStressBridgeValidation.agda
  DASHI/Physics/Foundations/GRQFTPostMergeMaxCutExact.agda
  DASHI/Physics/Foundations/GRQFTPostMergeMaxCutValidation.agda
  DASHI/Physics/Foundations/GRQFTActiveGaugeSectorTotalizationExact.agda
  DASHI/Physics/Foundations/CMP119SingleActiveSectorSourceFactorisationExact.agda
  DASHI/Physics/Foundations/CMP119SingleActiveSectorSourceFactorisationValidation.agda
  DASHI/Physics/Foundations/CMP119SingleSectorSharedSourceStressWeldExact.agda
  DASHI/Physics/Foundations/CMP119SingleSectorSharedSourceStressWeldValidation.agda
  DASHI/Physics/Foundations/GRAnchoredSharedEffectiveSourceExact.agda
  DASHI/Physics/Foundations/CMP119GRAnchoredStressWeldCompilerExact.agda
  DASHI/Physics/Foundations/CMP119GRAnchoredStressWeldCompilerValidation.agda
  DASHI/Physics/Foundations/GRRecoveryVsSchwarzschildValidationExact.agda
  DASHI/Physics/Foundations/GRRecoveryVsSchwarzschildValidationValidation.agda
  DASHI/Physics/Foundations/StressEnergyWeldMathematicalCoreExact.agda
  DASHI/Physics/Foundations/CMP119GRAnchoredStressMathematicalCoreExact.agda
  DASHI/Physics/Foundations/StressEnergyWeldMathematicalCoreValidation.agda
  DASHI/Physics/Foundations/StressEnergyEqualityCoreExact.agda
  DASHI/Physics/Foundations/CMP119GRAnchoredStressEqualityCoreExact.agda
  DASHI/Physics/Foundations/StressEnergyEqualityCoreValidation.agda
  DASHI/Physics/Foundations/SingleSectorUnifiedCandidateExact.agda
  DASHI/Physics/Foundations/SingleSectorRecoveryTransportExact.agda
  DASHI/Physics/Foundations/SingleSectorUnifiedCandidateValidation.agda
  DASHI/Physics/Foundations/GRHolonomyTaylorRicciEvidenceExact.agda
  DASHI/Physics/Foundations/GRDiscreteToSmoothMaxCutExact.agda
  DASHI/Physics/Foundations/GRDiscreteToSmoothMaxCutValidation.agda
  DASHI/Physics/Foundations/RecoveryCommutationCoreExact.agda
  DASHI/Physics/Foundations/CommonRegimeMathematicalCoreExact.agda
  DASHI/Physics/Foundations/GRQFTTheoryValidationSplitExact.agda
  DASHI/Physics/Foundations/GRQFTTheoryValidationSplitValidation.agda
  DASHI/Physics/Foundations/GRQFTRationalStressComponentCutExact.agda
  DASHI/Physics/Foundations/GRQFTConcreteInstanceFrontierV2Exact.agda
  DASHI/Physics/Foundations/GRQFTConcreteInstanceFrontierV2Validation.agda
  DASHI/Physics/Closure/DrellYanRatioCancellationBoundaryExact.agda
  DASHI/Physics/Closure/ColliderLowChiSquareProvenanceLadderExact.agda
  DASHI/Physics/Closure/W4ProjectionOperatorAblationRequestExact.agda
)

for f in "${files[@]}"; do
  test -f "$f"
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)' "$f"; then
    echo "forbidden trust/hole pattern in $f" >&2
    exit 1
  fi
done

tmp1="$(mktemp)"
tmp2="$(mktemp)"
trap 'rm -f "$tmp1" "$tmp2"' EXIT
python3 scripts/grqft_dy_ratio_absolute_localization.py --output "$tmp1" >/dev/null
diff -u outputs/grqft_dy_ratio_absolute_localization.json "$tmp1"
python3 scripts/grqft_collider_chi2_scope_matrix.py --output "$tmp2" >/dev/null
diff -u outputs/grqft_collider_chi2_scope_matrix.json "$tmp2"

if command -v dashi-agda-preflight >/dev/null 2>&1; then
  for f in "${files[@]}"; do
    dashi-agda-preflight "$f"
  done
fi

# The W4 operator ablation is executed as a diagnostic but is not diffed against
# a committed numeric artifact: its purpose is to discover which branch of the
# next proof/search cut is live on this exact head.
ablation_json="$(mktemp)"
trap 'rm -f "$tmp1" "$tmp2" "$ablation_json"' EXIT
python3 scripts/grqft_w4_projection_operator_ablation.py --output "$ablation_json"
python3 - "$ablation_json" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
assert p["promotesW4"] is False
assert p["sharedWindowGeV"] == [76,106]
for k in ("currentW4SigmaDashiShape","ratioPathFivePointDenominatorDensity"):
    assert p[k]["dof"] == 17
    assert p[k]["chi2PerDof"] >= 0
print("projection-ablation:", p["currentW4SigmaDashiShape"]["chi2PerDof"],
      "->", p["ratioPathFivePointDenominatorDensity"]["chi2PerDof"])
PY

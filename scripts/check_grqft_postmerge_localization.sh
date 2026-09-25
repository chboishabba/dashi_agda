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
  DASHI/Physics/Foundations/GRQFTCommonRegimeBidiAttemptExact.agda
  DASHI/Physics/Foundations/GRQFTCommonRegimeBidiAttemptValidation.agda
  DASHI/Physics/Foundations/CMP119MetricBasisStressComponentCompilerExact.agda
  DASHI/Physics/Foundations/CMP119MetricBasisStressComponentCompilerValidation.agda
  DASHI/Physics/Foundations/CMP119SymmetricStressComponentReductionExact.agda
  DASHI/Physics/Foundations/CMP119SymmetrySemanticBridgeExact.agda
  DASHI/Physics/Foundations/CMP119SymmetricStressComponentReductionValidation.agda
  DASHI/Physics/Foundations/CMP119SymmetricMetricBasisRealizationExact.agda
  DASHI/Physics/Foundations/CMP119SymmetricMetricBasisRealizationValidation.agda
  DASHI/Physics/Foundations/GRQFTSourceNativeQFTRecoveryProvenanceExact.agda
  DASHI/Physics/Foundations/GRQFTSourceNativeQFTRecoveryProvenanceValidation.agda
  DASHI/Physics/Foundations/GRQFTR457SourceNativeRecoveryBindingExact.agda
  DASHI/Physics/Foundations/GRQFTR457SourceNativeRecoveryBindingValidation.agda
  DASHI/Physics/Foundations/CMP119SymmetricFiniteTangentBasisCompilerExact.agda
  DASHI/Physics/Foundations/CMP119SymmetricFiniteTangentBasisCompilerValidation.agda
  DASHI/Physics/Foundations/CMP119ActiveRawSymmetricTangentSpecializationExact.agda
  DASHI/Physics/Foundations/CMP119ActiveRawSymmetricTangentSpecializationValidation.agda
  DASHI/Physics/Foundations/CMP119SymmetricPresentCutCarrierCompilerExact.agda
  DASHI/Physics/Foundations/CMP119SymmetricPresentCutCarrierCompilerValidation.agda
  DASHI/Physics/Foundations/CMP119TenFiniteD1ComponentCompilerExact.agda
  DASHI/Physics/Foundations/CMP119GRQFTD1MaxCutExact.agda
  DASHI/Physics/Foundations/CMP119FourDiagonalFiniteD1ActiveStressExact.agda
  DASHI/Physics/Foundations/CMP119FourD1LocalizedPositiveGRepulsionExact.agda
  DASHI/Physics/Foundations/CMP119FourDiagonalLiteralFiniteMeasureActiveStressExact.agda
  DASHI/Physics/Foundations/CMP119AntigravitySourceMaxCutExact.agda
  DASHI/Physics/Foundations/CMP119RationalFiniteMeasureIntegrationLawsExact.agda
  DASHI/Physics/Foundations/CMP119GibbsDiagonalTraceCancellationExact.agda
  DASHI/Physics/Foundations/CMP119GibbsDiagonalTraceSignExact.agda
  DASHI/Physics/Foundations/CMP119ClassicalWilsonTraceInsertionReductionExact.agda
  DASHI/Physics/Foundations/CMP119AntigravityTraceMaxCutExact.agda
  DASHI/Physics/Foundations/CMP119ConcreteTenSlotCrossNumeratorCandidateExact.agda
  DASHI/Physics/Foundations/CMP119ConcreteTenSlotD1SourceWeldExact.agda
  DASHI/Physics/Foundations/CMP119TenActualSourceReadoutsExact.agda
  DASHI/Physics/Foundations/CMP119TenLiteralDensitySourceReadoutsExact.agda
  DASHI/Physics/Foundations/CMP119LiteralFiniteMeasureStressSourceConstructorExact.agda
  DASHI/Physics/Foundations/CMP119LiteralFiniteMeasureDensityAnchorConstructorExact.agda
  DASHI/Physics/Foundations/CMP119TenLiteralFiniteMeasureReadoutsExact.agda
  DASHI/Physics/Foundations/CMP119PhysicalFiniteMeasureNZDNDZExact.agda
  DASHI/Physics/Foundations/CMP119GibbsFiniteMeasureNZDNDZReductionExact.agda
  DASHI/Physics/Foundations/CMP119GibbsConnectedNumeratorEvaluationExact.agda
  DASHI/Physics/Foundations/CMP119ClassicalWilsonDiagonalMetricVariationExact.agda
  DASHI/Physics/Foundations/CMP119ClassicalWilsonTenMetricVariationExact.agda
  DASHI/Physics/Foundations/CMP119ClassicalCurvatureTenMetricVariationExact.agda
  DASHI/Physics/Foundations/CMP119ClassicalCurvatureStressInsertionExact.agda
  DASHI/Physics/Foundations/CMP119FlatSide4CurvatureStressExact.agda
  DASHI/Physics/Foundations/CMP119NormalizedTargetTraceSplitExact.agda
  DASHI/Physics/Closure/W4YMStressEnergyFromCurvatureSixExact.agda
  DASHI/Physics/Foundations/CMP119PinnedStressMetricRepresentationBridgeExact.agda
  DASHI/Physics/Foundations/CMP119PinnedStressMetricRepresentationBridgeValidation.agda
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

tmp_component_json="$(mktemp)"
trap 'rm -f "$tmp_component_json"' EXIT
python3 scripts/grqft_cross_sector_component_residual.py --output "$tmp_component_json"
diff -u outputs/grqft_cross_sector_component_target.json "$tmp_component_json"


# Exact post-sum finite-D1 readout path: exercise both an exact-zero target
# fixture and a one-component nonzero control.  These are harness regressions
# only; they do not claim the target numbers were derived from CMP119 source data.
tmp_d1_in="$(mktemp)"
tmp_d1_out="$(mktemp)"
tmp_d1_bad_in="$(mktemp)"
tmp_d1_bad_out="$(mktemp)"
trap 'rm -f "$tmp_component_json" "$tmp_d1_in" "$tmp_d1_out" "$tmp_d1_bad_in" "$tmp_d1_bad_out"' EXIT
cat >"$tmp_d1_in" <<'JSON'
{"qft_finite_d1_readouts":{"00":1,"01":0,"02":0,"03":0,"11":-1,"12":0,"13":0,"22":-1,"23":0,"33":-1}}
JSON
python3 scripts/grqft_cross_sector_component_residual.py --qft-json "$tmp_d1_in" --output "$tmp_d1_out"
python3 - "$tmp_d1_out" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
assert p["input_form"] == "ten post-sum finite localized D1 rational readouts"
assert p["status"] == "exact_zero"
assert p["l1_residual"] == 0
assert p["max_abs_residual"] == 0
assert p["finite_d1_readouts"] == {
    "00": 1, "01": 0, "02": 0, "03": 0,
    "11": -1, "12": 0, "13": 0,
    "22": -1, "23": 0, "33": -1,
}
PY

cat >"$tmp_d1_bad_in" <<'JSON'
{"qft_finite_d1_readouts":{"00":1,"01":0,"02":0,"03":0,"11":-1,"12":0,"13":0,"22":-1,"23":0,"33":0}}
JSON
python3 scripts/grqft_cross_sector_component_residual.py --qft-json "$tmp_d1_bad_in" --output "$tmp_d1_bad_out"
python3 - "$tmp_d1_bad_out" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
assert p["status"] == "nonzero_residual"
assert p["l1_residual"] == 1
assert p["max_abs_residual"] == 1
PY


tmp_d1_candidate="$(mktemp)"
trap 'rm -f "$tmp_d1_candidate"' EXIT
python3 scripts/grqft_ten_d1_source_candidate.py --output "$tmp_d1_candidate"
diff -u outputs/grqft_ten_d1_source_candidate.json "$tmp_d1_candidate"
python3 - "$tmp_d1_candidate" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
assert p["candidate_only"] is True
assert p["published_cmp119_expectation_identification_claimed"] is False
assert p["all_cross_numerators_exact"] is True
assert p["gr_residual_exact_zero"] is True
assert p["active_stress_is_negative_two"] is True
assert p["active_stress_rho_plus_px_plus_py_plus_pz"] == -2
PY


tmp_active="$(mktemp)"
tmp_active_zero_in="$(mktemp)"
tmp_active_zero_out="$(mktemp)"
trap 'rm -f "$tmp_active" "$tmp_active_zero_in" "$tmp_active_zero_out"' EXIT
python3 scripts/grqft_four_diagonal_active_stress.py --output "$tmp_active" >/dev/null
diff -u outputs/grqft_four_diagonal_active_stress_target.json "$tmp_active"
cat >"$tmp_active_zero_in" <<'JSON'
{"qft_diagonal_finite_d1_readouts":{"00":{"num":3,"den":2},"11":{"num":-1,"den":2},"22":{"num":-1,"den":2},"33":{"num":-1,"den":2}}}
JSON
python3 scripts/grqft_four_diagonal_active_stress.py --input "$tmp_active_zero_in" --output "$tmp_active_zero_out" >/dev/null
python3 - "$tmp_active_zero_out" <<'PY'
import json,sys
p=json.load(open(sys.argv[1]))
assert p["status"] == "zero_active_stress"
assert p["active_stress_rho_plus_px_plus_py_plus_pz"] == 0
assert p["negative_active_stress"] is False
assert p["off_diagonal_readouts_required_for_this_diagnostic"] is False
PY

#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  DASHI/Cognition/CCDCOEMultiplexGraphCutCoreExact.agda
  DASHI/Cognition/CCDCOECognitiveMultiplexInvariantExact.agda
  DASHI/Cognition/CCDCOEFiveLayerCertifiedCutExact.agda
  DASHI/Cognition/CCDCOEQueryPNFEvidenceBridgeExact.agda
  DASHI/Cognition/CCDCOEPersonalHolonomyBoundaryExact.agda
  DASHI/Cognition/CCDCOECognitiveMultiplexInvariantRegression.agda
  DASHI/Cognition/CCDCOEMaxCutRegressionExact.agda
  DASHI/Cognition/CCDCOEP3TypedIntersectionalAxisExact.agda
  DASHI/Cognition/CCDCOEP3SituatedHistoryPNFExact.agda
  DASHI/Cognition/CCDCOEP3CausalTrialecticInteractionExact.agda
  DASHI/Cognition/CCDCOEP3SourcePowerEvidenceWeldExact.agda
  DASHI/Cognition/CCDCOEP3CausalTrialecticRegressionExact.agda
  DASHI/Cognition/CCDCOEP3ClimateGenealogyCaseExact.agda
  DASHI/Cognition/CCDCOEP3API1998PrimaryPlanExact.agda
  DASHI/Cognition/CCDCOEP3EvidenceStageIdentificationExact.agda
  DASHI/Cognition/CCDCOEP3PreAPIOpinionTemporalControlExact.agda
  DASHI/Cognition/CCDCOEP3ClimateContestedAttributionExact.agda
  DASHI/Cognition/CCDCOEP3ClimateObservedActivityAndCorpusExact.agda
  DASHI/Cognition/CCDCOEP3GCCExecutedCampaignSourceExact.agda
  DASHI/Cognition/CCDCOEP3Trumbo1996IndependentMediaBaselineExact.agda
  DASHI/Cognition/CCDCOEP3G20COP21AttributionExact.agda
  DASHI/Cognition/CCDCOEP3G20ComplianceObservedExact.agda
  DASHI/Cognition/CCDCOEP3CountryImplementationJoinExact.agda
  DASHI/Cognition/CCDCOEP3G20RGMemberPanelExact.agda
  DASHI/Cognition/CCDCOEP3StakeholderHandoffExact.agda
  DASHI/Cognition/CCDCOEP3CulturalSourceGenreExact.agda
  DASHI/Cognition/CCDCOEP3CognitiveWarfareArtDiscriminatorExact.agda
  DASHI/Cognition/CCDCOEP3SameOperationIndexedAdmissionExact.agda
  DASHI/Cognition/CCDCOEP3GCC1993SourceChainExact.agda
  DASHI/Cognition/CCDCOEP3GCC1993DirectionDiscriminatorExact.agda
  DASHI/Cognition/CCDCOEP3GCC1993ClaimCodingAdmissionExact.agda
  DASHI/Cognition/CCDCOEP3GCC1993PreResponseBaselineExact.agda
  DASHI/Cognition/CCDCOEP3GCC1993PreResponseExpandedExact.agda
  DASHI/Culture/CriticalArtTemporalReceptionReuseExact.agda
  DASHI/Culture/CriticalArtSameSceneTransportExact.agda
  DASHI/Culture/CriticalArtTriadicFilmBoundaryExact.agda
  DASHI/Culture/CriticalArtEditionAuthorityExact.agda
)
for file in "${modules[@]}"; do
  test -s "$file" || { echo "Missing owner: $file" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|[{][!]|[!][}]|TERMINATING|NO_TERMINATION_CHECK|--allow-unsolved-metas' "$file"; then
    echo "Rejected postulate/meta/termination bypass: $file" >&2
    exit 1
  fi
done

python3 scripts/check_ccdcoe_cognitive_multiplex.py
python3 scripts/check_ccdcoe_p3_causal_trialectic.py
python3 scripts/check_ccdcoe_p3_climate_case.py
python3 scripts/check_ccdcoe_p3_gcc_campaign.py
python3 scripts/check_ccdcoe_p3_g20_cop21.py --self-test
python3 scripts/check_ccdcoe_p3_g20_cop21.py
python3 scripts/check_ccdcoe_p3_country_implementation.py --self-test
python3 scripts/check_ccdcoe_p3_g20rg_member_panel.py --self-test
python3 scripts/check_ccdcoe_p3_g20rg_member_panel.py
python3 scripts/check_ccdcoe_p3_stakeholder_handoff.py --self-test
python3 scripts/check_ccdcoe_p3_stakeholder_handoff.py
python3 scripts/check_ccdcoe_p3_cultural_sources.py --self-test
python3 scripts/check_ccdcoe_p3_cultural_sources.py
python3 scripts/check_ccdcoe_p3_cognitive_warfare_discriminator.py --self-test
python3 scripts/check_ccdcoe_p3_cognitive_warfare_discriminator.py
python3 scripts/check_ccdcoe_p3_gcc1993_pre_response_baseline.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_pre_response_baseline.py
python3 scripts/check_ccdcoe_p3_gcc1993_chain.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_chain.py
python3 scripts/check_ccdcoe_p3_gcc1993_directional_control.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_directional_control.py
python3 scripts/check_ccdcoe_p3_gcc1993_claim_comparison.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_claim_comparison.py
python3 scripts/check_ccdcoe_p3_gcc1993_original_coding_receipts.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_claim_coding_protocol.py --self-test
python3 scripts/check_ccdcoe_p3_gcc1993_claim_coding_protocol.py
python3 scripts/check_critical_art_film_edition_intake.py --self-test
python3 scripts/check_critical_art_film_edition_intake.py
python3 scripts/check_critical_art_original_edition_authorities.py --self-test
python3 scripts/check_critical_art_original_edition_authorities.py
python3 scripts/measure_ccdcoe_p3_gcc_media.py --self-test
python3 scripts/measure_ccdcoe_p3_gcc_dual_coder.py --self-test
python3 scripts/build_ccdcoe_p3_primary_intake.py --self-test

# The repo's canonical Agda 2.9 parallel checker owns compiler resolution,
# cache, resource guards and exact-head kernel receipts. No direct nix call.
# Its nonzero exit remains fatal. The source --safe option on the generic
# graph owner is enforced by Agda when this target is checked.
test -f scripts/run_agda29_parallel_check.sh || {
  echo "Canonical parallel_checker wrapper is missing; kernel verification OPEN" >&2
  exit 2
}

bash scripts/run_agda29_parallel_check.sh \
  "${modules[@]}" \
  DASHI/Cognition/Everything.agda

echo "CCDCOE max-cut: canonical parallel_checker accepted all focused owners and cognition aggregate"

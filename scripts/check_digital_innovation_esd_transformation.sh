#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Education/DigitalInnovationESDSourceAtlas.agda
  DASHI/Education/DigitalInnovationESDTransformationExact.agda
  DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
  DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
  DASHI/Education/DigitalESDReciprocalBraidExact.agda
  DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
  DASHI/Education/DigitalInnovationESDRegression.agda
  DASHI/EverythingDigitalESDReciprocalBraid.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required digital-ESD source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^technologyUseCannotDetermineTransformativeESD :' DASHI/Education/DigitalInnovationESDTransformationExact.agda
grep -q '^learningGainCannotDetermineSystemResponseCapacity :' DASHI/Education/DigitalInnovationESDTransformationExact.agda
grep -q '^separateAgendasCannotAutoPromoteToIntegratedTransition :' DASHI/Education/DigitalInnovationESDTransformationExact.agda
grep -q '^canonicalTwinTransitionCoordinates :' DASHI/Education/DigitalInnovationESDTransformationExact.agda
grep -q '^canonicalDigitalInnovationESDSourceAtlas :' DASHI/Education/DigitalInnovationESDSourceAtlas.agda
grep -q '^editorialCallDoesNotSupplyEffectivenessEvidence :' DASHI/Education/DigitalInnovationESDSourceAtlas.agda
grep -q '^editorialCallCannotPromoteAgendaToConclusion :' DASHI/Education/DigitalInnovationESDSourceAtlas.agda
grep -q '^proceduralEthicsDoesNotPromoteEpistemicParticipation :' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q '^aiClassificationDoesNotPromoteStudentMeaning :' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q '^dataAvailabilityDoesNotPromoteContextPreservingReuse :' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q '^invitationDoesNotPromoteEvidence :' DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
grep -q '^genAIDoesNotPromoteAuthor :' DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
grep -q '^conflictedGuestEditorCannotHandleManuscript :' DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
grep -q '^genAICannotProduceSubstantiveReview :' DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
grep -q '^genAICannotMakeEditorialDecision :' DASHI/Education/MDPISpecialIssueResearchGovernanceExact.agda
grep -q '^coarseAgendaCannotDetermineReciprocalBraidAdequacy :' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q '^canonicalDigitalESDReciprocalBraid :' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q '^canonicalDirectionalObligations :' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q '^admitContextTransfer :' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q 'canonicalAliceBrownDiagnosisSchedulerBoundary' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q 'canonicalAliceBrownTemporalDiagnosisBoundary' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q 'canonicalAliceBrownSelectiveInvalidationParetoBoundary' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q 'canonicalAliceBrownRecursiveParetoBoundary' DASHI/Education/AliceBrownDigitalESDEpistemicGovernanceBridgeExact.agda
grep -q 'canonicalKimmererTransferResidualBoundary' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q 'Memory.revaluePreservesRememberedEvent' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q 'Learning.generalisationIsAutomaticIsFalse' DASHI/Education/DigitalESDReciprocalBraidExact.agda
grep -q 'Seven.canonicalSevenGenerationBNFBoundary' DASHI/Education/DigitalESDReciprocalBraidExact.agda

grep -q '^canonicalDigitalESDAcquisitionAtlas :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '^currentAcquisitionFrontier :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '^firstAcquisitionLeaf :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '^citationDoesNotPromoteDigitalESDConclusion :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '^teachingSustainabilityWithTechnologyDoesNotPromoteSustainabilityOfTechnology :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '^oneEducationLCADoesNotEstablishUniversalOnlineSuperiority :' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q 'canonicalSourceRoleSnowballReceipt' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '10.54675/ZACQ4808' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '10.3390/educsci13010033' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '10.1787/9997e7b3-en' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '10.1007/s11367-026-02656-7' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q '10.1186/s41239-025-00569-3' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q 'Global E-waste Monitor 2024' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
grep -q 'Energy and AI' DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda

grep -q '^reciprocalDirectionsRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^contextTransferAdmissionRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^institutionalNonErasureRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^scalabilityDesirabilityRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^sevenGenerationAuthorityRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^traumaGeneralisationRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^patternMindCandidateOnlyRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^duplicateSnapshotReceiptRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^snapshotSingleAuthorityRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^conflictedGuestEditorHandlingRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^reviewerGenAIRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^editorGenAIDecisionRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^substantiveGenAIDisclosureRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^humanAccountabilityRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^acquisitionAtlasRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^unescoTwinTransitionSameObjectRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^reviewAntecedentSameObjectRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^citationNonPromotionSnowballRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^energySourceScopeRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^ewasteSourceScopeRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^educationScenarioLCABenchmarkRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^digitalSobrietyPedagogyRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^reflexiveSustainabilityRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^singleLCAGeneralisationRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^lifecyclePaymentRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^currentAcquisitionFrontierRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^firstAcquisitionLeafRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^acquisitionOrderPaymentOrderRegression :' DASHI/Education/DigitalInnovationESDRegression.agda
grep -q '^unpaidDependencyReopensRegression :' DASHI/Education/DigitalInnovationESDRegression.agda

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh DASHI/Education/DigitalInnovationESDRegression.agda
elif command -v agda >/dev/null 2>&1; then
  agda -i . DASHI/Education/DigitalInnovationESDRegression.agda
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi

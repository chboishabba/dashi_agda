#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/FormalClaimTransportGeometryExact.agda
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda
  DASHI/Core/FormalizationRecoveryGeometryExact.agda
  DASHI/Core/DeductionIndexedInterpretationExact.agda
  DASHI/Core/FormalSystemRevisionGeometryExact.agda
  DASHI/Core/RulePremiseDependencyGeometryExact.agda
  DASHI/Core/OrderedSubstitutionGeometryExact.agda
  DASHI/Core/RulePremiseTypingGeometryExact.agda
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda
  DASHI/Foundations/Wette1969PrimaryTextExtractionExact.agda
  DASHI/Foundations/Wette1969HistoricalSignatureExact.agda
  DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
  DASHI/Foundations/Wette1969RuleRevisionExact.agda
  DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda
  DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
  DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
  DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
  DASHI/Foundations/Wette1969CompletenessInterpretationBridgeExact.agda
  DASHI/Foundations/Wette1970PrimaryTextExtractionExact.agda
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
  DASHI/Foundations/WetteArithmeticRepresentationExact.agda
  DASHI/Foundations/WetteConstructiveAutomatonExact.agda
  DASHI/Foundations/WetteArithmeticTransitionBridgeExact.agda
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda
  DASHI/Foundations/WetteRepresentationKernelBridgeExact.agda
  DASHI/Foundations/WetteCertifiedArithmeticKernelExact.agda
  DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
  DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
  DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda
  DASHI/Foundations/Wette/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required Wette reconstruction source is missing: $file" >&2
    exit 1
  fi
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'existenceOfRepresentationMapTransportsEveryClaimIsFalse' DASHI/Core/FormalClaimTransportGeometryExact.agda
grep -q 'comparisonAxesAreDefinitionallyTotallyOrderedIsFalse' DASHI/Core/FormalClaimTransportGeometryExact.agda
grep -q 'interpretationSpecificationIsAlreadyPointwiseProofCertificateIsFalse' DASHI/Core/DeductionIndexedInterpretationExact.agda
grep -q 'pointwiseProofFamilyIsDefinitionallyUniformInternalProofIsFalse' DASHI/Core/DeductionIndexedInterpretationExact.agda
grep -q 'historicalRevisionIsNotDefinitionallyDerivationalEquivalenceIsTrue' DASHI/Core/FormalSystemRevisionGeometryExact.agda
grep -q 'sourceRequiredOrderAlreadyProvesSemanticNonCommutationIsFalse' DASHI/Core/OrderedSubstitutionGeometryExact.agda
grep -q 'premiseKindsCanBeRecoveredBeforeBodiesIsTrue' DASHI/Core/RulePremiseTypingGeometryExact.agda
grep -q 'typedRequirementIsAlreadyExactPremiseBodyIsFalse' DASHI/Core/RulePremiseTypingGeometryExact.agda
grep -q 'allHistoricalRelatorAritiesHaveTypedConstructorsIsTrue' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
grep -q 'constructorLayerAddsSemanticTruthIsFalse' DASHI/Foundations/Wette1969JudgementConstructorsExact.agda
grep -q 'rule9324x25OrderRequirementRecoveredIsTrue' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'sourceOrderRequirementAlreadySuppliesHistoricalSubstitutionEvaluatorIsFalse' DASHI/Foundations/Wette1969SubstitutionOrderExact.agda
grep -q 'rule9324x25FourPremiseKindsRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'judgementKindRecoveryAlreadySuppliesExactFormulaArgumentsIsFalse' DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda
grep -q 'fourPremiseTemplateNowConstructibleIsTrue' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
grep -q 'freshTupleSharingAcrossPremises2To4RecoveredIsTrue' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
grep -q 'parameterizedTemplateIsAlreadyLiteralOCRPerfectTranscriptionIsFalse' DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda
grep -q 'doi:10.1007/978-3-642-86745-3_9' DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'doi:10.2307/2272630' DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'unverified1974DOIFabricatedIsFalse' DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda
grep -q 'historicalRuleSetFullyTranscribedIntoAgdaIsFalse' DASHI/Foundations/Wette1969PrimaryTextExtractionExact.agda
grep -q 'formulaRelatorArityEnforcedByTypeIsTrue' DASHI/Foundations/Wette1969HistoricalSignatureExact.agda
grep -q 'p193RevisionTranscribedIsTrue' DASHI/Foundations/Wette1969RuleRevisionExact.agda
grep -q 'firstRuleBodiesTranscribedIsTrue' DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda
grep -q 'sharedJudgementConstructorOwnerReusedIsTrue' DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda
grep -q 'premise18InductionRoleRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'premise27IndependenceRoleRecoveredIsTrue' DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda
grep -q 'hauptsatz2IsDefinitionallyFormulaOnlyTranslationIsFalse' DASHI/Foundations/Wette1969CompletenessInterpretationBridgeExact.agda
grep -q 'DOI: 10.1111/j.1746-8361.1970.tb01221.x' DASHI/Foundations/Wette1970PrimaryTextExtractionExact.agda
grep -q 'relativeCompletenessShouldBeDefinedBeforeSourceRecoveryIsFalse' DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda
grep -q 'partialHistoricalTranscriptionNowStartedIsTrue' DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
grep -q 'criticalSubstitutionOrderGeometryNowRecoveredIsTrue' DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
grep -q 'criticalPremiseTypingGeometryNowRecoveredIsTrue' DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda
grep -q 'historicalWetteCodecRecoveredIsFalse' DASHI/Foundations/WetteArithmeticRepresentationExact.agda
grep -q 'fractranMachineIsHistoricalWetteMachineIsFalse' DASHI/Foundations/WetteFRACTRANCrossPollinationExact.agda
grep -q 'ordinaryArithmeticInconsistencyEstablishedIsFalse' DASHI/Foundations/WetteBernaysConsistencyDeductionBoundaryExact.agda
grep -q 'machineReachabilityIsAlreadyMetatheoreticContradictionIsFalse' DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda
grep -q 'translatedContradictionProofIsAlreadySemanticAbsurdityIsFalse' DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda
grep -q 'theoremProvesOrdinaryArithmeticConsistencyIsFalse' DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda
grep -q 'historicalWetteToOrdinaryArithmeticTranslationRecoveredIsFalse' DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda
grep -q 'contradictionInOrdinaryArithmeticProvedIsFalse' DASHI/Foundations/WetteConsistencyClaimBoundaryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/FormalClaimTransportGeometryExact.agda \
  DASHI/Core/FormalizationRecoverySourceRegistryExact.agda \
  DASHI/Core/FormalizationRecoveryGeometryExact.agda \
  DASHI/Core/DeductionIndexedInterpretationExact.agda \
  DASHI/Core/FormalSystemRevisionGeometryExact.agda \
  DASHI/Core/RulePremiseDependencyGeometryExact.agda \
  DASHI/Core/OrderedSubstitutionGeometryExact.agda \
  DASHI/Core/RulePremiseTypingGeometryExact.agda \
  DASHI/Foundations/WetteHistoricalSourceAtlasExact.agda \
  DASHI/Foundations/WettePrimaryTextAcquisitionPlanExact.agda \
  DASHI/Foundations/Wette1969PrimaryTextExtractionExact.agda \
  DASHI/Foundations/Wette1969HistoricalSignatureExact.agda \
  DASHI/Foundations/Wette1969JudgementConstructorsExact.agda \
  DASHI/Foundations/Wette1969RuleRevisionExact.agda \
  DASHI/Foundations/Wette1969InitialRuleTranscriptionExact.agda \
  DASHI/Foundations/Wette1969CriticalRuleDependencyExact.agda \
  DASHI/Foundations/Wette1969SubstitutionOrderExact.agda \
  DASHI/Foundations/Wette1969CriticalPremiseTypingExact.agda \
  DASHI/Foundations/Wette1969Rule9324x25PremiseTemplateExact.agda \
  DASHI/Foundations/Wette1969CompletenessInterpretationBridgeExact.agda \
  DASHI/Foundations/Wette1970PrimaryTextExtractionExact.agda \
  DASHI/Foundations/WetteHistoricalRecoveryFrontierExact.agda \
  DASHI/Foundations/WetteHistoricalRecoveryGeometryBridgeExact.agda \
  DASHI/Foundations/WetteFiniteDeductionTraceExact.agda \
  DASHI/Foundations/WetteFiniteDerivationCompositionExact.agda \
  DASHI/Foundations/WetteFiniteCalculusTranslationExact.agda \
  DASHI/Foundations/WetteFormalClaimTransportBridgeExact.agda \
  DASHI/Foundations/WetteFiniteDerivabilityBernaysBridgeExact.agda \
  DASHI/Foundations/WetteTranslatedBernaysObstructionExact.agda \
  DASHI/Foundations/WetteFiniteTraceConsistencyObstructionExact.agda \
  DASHI/Foundations/Wette/Everything.agda

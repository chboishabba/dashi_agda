#!/usr/bin/env bash
set -euo pipefail

ROOT="DASHI/Math2026ClaimAuditValidation.agda"
FILES=(
  DASHI/Analysis/DeBruijnNewman2026ClaimAuditExact.agda
  DASHI/Analysis/DeBruijnNewman2026SourceWeldExact.agda
  DASHI/Analysis/DeBruijnNewmanRiemannG2BridgeAuditExact.agda
  DASHI/Analysis/DeBruijnNewmanRiemannG2RiemannSiegelBridgeExact.agda
  DASHI/Analysis/RiemannG2ExplicitFormulaBridgeAuditExact.agda
  DASHI/Analysis/RiemannG2LiteralSpectralZeroWeldExact.agda
  DASHI/Analysis/RiemannG2BidiCutReconciliationExact.agda
  DASHI/Analysis/RiemannG2C3MonsterEquivarianceAuditExact.agda
  DASHI/Analysis/RiemannG2DeterminantConsumerQuotient369Exact.agda
  DASHI/Analysis/RiemannG2PostSchurDeterminantSufficiency369Exact.agda
  DASHI/Analysis/RiemannG2DeterminantSymmetryRelevance369Exact.agda
  DASHI/Analysis/RiemannG2C3FixedNuisanceDeterminantNoGo369Exact.agda
  DASHI/Analysis/RiemannG2C3SimultaneousDeterminantCovariance369Exact.agda
  DASHI/Analysis/RiemannG2CommonC3DeterminantCovarianceCompilerExact.agda
  DASHI/Analysis/RiemannG2LiteralC3CovarianceSourceGateExact.agda
  DASHI/Analysis/RiemannG2C3ToScalarRouteCutExact.agda
  DASHI/Analysis/RiemannG2TargetCenteredScalarCancellationAssemblyExact.agda
  DASHI/Analysis/RiemannG2ExistingScalarHarmonicSameObjectAttachmentExact.agda
  DASHI/Analysis/RiemannG2ExistingScalarDonorInventoryExact.agda
  DASHI/Analysis/RiemannG2HighestAlphaAfter369Exact.agda
  DASHI/Analysis/RiemannG2PostScalarBalanceBreakingBidiExact.agda
  DASHI/Analysis/RiemannG2ScalarDonorToPostBalanceBidiExact.agda
  DASHI/Analysis/RiemannG2NarrowWindowNoCancellationReturnExact.agda
  DASHI/Analysis/RiemannG2CutoffGrowthBidiExact.agda
  DASHI/Analysis/RiemannG2ScalarDonorRegimeReconciliationExact.agda
  DASHI/Analysis/RiemannG2QuarterPeriodScalingPropagationExact.agda
  DASHI/Analysis/RiemannG2CutoffComplementCoordinateSeparationExact.agda
  DASHI/Analysis/RiemannG2QuarterPeriodPoleQuotientFinalCompilerExact.agda
  DASHI/Analysis/RiemannG2PoleQuotientProducerReconciliation8889Exact.agda
  DASHI/Analysis/RiemannG2QuarterPeriodAnalyticRouteReconciliationExact.agda
  DASHI/Analysis/RiemannG2GammaPrecisionLossLocalizationExact.agda
  DASHI/Analysis/RiemannG2CanonicalCharacterHighestAlphaReconciliationExact.agda
  DASHI/Analysis/RiemannG2ConstructedComplexAnalyticCarrierAdapterExact.agda
  DASHI/Analysis/RiemannG2CanonicalTestModulationHighestAlphaExact.agda
  DASHI/Analysis/RiemannG2CanonicalTestModulationProducerInventoryExact.agda
  DASHI/Analysis/RiemannG2MellinTestActionTransportExact.agda
  DASHI/Analysis/RiemannG2GammaMellinImplementationRecoveryExact.agda
  DASHI/Analysis/RiemannG2CanonicalTestModulationProofRelevantExact.agda
  DASHI/Analysis/RiemannG2GammaMellinProofRelevantActionCompilerExact.agda
  DASHI/Analysis/RiemannG2SourceNativePhiHatModulationAdapterExact.agda
  DASHI/Analysis/RiemannG2HAConsumerQuotientActiveSearchExact.agda
  DASHI/Analysis/RiemannG2HARecoveryDependencyFrontierExact.agda
  DASHI/Analysis/RiemannG2HAAdmissibleSearchRankingExact.agda
  DASHI/Analysis/RiemannG2HAProofCarryingRecoveryTraceExact.agda
  DASHI/Analysis/RiemannG2HAConsumerFanoutPriorityExact.agda
  DASHI/Analysis/RiemannG2HAConsumerWeightedRecoveryTraceExact.agda
  DASHI/Analysis/RiemannG2HASourceProducerHyperedgeExact.agda
  DASHI/Analysis/RiemannG2HASingleSourceProducerBidiExact.agda
  DASHI/Analysis/RiemannG2HASingleProducerLegacyHACompilerExact.agda
  DASHI/Analysis/RiemannG2CanonicalHAToHMFactorizationExact.agda
  DASHI/Mathematics/NumberTheory/PrimeGap2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/PrimeGap2026SourceAcquisitionExact.agda
  DASHI/Mathematics/NumberTheory/DiophantineTupleDPrimeSquare2026ClaimAuditExact.agda
  DASHI/Mathematics/NumberTheory/PrimePowerDiophantineTuple2026SourceExact.agda
  DASHI/Core/ExternalAutoformalizationProvenanceExact.agda
  DASHI/Core/SourceExactFrontierBidiCrossPollination2026.agda
  DASHI/Core/FrontierRelationStrengthBidiExact.agda
  DASHI/Core/FiniteCertificateConsumerBridgeExact.agda
  DASHI/Core/ThreeChannelC3EquivarianceGateExact.agda
  DASHI/Core/ConsumerRelativeSymmetryRelevanceExact.agda
  DASHI/Core/Clay369ResidualSufficiencyDichotomyExact.agda
  DASHI/Core/ClayMonster369CrossPollination2026Exact.agda
  DASHI/Physics/YangMills/BalabanActiveSourceDiscriminator2026Exact.agda
  DASHI/Physics/YangMills/BalabanC3MonsterEquivarianceAuditExact.agda
  DASHI/Physics/YangMills/BalabanSourceResidualConsumerNonDescent369Exact.agda
  DASHI/Physics/Closure/NSCriticalConeAristotleRouteHypergraph2026Exact.agda
  DASHI/Physics/Closure/NSCriticalConeResidualFibre369CrossPollinationExact.agda
  "$ROOT"
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required Math2026 source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh "$ROOT"

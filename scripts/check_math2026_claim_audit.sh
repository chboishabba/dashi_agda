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

if grep -nE '\b(postulate|{-# OPTIONS --allow-unsolved-metas #-}|\?|{!!})\b' "${FILES[@]}"; then
  echo "unsafe or incomplete proof surface found" >&2
  exit 1
fi

if command -v agda >/dev/null 2>&1; then
  agda -i . "$ROOT"
else
  echo "agda not available; trust scan only"
fi

module DASHI.Governance.GovernanceObservationCompressionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Governance.FutureSafeCausalCompressionExact as Compression
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.ContestableCompressionResidualExact as Residual
import DASHI.Governance.OpenWorldDisconfirmationBoundaryExact as OpenWorld
import DASHI.Governance.CounterpositionDiversityAutonomyExact as Counter
import DASHI.Governance.InterventionFeasibilityCutsetExact as Feasibility
import DASHI.Governance.FiniteCausalQueryRefinementStabilizationExact as Refinement
import DASHI.Governance.ProxyObjectiveFutureSafetyExact as Proxy

------------------------------------------------------------------------
-- Focused local-kernel regression root.
--
-- Suggested local command:
--   agda -i . DASHI/Governance/GovernanceObservationCompressionRegression.agda
------------------------------------------------------------------------

compressionIsNotAutomaticallyReification :
  Compression.FutureSafeCausalCompressionBoundary.everyCompressionIsReificationLoss
    Compression.canonicalFutureSafeCausalCompressionBoundary
  ≡ false
compressionIsNotAutomaticallyReification = refl

querySafetyIsObservationRelative :
  Compression.FutureSafeCausalCompressionBoundary.futureSafetyIsRelativeToActionObservationLanguage
    Compression.canonicalFutureSafeCausalCompressionBoundary
  ≡ true
querySafetyIsObservationRelative = refl

asymmetricLegibilityDoesNotPromoteAbuse :
  Legibility.AsymmetricLegibilityBoundary.asymmetryAloneProvesAbuse
    Legibility.canonicalAsymmetricLegibilityBoundary
  ≡ false
asymmetricLegibilityDoesNotPromoteAbuse = refl

finiteLegibilityGapBlocksExactRecovery :
  Legibility.ExactInstitutionalViewDecoder Legibility.finiteLegibilityChannel →
  Data.Empty.⊥
finiteLegibilityGapBlocksExactRecovery =
  Legibility.finiteExactDecoderImpossible
  where
    open import Data.Empty

exactResidualRestoresRepresentativeIdentity :
  Residual.ContestableCompressionReceipt.exactResidualRestoresRepresentativeIdentity
    Residual.canonicalExactContestabilityReceipt
  ≡ true
exactResidualRestoresRepresentativeIdentity = refl

absenceDoesNotBecomeContradiction :
  OpenWorld.OpenWorldDisconfirmationBoundary.absenceEqualsContradiction
    OpenWorld.canonicalOpenWorldDisconfirmationBoundary
  ≡ false
absenceDoesNotBecomeContradiction = refl

concealmentNeedsSeparateEvidence :
  OpenWorld.OpenWorldDisconfirmationBoundary.concealmentNeedsOwnEvidence
    OpenWorld.canonicalOpenWorldDisconfirmationBoundary
  ≡ true
concealmentNeedsSeparateEvidence = refl

forcedBinaryDoesNotExhaustCounterpositions :
  Counter.CounterpositionDiversityBoundary.forcedBinaryChoiceExhaustsCounterpositionSpace
    Counter.canonicalCounterpositionDiversityBoundary
  ≡ false
forcedBinaryDoesNotExhaustCounterpositions = refl

nonBinaryAlternativeExistsInFoundation :
  Counter.NonBinaryAlternativeAccess Counter.foundationCounterpositionSystem
nonBinaryAlternativeExistsInFoundation = Counter.foundationNonBinaryAccess

outcomeNeedsSeparateFeasibilityLaw :
  Feasibility.InterventionFeasibilityCutsetBoundary.desiredOutcomeNeedsSeparateLaw
    Feasibility.canonicalInterventionFeasibilityCutsetBoundary
  ≡ true
outcomeNeedsSeparateFeasibilityLaw = refl

boundedRefinementStabilizes :
  Refinement.FiniteCausalQueryRefinementBoundary.boundedStrictRefinementEventuallyStabilizes
    Refinement.canonicalFiniteCausalQueryRefinementBoundary
  ≡ true
boundedRefinementStabilizes = refl

proxyEqualityDoesNotGuaranteeFutureWelfare :
  Proxy.ProxyFutureSafetyBoundary.presentProxyEqualityImpliesFutureWelfareEquality
    Proxy.canonicalProxyFutureSafetyBoundary
  ≡ false
proxyEqualityDoesNotGuaranteeFutureWelfare = refl

proxyDefectCanRefuteSufficiency :
  Proxy.ProxyFutureSafetyBoundary.separatingDefectCanRefuteSufficiency
    Proxy.canonicalProxyFutureSafetyBoundary
  ≡ true
proxyDefectCanRefuteSufficiency = refl

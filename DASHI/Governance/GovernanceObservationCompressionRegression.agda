module DASHI.Governance.GovernanceObservationCompressionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
open import Data.Empty using (⊥)

import DASHI.Core.ObservationLanguageRefinementExact as Observation
import DASHI.Governance.FutureSafeCausalCompressionExact as Compression
import DASHI.Governance.ObservationRelativeReificationRegressionExact as Reification
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.ReciprocalLegibilityRefinementExact as Reciprocal
import DASHI.Governance.ContestabilityObservationRefinementExact as ContestObservation
import DASHI.Governance.ContestabilityAccessCostExact as AccessCost
import DASHI.Governance.ContestableCompressionResidualExact as Residual
import DASHI.Governance.OpenWorldDisconfirmationBoundaryExact as OpenWorld
import DASHI.Governance.CounterpositionDiversityAutonomyExact as Counter
import DASHI.Governance.EpistemicBinaryForcingLossExact as Binary
import DASHI.Governance.EpistemicTritBalancedTernarySeparationExact as TernarySeparation
import DASHI.Governance.CompositionalEvidenceEnclosureExact as Evidence
import DASHI.Governance.InterventionFeasibilityCutsetExact as Feasibility
import DASHI.Governance.FiniteCausalQueryRefinementStabilizationExact as Refinement
import DASHI.Governance.ProxyObjectiveFutureSafetyExact as Proxy

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

sameCompressionCannotBeSafeForSeparatingQuery :
  Compression.QuerySafeCompression
    Reification.fineGraph
    Reification.coarseGraph
    Reification.compression
    Reification.richLanguage
  → ⊥
sameCompressionCannotBeSafeForSeparatingQuery =
  Reification.richQuerySafetyImpossible

asymmetricLegibilityDoesNotPromoteAbuse :
  Legibility.AsymmetricLegibilityBoundary.asymmetryAloneProvesAbuse
    Legibility.canonicalAsymmetricLegibilityBoundary
  ≡ false
asymmetricLegibilityDoesNotPromoteAbuse = refl

finiteLegibilityGapBlocksExactRecovery :
  Legibility.ExactInstitutionalViewDecoder Legibility.finiteLegibilityChannel →
  ⊥
finiteLegibilityGapBlocksExactRecovery =
  Legibility.finiteExactDecoderImpossible

institutionOnlyRefinementBlocksExactRecovery :
  Legibility.ExactInstitutionalViewDecoder
    (Reciprocal.institutionOnlyChannel Reciprocal.finiteDirectionalRefinement) →
  ⊥
institutionOnlyRefinementBlocksExactRecovery =
  Reciprocal.finiteInstitutionOnlyDecoderImpossible

reciprocalFullViewRestoresExactDecoder :
  Legibility.ExactInstitutionalViewDecoder
    (Reciprocal.reciprocalFullViewChannel Reciprocal.finiteDirectionalRefinement)
reciprocalFullViewRestoresExactDecoder =
  Reciprocal.finiteReciprocalDecoderExists

finiteExplanationAddsStrictObservationRefinement :
  Observation.StrictObservationRefinement
    (ContestObservation.asObservationLanguage
      ContestObservation.finiteExplanationChannel)
finiteExplanationAddsStrictObservationRefinement =
  ContestObservation.finiteExplanationStrictlyRefines

formalContestabilityDoesNotGuaranteeAffordableAccess :
  AccessCost.AffordableContestability
    AccessCost.finiteCost AccessCost.finiteBudget → ⊥
formalContestabilityDoesNotGuaranteeAffordableAccess =
  AccessCost.formalAvailabilityDoesNotEstablishAffordability

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

unresolvedDoesNotAutomaticallyBecomeNeutralDigit :
  TernarySeparation.EpistemicTernarySeparationBoundary.unresolvedDefinitionallyEqualsNeutralDigit
    TernarySeparation.canonicalEpistemicTernarySeparationBoundary
  ≡ false
unresolvedDoesNotAutomaticallyBecomeNeutralDigit = refl

forcedBinaryDoesNotExhaustCounterpositions :
  Counter.CounterpositionDiversityBoundary.forcedBinaryChoiceExhaustsCounterpositionSpace
    Counter.canonicalCounterpositionDiversityBoundary
  ≡ false
forcedBinaryDoesNotExhaustCounterpositions = refl

nonBinaryAlternativeExistsInFoundation :
  Counter.NonBinaryAlternativeAccess Counter.foundationCounterpositionSystem
nonBinaryAlternativeExistsInFoundation = Counter.foundationNonBinaryAccess

acceptBinaryCannotReconstructEpistemicState :
  Binary.AcceptForcingInjective → ⊥
acceptBinaryCannotReconstructEpistemicState = Binary.acceptForcingIsNotInjective

rejectBinaryCannotReconstructEpistemicState :
  Binary.RejectForcingInjective → ⊥
rejectBinaryCannotReconstructEpistemicState = Binary.rejectForcingIsNotInjective

composedEvidenceLowerBoundIsDerived : Evidence.lower Evidence.fiveBox ≡ 3
composedEvidenceLowerBoundIsDerived = Evidence.fiveBoxLowerIsThree

composedEvidenceUpperBoundIsDerived : Evidence.upper Evidence.fiveBox ≡ 7
composedEvidenceUpperBoundIsDerived = Evidence.fiveBoxUpperIsSeven

targetEvidenceReceiptIsNotRequired :
  Evidence.EvidenceEnclosureBoundary.localBoundsCanComposeWithoutTargetReceipt
    Evidence.canonicalEvidenceEnclosureBoundary
  ≡ true
targetEvidenceReceiptIsNotRequired = refl

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

finiteProxyCannotServeAsFutureWelfareQuotient :
  Proxy.ProxySufficientForFutureWelfare Proxy.finiteProxyWelfareSystem → ⊥
finiteProxyCannotServeAsFutureWelfareQuotient =
  Proxy.finiteProxyIsNotFutureWelfareSufficient

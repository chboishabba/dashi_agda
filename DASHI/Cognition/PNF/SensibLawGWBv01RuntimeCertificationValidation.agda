module DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawGWBv01RuntimeCertificationExact as Receipt
import DASHI.Cognition.PNF.SensibLawGWBv01PostCertificationRoadmapExact as Roadmap
import DASHI.Cognition.PNF.SensibLawRuntimeNumericProjectionBoundaryExact as Numeric
import DASHI.Cognition.PNF.SensibLawSemanticExpansionSoftwareValidationExact as Expansion
import DASHI.Cognition.PNF.SensibLawExpandedCertificationTelemetryBoundaryExact as ExpandedRun
import DASHI.Cognition.PNF.SensibLawGWBv01ExpandedSemanticCertificationV02Exact as ExpandedV02
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Focused validation root for the current SensibLaw runtime state.
------------------------------------------------------------------------

parityFailureCountIsZero :
  Receipt.parityFailed Receipt.gwbV01Parity ≡ zero
parityFailureCountIsZero = refl

parityCoversAllGwbSentences :
  Receipt.parityChecked Receipt.gwbV01Parity
  ≡ Receipt.sentenceCount Receipt.gwbV01Corpus
parityCoversAllGwbSentences = refl

publicationCountIsZero :
  Receipt.publishedGenerations Receipt.gwbV01CertifiedRun ≡ zero
publicationCountIsZero = refl

fullGateIsRecordedPassed :
  Receipt.fullGatePassed Receipt.gwbV01CertifiedRun ≡ true
fullGateIsRecordedPassed = refl

measuredTierIsOnePointTwo :
  Receipt.measuredTier Receipt.gwbV01Timing ≡ Receipt.production1_2x
measuredTierIsOnePointTwo = refl

currentFrontierAwaitsCutoverDecision :
  Roadmap.currentStage Roadmap.currentSensibLawPostGWBFrontier
  ≡ Roadmap.productionCutoverDecision
currentFrontierAwaitsCutoverDecision = refl

universalCutoverStillFalse :
  Roadmap.productionCutoverUniversallyAuthorized
    Roadmap.currentSensibLawPostGWBFrontier
  ≡ false
universalCutoverStillFalse = refl

numericGateProjectionRetainsPass :
  Numeric.gatePassed Numeric.gwbV01PerformanceProjection ≡ true
numericGateProjectionRetainsPass = refl

numericTierProjectionRetainsOnePointTwo :
  Numeric.tier Numeric.gwbV01PerformanceProjection ≡ Receipt.production1_2x
numericTierProjectionRetainsOnePointTwo = refl

numericProjectionCannotRecoverFineTiming :
  INF.FactorsThrough Numeric.projection Numeric.activeWorkClass → ⊥
numericProjectionCannotRecoverFineTiming =
  Numeric.performanceProjectionCannotRecoverFineTiming

semanticExpansionWorkspaceValidationPassed :
  Expansion.workspaceTestsPassed Expansion.semanticExpansionSoftwareValidation ≡ true
semanticExpansionWorkspaceValidationPassed = refl

semanticExpansionCandidateOnlyContractPassed :
  Expansion.candidateOnlyContractChecked Expansion.semanticExpansionSoftwareValidation ≡ true
semanticExpansionCandidateOnlyContractPassed = refl

semanticExpansionNoPublicationApiContractPassed :
  Expansion.noPublicationApiChecked Expansion.semanticExpansionSoftwareValidation ≡ true
semanticExpansionNoPublicationApiContractPassed = refl

semanticExpansionSoftwareFrontierWasAwaitingRuntimeCertification :
  Expansion.currentSemanticExpansionFrontier
  ≡ Expansion.softwareValidatedAwaitingExpandedParityPerformance
semanticExpansionSoftwareFrontierWasAwaitingRuntimeCertification = refl

------------------------------------------------------------------------
-- Historical failed raw-hash attempt remains visible.
------------------------------------------------------------------------

expandedParityRunCoversAllSentences :
  ExpandedRun.parityChecked ExpandedRun.expandedRun0833
  ≡ ExpandedRun.sentences ExpandedRun.expandedRun0833
expandedParityRunCoversAllSentences = refl

expandedParityRunHasZeroFailures :
  ExpandedRun.parityFailed ExpandedRun.expandedRun0833 ≡ zero
expandedParityRunHasZeroFailures = refl

runtimeTelemetryIsExcludedFromSemanticObservation :
  ExpandedRun.semanticObservationFrame ExpandedRun.runtimeTimingTelemetryFrame ≡ false
runtimeTelemetryIsExcludedFromSemanticObservation = refl

historicalExpandedFrontierWasAwaitingCanonicalDigestRerun :
  ExpandedRun.currentExpandedCertificationFrontier
  ≡ ExpandedRun.semanticParityAndPerformanceObservedAwaitingCanonicalDigestRerun
historicalExpandedFrontierWasAwaitingCanonicalDigestRerun = refl

------------------------------------------------------------------------
-- Successful corrected v0.2 expanded-semantic certification.
------------------------------------------------------------------------

expandedV02ParityCoversAllSentences :
  ExpandedV02.parityChecked ExpandedV02.expandedSurfaceV02
  ≡ ExpandedV02.sentences ExpandedV02.expandedSurfaceV02
expandedV02ParityCoversAllSentences = refl

expandedV02ParityFailuresZero :
  ExpandedV02.parityFailed ExpandedV02.expandedSurfaceV02 ≡ zero
expandedV02ParityFailuresZero = refl

expandedV02ProjectionFailuresZero :
  ExpandedV02.projectionFailures ExpandedV02.expandedSurfaceV02 ≡ zero
expandedV02ProjectionFailuresZero = refl

expandedV02PublicationEffectsZero :
  ExpandedV02.publicationEffects ExpandedV02.expandedSurfaceV02 ≡ zero
expandedV02PublicationEffectsZero = refl

expandedV02CanonicalDigestMatched :
  ExpandedV02.parityAndDirectDigestsMatched ExpandedV02.canonicalObservationV02 ≡ true
expandedV02CanonicalDigestMatched = refl

expandedV02FullGatePassed :
  ExpandedV02.fullExpandedGatePassed ExpandedV02.expandedGWBv02CertifiedRun ≡ true
expandedV02FullGatePassed = refl

expandedV02CurrentFrontier :
  ExpandedV02.currentExpandedSemanticCertificationFrontier
  ≡ ExpandedV02.boundedExpandedGWBv02CertifiedAwaitingAdmissionAndMultiCorpus
expandedV02CurrentFrontier = refl

------------------------------------------------------------------------
-- New legal semantic adequacy / admission frontier.
------------------------------------------------------------------------

legalGoldCoveredFixtureCountIsTen :
  Admission.coveredFixtureCount Admission.legalSemanticGoldV01 ≡ 10
legalGoldCoveredFixtureCountIsTen = refl

legalGoldProducerGapCountIsSix :
  Admission.producerGapCount Admission.legalSemanticGoldV01 ≡ 6
legalGoldProducerGapCountIsSix = refl

parserCandidateStillCannotAuthorizeAdmission :
  Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
parserCandidateStillCannotAuthorizeAdmission =
  Admission.parserCandidateAloneCannotAuthorizeAdmission

residualFrequencyStillNotSemanticQuality :
  Admission.ResidualFrequencyIsSemanticQuality → ⊥
residualFrequencyStillNotSemanticQuality =
  Admission.residualFrequencyIsNotSemanticQuality

legalAdmissionFrontierAwaitsRuntimeReceipt :
  Admission.currentLegalSemanticAdmissionFrontier
  ≡ Admission.implementationAwaitingCompileGoldAndResidualReceipt
legalAdmissionFrontierAwaitsRuntimeReceipt = refl

module DASHI.Reasoning.RelationRepresentationRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as Phase
import DASHI.Biology.NeuralRepresentationLaplacianExact as Neural
import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Biology.HumourOnlineEngagementFramework as Humour
import DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge as HumourAgency
import DASHI.Reasoning.RelationRepresentationSourceRegistryExact as Sources
import DASHI.Reasoning.RelationRepresentationStudyValidationObligationsExact as Validation
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization
import DASHI.Reasoning.BidirectionalRelationRepresentationBridgeExact as Bidi
import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Protocol
import DASHI.Reasoning.FiniteRelationLinearAlgebraProducerExact as Producer
import DASHI.Reasoning.FiniteRelationSVDJacobianProducerExact as SVD
import DASHI.Reasoning.EigenslurFlourishingRelationBoundaryExact as Domain
import DASHI.Reasoning.RelationRepresentationCrossPollinationExact as Cross
import DASHI.Reasoning.HumourRelationRepresentationCrossPollinationExact as HumourCross
import DASHI.Reasoning.NeuralSpectralRelationCrossPollinationExact as NeuralCross

------------------------------------------------------------------------
-- Focused regression: keep the exact seams live in one typecheck target.
------------------------------------------------------------------------

sourceBoundary : Sources.RelationRepresentationAttributionBoundary
sourceBoundary = Sources.canonicalRelationRepresentationAttributionBoundary

studyValidationBoundary : Validation.StudyValidationBoundary
studyValidationBoundary = Validation.canonicalStudyValidationBoundary

adequacyBoundary : Adequacy.RelationRepresentationAdequacyBoundary
adequacyBoundary = Adequacy.canonicalRelationRepresentationAdequacyBoundary

realizationBoundary : Realization.RelationRepresentationRealizationBoundary
realizationBoundary = Realization.canonicalRelationRepresentationRealizationBoundary

bidirectionalBoundary : Bidi.BidirectionalRelationBridgeBoundary
bidirectionalBoundary = Bidi.canonicalBidirectionalRelationBridgeBoundary

protocolBoundary : Protocol.RelationExperimentProtocolBoundary
protocolBoundary = Protocol.canonicalRelationExperimentProtocolBoundary

producerBoundary : Producer.FiniteRelationProducerBoundary
producerBoundary = Producer.canonicalFiniteRelationProducerBoundary

svdJacobianBoundary : SVD.SVDJacobianProducerBoundary
svdJacobianBoundary = SVD.canonicalSVDJacobianProducerBoundary

domainBoundary : Domain.EigenslurFlourishingBoundary
domainBoundary = Domain.canonicalEigenslurFlourishingBoundary

humourBoundary : HumourCross.HumourRelationRepresentationBoundary
humourBoundary = HumourCross.canonicalHumourRelationRepresentationBoundary

neuralBoundary : NeuralCross.NeuralSpectralRelationBoundary
neuralBoundary = NeuralCross.canonicalNeuralSpectralRelationBoundary

------------------------------------------------------------------------
-- External-study validation readiness remains fail-closed.
------------------------------------------------------------------------

relationDecoderPayloadStillAbsent :
  Validation.relationDecoderRawPayloadPresent
    Validation.currentExternalStudyPayloadAvailability ≡ false
relationDecoderPayloadStillAbsent = refl

risePayloadStillAbsent :
  Validation.riseRawPayloadPresent
    Validation.currentExternalStudyPayloadAvailability ≡ false
risePayloadStillAbsent = refl

recosPayloadStillAbsent :
  Validation.recosRawPayloadPresent
    Validation.currentExternalStudyPayloadAvailability ≡ false
recosPayloadStillAbsent = refl

manifoldPayloadStillAbsent :
  Validation.manifoldSteeringRawPayloadPresent
    Validation.currentExternalStudyPayloadAvailability ≡ false
manifoldPayloadStillAbsent = refl

externalRawPayloadCouldPopulateProducerInterfaces :
  Validation.exactRawPayloadCouldPopulateProducerInterfaces
    Validation.canonicalStudyValidationBoundary ≡ true
externalRawPayloadCouldPopulateProducerInterfaces = refl

------------------------------------------------------------------------
-- Exact finite producer receipts.
------------------------------------------------------------------------

principalEigenpairReceipt :
  Producer.matVec Producer.sampleGram Producer.principalAxis
  ≡ Producer.scaleVec 9 Producer.principalAxis
principalEigenpairReceipt =
  Producer.eigenEquation Producer.principalEigenpair

secondaryEigenpairReceipt :
  Producer.matVec Producer.sampleGram Producer.secondaryAxis
  ≡ Producer.scaleVec 1 Producer.secondaryAxis
secondaryEigenpairReceipt =
  Producer.eigenEquation Producer.secondaryEigenpair

finiteSpectralGapIsEight : Producer.spectralGapCode ≡ 8
finiteSpectralGapIsEight = Producer.spectralGapCodeIsEight

rankOneOuterProductStillExact :
  Producer.outer Producer.rankOneLeft Producer.rankOneRight
  ≡ Producer.rankOneMatrix
rankOneOuterProductStillExact = Producer.rankOneOuterProductReceipt

quarterTurnStillOrderFour :
  (p : Producer.AxisPhase4) →
  Producer.quarterTurn
    (Producer.quarterTurn
      (Producer.quarterTurn
        (Producer.quarterTurn p))) ≡ p
quarterTurnStillOrderFour = Producer.quarterTurnFourth

affineProducerStillExact :
  Producer.affineDemo (Producer.vec2 2 3) ≡ Producer.vec2 5 11
affineProducerStillExact = Producer.affineDemoAt23

finiteDifferenceSensitivityIsStateDependent :
  Producer.forwardDifference Producer.squareMap 2
  ≡ Producer.forwardDifference Producer.squareMap 3 → ⊥
finiteDifferenceSensitivityIsStateDependent =
  Producer.localSensitivityChangesWithState

------------------------------------------------------------------------
-- Literal tiny SVD receipts: X = U Sigma V^T for X = diag(3,1), with the
-- singular action equations and squared-scale/Gram relation kept exact.
------------------------------------------------------------------------

principalSVDReceipt :
  Producer.matVec SVD.sampleDataMatrix Producer.principalAxis
  ≡ Producer.scaleVec 3 Producer.principalAxis
principalSVDReceipt = SVD.principalSVDActionReceipt

secondarySVDReceipt :
  Producer.matVec SVD.sampleDataMatrix Producer.secondaryAxis
  ≡ Producer.scaleVec 1 Producer.secondaryAxis
secondarySVDReceipt = SVD.secondarySVDActionReceipt

principalSingularSquareIsNine :
  SVD.singularScale1 SVD.canonicalSampleSVD
  * SVD.singularScale1 SVD.canonicalSampleSVD ≡ 9
principalSingularSquareIsNine =
  SVD.principalSingularScaleSquaresToGramEigenvalue

secondarySingularSquareIsOne :
  SVD.singularScale2 SVD.canonicalSampleSVD
  * SVD.singularScale2 SVD.canonicalSampleSVD ≡ 1
secondarySingularSquareIsOne =
  SVD.secondarySingularScaleSquaresToGramEigenvalue

jacobianStillRequiresDifferentiableCarrier :
  SVD.derivativeExistenceReceiptSupplied SVD.emptyJacobianProducerObligation ≡ false
jacobianStillRequiresDifferentiableCarrier = refl

externalFixtureDoesNotClaimEmpiricalEmbeddings :
  SVD.empiricalEmbeddingsLoaded SVD.canonicalExternalNumericalReceiptContract ≡ false
externalFixtureDoesNotClaimEmpiricalEmbeddings = refl

------------------------------------------------------------------------
-- Existing phase/amplitude owner remains a concrete operator-coordinate
-- precedent: equal amplitude does not identify phase and equal phase does not
-- identify amplitude.
------------------------------------------------------------------------

samePhaseCanRetainDifferentAmplitude :
  Phase.phase Phase.samePhaseDifferentAmplitudeA
  ≡ Phase.phase Phase.samePhaseDifferentAmplitudeB
samePhaseCanRetainDifferentAmplitude = Phase.samePhaseWitness

equalPhaseDoesNotCollapseAmplitude :
  Phase.amplitude Phase.samePhaseDifferentAmplitudeA
  ≡ Phase.amplitude Phase.samePhaseDifferentAmplitudeB → ⊥
equalPhaseDoesNotCollapseAmplitude = Phase.differentAmplitudeWitness

sameAmplitudeCanRetainDifferentPhase :
  Phase.amplitude Phase.sameAmplitudeDifferentAmplitudeA
  ≡ Phase.amplitude Phase.sameAmplitudeDifferentAmplitudeB
sameAmplitudeCanRetainDifferentPhase = Phase.sameAmplitudeWitness

equalAmplitudeDoesNotCollapsePhase :
  Phase.phase Phase.sameAmplitudeDifferentPhaseA
  ≡ Phase.phase Phase.sameAmplitudeDifferentPhaseB → ⊥
equalAmplitudeDoesNotCollapsePhase = Phase.differentPhaseWitness

------------------------------------------------------------------------
-- Concrete negative regressions.
------------------------------------------------------------------------

propertyCodeNotPreciseRelation :
  Realization.RepresentationRealizationWitness
    Realization.propertyCode Realization.preciseRelation → ⊥
propertyCodeNotPreciseRelation =
  Realization.propertyCodeCannotRealizePreciseRelation

compactCodeNotSituatedMeaning :
  Realization.RepresentationRealizationWitness
    Realization.compactRelation Realization.situatedMeaning → ⊥
compactCodeNotSituatedMeaning =
  Realization.compactRelationCannotRealizeSituatedMeaning

positiveCodeNotAgency :
  Realization.RepresentationRealizationWitness
    Domain.coarsePositiveCode Domain.agencyStatus → ⊥
positiveCodeNotAgency = Domain.coarsePositiveCodeCannotRealizeAgency

------------------------------------------------------------------------
-- Alice Brown / humour source and dynamic consumer boundary.
------------------------------------------------------------------------

humourSourceStillPrecedesLaterCorrection :
  Humour.sourceFrameworkPreservedBeforeLaterCorrection
    Humour.canonicalHumourFrameworkSourceSurface
  ≡ true
humourSourceStillPrecedesLaterCorrection =
  HumourCross.humourSourceExplicitlyPreservedBeforeLaterCorrection

humourCurrentPositiveSurfaceDoesNotEstablishPluralFutureSafety :
  Plural.PluralDynamicSafety HumourAgency.humourProjectionFamily → ⊥
humourCurrentPositiveSurfaceDoesNotEstablishPluralFutureSafety =
  HumourCross.oneHumourConsumerSafetyDoesNotEstablishPluralSafety

------------------------------------------------------------------------
-- Neural / spectral representation stress test.
------------------------------------------------------------------------

sameCoarseNeuralObservationStillLosesRelationalVariation :
  Realization.RepresentationRealizationWitness
    Neural.fmriLikeObservation Neural.laplacianVariation → ⊥
sameCoarseNeuralObservationStillLosesRelationalVariation =
  NeuralCross.neuralCoarseObservationCannotRealizeVariation

neuralConsumerCollisionReopensCandidateSearch :
  Protocol.ReopenedCandidateSearch
    Neural.fmriLikeObservation Neural.laplacianVariation
neuralConsumerCollisionReopensCandidateSearch =
  NeuralCross.neuralSearchMayReopenFromOffsetToRotation

------------------------------------------------------------------------
-- Existing learning-future result stays wired through the capstone.
------------------------------------------------------------------------

grokkingCurrentFitStillNotLearningFuture :
  Future.FutureObservationEquivalent
    Grok.learningSystem
    Grok.generalizationVisible
    Grok.structuredBefore
    Grok.memorizerBefore
  → ⊥
grokkingCurrentFitStillNotLearningFuture =
  Cross.grokkingCurrentFitDoesNotCloseLearningFuture

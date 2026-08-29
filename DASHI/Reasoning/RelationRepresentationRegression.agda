module DASHI.Reasoning.RelationRepresentationRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as Phase
import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Biology.HumourEpistemicAgencyHyperfabricBridge as HumourAgency
import DASHI.Reasoning.RelationRepresentationSourceRegistryExact as Sources
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization
import DASHI.Reasoning.BidirectionalRelationRepresentationBridgeExact as Bidi
import DASHI.Reasoning.EigenslurFlourishingRelationBoundaryExact as Domain
import DASHI.Reasoning.RelationRepresentationCrossPollinationExact as Cross
import DASHI.Reasoning.HumourRelationRepresentationCrossPollinationExact as HumourCross

------------------------------------------------------------------------
-- Focused regression: keep the exact seams live in one typecheck target.
------------------------------------------------------------------------

sourceBoundary : Sources.RelationRepresentationAttributionBoundary
sourceBoundary = Sources.canonicalRelationRepresentationAttributionBoundary

adequacyBoundary : Adequacy.RelationRepresentationAdequacyBoundary
adequacyBoundary = Adequacy.canonicalRelationRepresentationAdequacyBoundary

realizationBoundary : Realization.RelationRepresentationRealizationBoundary
realizationBoundary = Realization.canonicalRelationRepresentationRealizationBoundary

bidirectionalBoundary : Bidi.BidirectionalRelationBridgeBoundary
bidirectionalBoundary = Bidi.canonicalBidirectionalRelationBridgeBoundary

domainBoundary : Domain.EigenslurFlourishingBoundary
domainBoundary = Domain.canonicalEigenslurFlourishingBoundary

humourBoundary : HumourCross.HumourRelationRepresentationBoundary
humourBoundary = HumourCross.canonicalHumourRelationRepresentationBoundary

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
  Phase.amplitude Phase.sameAmplitudeDifferentPhaseA
  ≡ Phase.amplitude Phase.sameAmplitudeDifferentPhaseB
sameAmplitudeCanRetainDifferentPhase = Phase.sameAmplitudeWitness

equalAmplitudeDoesNotCollapsePhase :
  Phase.phase Phase.sameAmplitudeDifferentPhaseA
  ≡ Phase.phase Phase.sameAmplitudeDifferentPhaseB → ⊥
equalAmplitudeDoesNotCollapsePhase = Phase.differentPhaseWitness

------------------------------------------------------------------------
-- New concrete negative regressions.
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

humourSourceStillPrecedesLaterCorrection =
  HumourCross.humourSourceExplicitlyPreservedBeforeLaterCorrection

humourCurrentPositiveSurfaceDoesNotEstablishPluralFutureSafety :
  Plural.PluralDynamicSafety HumourAgency.humourProjectionFamily → ⊥
humourCurrentPositiveSurfaceDoesNotEstablishPluralFutureSafety =
  HumourCross.oneHumourConsumerSafetyDoesNotEstablishPluralSafety

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

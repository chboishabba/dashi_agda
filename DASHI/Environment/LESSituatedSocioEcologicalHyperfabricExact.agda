module DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.PredictionEnvelopeExact as Prediction
import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as Kimmerer
import DASHI.Culture.ProvenancePreservingCulturalHyperfabric as Cultural
import DASHI.Governance.JusticeRequiredAxisEvidenceExact as JusticeEvidence
import DASHI.Governance.RecognitionDistributionRepresentationAxesExact as Fraser
import DASHI.Governance.RequiredAxisAuthorityRoutingExact as Authority
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing

------------------------------------------------------------------------
-- LES SITUATED SOCIO-ECOLOGICAL HYPERFABRIC CROSS-POLLINATION
--
-- This module composes existing, independently source-calibrated owners:
--
--   * Crenshaw-motivated intersectional non-factorability;
--   * Kimmerer / Two-Eyed Seeing provenance-preserving coordination;
--   * Fraser's redistribution / recognition / representation separation;
--   * provenance-preserving cultural hyperfabric;
--   * Stage-6 prediction envelopes over evidence fibres;
--   * required-axis authority routing.
--
-- The exact finite mathematics below is DASHI's.  It does not claim that any
-- cited source contains this construction, and it does not promote a finite
-- specimen into an empirical environmental, Indigenous, political or legal
-- model.
------------------------------------------------------------------------

-- A situated environmental planning point carries both a knowledge history and
-- a participation configuration.  The ecological observation below is
-- intentionally coarse: both knowledge histories converge on the same observed
-- environmental condition, while provenance and justice-relevant coordinates
-- remain independently available upstairs.

SituatedEnvironmentalState : Set
SituatedEnvironmentalState =
  Kimmerer.KnowledgeHistory × Fraser.ParticipationState

knowledgeHistory : SituatedEnvironmentalState → Kimmerer.KnowledgeHistory
knowledgeHistory = proj₁

participationState : SituatedEnvironmentalState → Fraser.ParticipationState
participationState = proj₂

coarseEcologicalObservation :
  SituatedEnvironmentalState → Kimmerer.SharedEcologicalObservation
coarseEcologicalObservation state =
  Kimmerer.observeKnowledgeHistory (knowledgeHistory state)

knowledgeProvenance : SituatedEnvironmentalState → Kimmerer.Provenance
knowledgeProvenance state = Kimmerer.provenance (knowledgeHistory state)

justiceDistribution : SituatedEnvironmentalState → Fraser.Distribution
justiceDistribution state = Fraser.distribution (participationState state)

justiceRecognition : SituatedEnvironmentalState → Fraser.Recognition
justiceRecognition state = Fraser.recognition (participationState state)

justiceRepresentation : SituatedEnvironmentalState → Fraser.Representation
justiceRepresentation state = Fraser.representation (participationState state)

JusticeCoordinate : Set
JusticeCoordinate =
  Fraser.Distribution × (Fraser.Recognition × Fraser.Representation)

justiceCoordinate : SituatedEnvironmentalState → JusticeCoordinate
justiceCoordinate state =
  justiceDistribution state ,
    (justiceRecognition state , justiceRepresentation state)

-- This is deliberately called a planning distinction rather than a decision or
-- welfare score.  It records which distinctions a downstream planning consumer
-- may require; it does not rank or normatively aggregate them.

PlanningDistinction : Set
PlanningDistinction = Kimmerer.Provenance × JusticeCoordinate

planningDistinction : SituatedEnvironmentalState → PlanningDistinction
planningDistinction state =
  knowledgeProvenance state , justiceCoordinate state

------------------------------------------------------------------------
-- Single/coarse projections are not sufficient for the joint planning
-- distinction.  These are exact finite non-factorability witnesses.
------------------------------------------------------------------------

indigenousLowDistribution : SituatedEnvironmentalState
indigenousLowDistribution =
  Kimmerer.indigenousHistory , Fraser.highRecognitionLowDistribution

scientificLowDistribution : SituatedEnvironmentalState
scientificLowDistribution =
  Kimmerer.scientificHistory , Fraser.highRecognitionLowDistribution

indigenousHighDistribution : SituatedEnvironmentalState
indigenousHighDistribution =
  Kimmerer.indigenousHistory , Fraser.highRecognitionHighDistribution

indigenousLowRepresentation : SituatedEnvironmentalState
indigenousLowRepresentation =
  Kimmerer.indigenousHistory , Fraser.highDistributionLowRepresentation

indigenousHighRepresentation : SituatedEnvironmentalState
indigenousHighRepresentation =
  Kimmerer.indigenousHistory , Fraser.highDistributionHighRepresentation

coarseObservationCannotRecoverPlanningDistinction :
  INF.FactorsThrough coarseEcologicalObservation planningDistinction → ⊥
coarseObservationCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowDistribution
      scientificLowDistribution
      refl
      (λ ()))

provenanceAloneCannotRecoverPlanningDistinction :
  INF.FactorsThrough knowledgeProvenance planningDistinction → ⊥
provenanceAloneCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowDistribution
      indigenousHighDistribution
      refl
      (λ ()))

justiceCoordinatesAloneCannotRecoverPlanningDistinction :
  INF.FactorsThrough justiceCoordinate planningDistinction → ⊥
justiceCoordinatesAloneCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowDistribution
      scientificLowDistribution
      refl
      (λ ()))

recognitionAloneCannotRecoverPlanningDistinction :
  INF.FactorsThrough justiceRecognition planningDistinction → ⊥
recognitionAloneCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowDistribution
      indigenousHighDistribution
      refl
      (λ ()))

distributionAloneCannotRecoverPlanningDistinction :
  INF.FactorsThrough justiceDistribution planningDistinction → ⊥
distributionAloneCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowRepresentation
      indigenousHighRepresentation
      refl
      (λ ()))

representationAloneCannotRecoverPlanningDistinction :
  INF.FactorsThrough justiceRepresentation planningDistinction → ⊥
representationAloneCannotRecoverPlanningDistinction =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      indigenousLowDistribution
      indigenousLowRepresentation
      refl
      (λ ()))

------------------------------------------------------------------------
-- Provenance-preserving cultural hyperfabric instantiation.
--
-- The existing cultural owner deliberately separates memory, practice,
-- relation, knowledge, material relation and provenance fibres.  Here the
-- concrete values remain on SituatedEnvironmentalState while the hyperfabric
-- records which kinds of fibre are available at each situated point.
------------------------------------------------------------------------

data LESBase : Set where
  environmentalSite : LESBase

lesCulturalHyperfabric : Cultural.CulturalHyperfabric
lesCulturalHyperfabric =
  record
    { Cultural.Base = LESBase
    ; Cultural.Point = λ _ → SituatedEnvironmentalState
    ; Cultural.Memory = λ _ _ → Kimmerer.KnowledgeHistory
    ; Cultural.Practice = λ _ _ → Fraser.Recognition
    ; Cultural.Relation = λ _ _ → Fraser.Representation
    ; Cultural.Knowledge = λ _ _ → Kimmerer.Provenance
    ; Cultural.MaterialRelation = λ _ _ → Fraser.Distribution
    ; Cultural.Provenance = λ _ _ → Kimmerer.Provenance
    }

lesPublicEcologicalProjection :
  Cultural.PublicProjection lesCulturalHyperfabric
lesPublicEcologicalProjection =
  record
    { Cultural.Surface = Kimmerer.SharedEcologicalObservation
    ; Cultural.project = λ _ state → coarseEcologicalObservation state
    }

lesPublicProjectionDoesNotBecomeGlobalIdentity :
  Cultural.ProjectionPromotesGlobalIdentity
    lesCulturalHyperfabric lesPublicEcologicalProjection → ⊥
lesPublicProjectionDoesNotBecomeGlobalIdentity =
  Cultural.projectionDoesNotPromoteGlobalIdentity

lesProjectionWithPlanningResidual :
  Cultural.ProjectionWithCulturalResidual
    lesCulturalHyperfabric lesPublicEcologicalProjection
lesProjectionWithPlanningResidual =
  record
    { Cultural.Residual = PlanningDistinction
    ; Cultural.residual = λ _ state → planningDistinction state
    ; Cultural.ReopeningEvidence = ⊤
    ; Cultural.reopeningEvidence = λ _ _ → tt
    }

------------------------------------------------------------------------
-- Stage-6 evidence fibre: the full retained distinction is sufficient for the
-- matching downstream consumer, while the coarse ecological observation is
-- not.  No probability semantics are introduced.
------------------------------------------------------------------------

planningEvidenceCompatible :
  Prediction.Compatible PlanningDistinction SituatedEnvironmentalState
planningEvidenceCompatible evidence state =
  planningDistinction state ≡ evidence

fullPlanningEvidenceIsPointIdentifying :
  (evidence : PlanningDistinction) →
  Prediction.PointIdentifiable
    planningEvidenceCompatible planningDistinction evidence
fullPlanningEvidenceIsPointIdentifying evidence left right leftCompatible rightCompatible =
  trans leftCompatible (sym rightCompatible)

fullPlanningEvidenceHasUniqueEnvelope :
  (evidence : PlanningDistinction) →
  Prediction.EnvelopeUnique
    planningEvidenceCompatible planningDistinction evidence
fullPlanningEvidenceHasUniqueEnvelope evidence =
  Prediction.pointIdentifiableImpliesEnvelopeUnique
    (fullPlanningEvidenceIsPointIdentifying evidence)

-- Equality of a coarse ecological observation cannot close this envelope:
-- the Indigenous/scientific provenance contrast already provides a witness.

coarseCompatible :
  Prediction.Compatible
    Kimmerer.SharedEcologicalObservation SituatedEnvironmentalState
coarseCompatible evidence state =
  coarseEcologicalObservation state ≡ evidence

coarseObservationIsNotPointIdentifying :
  Prediction.PointIdentifiable
    coarseCompatible
    planningDistinction
    Kimmerer.convergentObservation →
  ⊥
coarseObservationIsNotPointIdentifying identifiable =
  (λ ())
    (identifiable
      indigenousLowDistribution
      scientificLowDistribution
      refl
      refl)

------------------------------------------------------------------------
-- Epistemic/predictive adequacy and intervention authority remain separate.
-- An LES promotion package requires both a point-identifiability receipt and an
-- independently admissible situated authority route.
------------------------------------------------------------------------

record LESInterventionPromotion
    {Evidence State PredictionValue Situation Route : Set}
    (compatible : Prediction.Compatible Evidence State)
    (consumer : State → PredictionValue)
    (evidence : Evidence)
    (system : Routing.RoutingSystem Situation Route)
    (situation : Situation)
    (route : Route) : Set₁ where
  constructor lesInterventionPromotion
  field
    predictionIdentifiable :
      Prediction.PointIdentifiable compatible consumer evidence
    authorityAdmissible :
      Routing.AdmissibleRoute system situation route

open LESInterventionPromotion public

resolvedRoutingEvidencePlusInterpretationYieldsPromotion :
  ∀ {Evidence State PredictionValue Situation Route : Set}
    {compatible : Prediction.Compatible Evidence State}
    {consumer : State → PredictionValue}
    {evidence : Evidence}
    {system : Routing.RoutingSystem Situation Route}
    {situation : Situation}
    {route : Route}
    {profile : JusticeEvidence.RouteEvidenceProfile} →
  Prediction.PointIdentifiable compatible consumer evidence →
  Support.RequiredAxesResolved
    (JusticeEvidence.routeEvidenceFamily profile) →
  Authority.RouteEvidenceInterpretation system situation route profile →
  LESInterventionPromotion
    compatible consumer evidence system situation route
resolvedRoutingEvidencePlusInterpretationYieldsPromotion
    identifiable resolved interpretation =
  lesInterventionPromotion
    identifiable
    (Authority.requiredAxisEvidenceYieldsAdmissibleRoute
      resolved interpretation)

-- No theorem is permitted to turn predictive identification into authority by
-- itself.  The type below is deliberately uninhabited.

data PredictionIdentifiabilityAutomaticallyPromotesAuthority : Set where

predictionIdentifiabilityDoesNotSelfPromoteToAuthority :
  PredictionIdentifiabilityAutomaticallyPromotesAuthority → ⊥
predictionIdentifiabilityDoesNotSelfPromoteToAuthority ()

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record LESSituatedSocioEcologicalBoundary : Set where
  constructor lesSituatedSocioEcologicalBoundary
  field
    coarseEcologicalObservationIsWholeSituatedState : Bool
    coarseEcologicalObservationIsWholeSituatedStateIsFalse :
      coarseEcologicalObservationIsWholeSituatedState ≡ false

    sharedObservationErasesKnowledgeProvenance : Bool
    sharedObservationErasesKnowledgeProvenanceIsFalse :
      sharedObservationErasesKnowledgeProvenance ≡ false

    anySingleJusticeAxisIsPlanningSufficient : Bool
    anySingleJusticeAxisIsPlanningSufficientIsFalse :
      anySingleJusticeAxisIsPlanningSufficient ≡ false

    coordinatedKnowledgeRequiresEpistemicFusion : Bool
    coordinatedKnowledgeRequiresEpistemicFusionIsFalse :
      coordinatedKnowledgeRequiresEpistemicFusion ≡ false

    pointIdentifiabilityCreatesAuthority : Bool
    pointIdentifiabilityCreatesAuthorityIsFalse :
      pointIdentifiabilityCreatesAuthority ≡ false

    finiteSpecimenIsEmpiricalEnvironmentalModel : Bool
    finiteSpecimenIsEmpiricalEnvironmentalModelIsFalse :
      finiteSpecimenIsEmpiricalEnvironmentalModel ≡ false

canonicalLESSituatedSocioEcologicalBoundary :
  LESSituatedSocioEcologicalBoundary
canonicalLESSituatedSocioEcologicalBoundary =
  lesSituatedSocioEcologicalBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

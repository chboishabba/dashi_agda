module DASHI.Biology.ConsciousAccessCoalition where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.Core.ContextIndexedSystem as Context
import DASHI.Biology.Cell.BioelectricNetwork as Bioelectric
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful
import DASHI.Biology.ProductiveTransformCoherence as Coherence
import DASHI.Biology.FunctionalConnectomeBodyMemoryBridge as Connectome
import DASHI.Biology.NeurochemicalBrainCarrierBridge as Neurochemical
import DASHI.Biology.PredictiveMetastabilityTraumaBridge as Predictive
import DASHI.Biology.BraidedEmotionDynamics as Emotion
import DASHI.Biology.RelationalChartResidualMachine as Chart
import DASHI.Biology.SparseExpertRoutingCoalition as Sparse

------------------------------------------------------------------------
-- Conscious access as a relational, recurrent coalition.
--
-- This module formalises access-consciousness only.  It does not identify
-- access with phenomenal consciousness, metaphysical consciousness, a single
-- anatomical ignition event, or a universal diagnostic marker.
--
-- Source-facing reference:
-- George Mashour, Pieter Roelfsema, Jean-Pierre Changeux, Stanislas Dehaene,
-- "Conscious Processing and the Global Neuronal Workspace Hypothesis",
-- DOI 10.1016/j.neuron.2020.01.026.

boolAnd : Bool → Bool → Bool
boolAnd false _ = false
boolAnd true b = b

record AccessRelation : Set₁ where
  field
    Representation : Set
    AccessContext : Set
    available : AccessContext → Representation → Bool

open AccessRelation public

data CanonicalAccessContext : Set where
  localRestrictedContext : CanonicalAccessContext
  recurrentGlobalContext : CanonicalAccessContext

canonicalAvailability :
  CanonicalAccessContext → Bool → Bool
canonicalAvailability localRestrictedContext _ = false
canonicalAvailability recurrentGlobalContext _ = true

canonicalAccessRelation : AccessRelation
canonicalAccessRelation =
  record
    { Representation = Bool
    ; AccessContext = CanonicalAccessContext
    ; available = canonicalAvailability
    }

canonicalSameTraceRestricted :
  available canonicalAccessRelation localRestrictedContext false ≡ false
canonicalSameTraceRestricted =
  refl

canonicalSameTraceGloballyAvailable :
  available canonicalAccessRelation recurrentGlobalContext false ≡ true
canonicalSameTraceGloballyAvailable =
  refl

------------------------------------------------------------------------
-- Sink-transform-source-update is represented as a recurrent phase machine,
-- not as a permanent sink.

data CoalitionPhase : Set where
  recruitmentPhase : CoalitionPhase
  transformationPhase : CoalitionPhase
  coherentRegimePhase : CoalitionPhase
  redistributedConstraintPhase : CoalitionPhase
  updatedPhase : CoalitionPhase

nextPhase : CoalitionPhase → CoalitionPhase
nextPhase recruitmentPhase = transformationPhase
nextPhase transformationPhase = coherentRegimePhase
nextPhase coherentRegimePhase = redistributedConstraintPhase
nextPhase redistributedConstraintPhase = updatedPhase
nextPhase updatedPhase = recruitmentPhase

canonicalCoalitionPhaseTrace : List CoalitionPhase
canonicalCoalitionPhaseTrace =
  recruitmentPhase
  ∷ transformationPhase
  ∷ coherentRegimePhase
  ∷ redistributedConstraintPhase
  ∷ updatedPhase
  ∷ []

recruitmentMovesToTransformation :
  nextPhase recruitmentPhase ≡ transformationPhase
recruitmentMovesToTransformation = refl

transformationMovesToCoherentRegime :
  nextPhase transformationPhase ≡ coherentRegimePhase
transformationMovesToCoherentRegime = refl

coherentRegimeRedistributesConstraint :
  nextPhase coherentRegimePhase ≡ redistributedConstraintPhase
coherentRegimeRedistributesConstraint = refl

redistributedConstraintUpdatesState :
  nextPhase redistributedConstraintPhase ≡ updatedPhase
redistributedConstraintUpdatesState = refl

updatedStateReopensRecruitment :
  nextPhase updatedPhase ≡ recruitmentPhase
updatedStateReopensRecruitment = refl

record CoalitionCriteria : Set where
  constructor coalitionCriteria
  field
    transformationalCompatibility : Bool
    recurrentViability : Bool
    broadConditionalReach : Bool
    counterfactualInfluence : Bool
    selfConditioning : Bool

open CoalitionCriteria public

criteriaSatisfied : CoalitionCriteria → Bool
criteriaSatisfied c =
  boolAnd (transformationalCompatibility c)
    (boolAnd (recurrentViability c)
      (boolAnd (broadConditionalReach c)
        (boolAnd (counterfactualInfluence c)
          (selfConditioning c))))

canonicalCoalitionCriteria : CoalitionCriteria
canonicalCoalitionCriteria =
  coalitionCriteria true true true true true

canonicalCoalitionCriteriaSatisfied :
  criteriaSatisfied canonicalCoalitionCriteria ≡ true
canonicalCoalitionCriteriaSatisfied = refl

------------------------------------------------------------------------
-- The aggregate reuses existing DASHI carriers maximally.

record ConsciousAccessCoalition : Setω where
  field
    statefulTransducer :
      Stateful.StatefulTransducer

    bioelectricNetwork :
      Bioelectric.BioelectricNetwork

    contextProjection :
      Context.ContextIndexedProjection

    transformCoherence :
      Coherence.CommutingTriangle

    accessRelation :
      AccessRelation

    criteria :
      CoalitionCriteria

    functionalConnectomeBridge :
      Connectome.FunctionalConnectomeBodyMemoryBridge

    neurochemicalBridge :
      Neurochemical.NeurochemicalBrainCarrierBridge

    predictiveMetastabilityBridge :
      Predictive.PredictiveMetastabilityTraumaBridge

    braidedEmotionDynamics :
      Emotion.BraidedEmotionDynamicsBoundary

    relationalChartMachine :
      Chart.RelationalChartResidualMachine

    sparseExpertBoundary :
      Sparse.SparseExpertCoalitionBoundary

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    accessTheoryOnly : Bool
    accessTheoryOnlyIsTrue : accessTheoryOnly ≡ true

    singleIgnitionEventPromoted : Bool
    singleIgnitionEventPromotedIsFalse :
      singleIgnitionEventPromoted ≡ false

    phenomenalIdentityPromoted : Bool
    phenomenalIdentityPromotedIsFalse :
      phenomenalIdentityPromoted ≡ false

    clinicalAuthorityPromoted : Bool
    clinicalAuthorityPromotedIsFalse :
      clinicalAuthorityPromoted ≡ false

open ConsciousAccessCoalition public

canonicalConsciousAccessCoalition : ConsciousAccessCoalition
canonicalConsciousAccessCoalition =
  record
    { statefulTransducer =
        Stateful.canonicalBoolTransducer
    ; bioelectricNetwork =
        Stateful.canonicalBioelectricNetwork
    ; contextProjection =
        Stateful.canonicalContextIndexedProjection
    ; transformCoherence =
        Coherence.canonicalDoubleInhibitionTriangle
    ; accessRelation =
        canonicalAccessRelation
    ; criteria =
        canonicalCoalitionCriteria
    ; functionalConnectomeBridge =
        Connectome.canonicalFunctionalConnectomeBodyMemoryBridge
    ; neurochemicalBridge =
        Neurochemical.canonicalNeurochemicalBrainCarrierBridge
    ; predictiveMetastabilityBridge =
        Predictive.canonicalPredictiveMetastabilityTraumaBridge
    ; braidedEmotionDynamics =
        Emotion.canonicalBraidedEmotionDynamicsBoundary
    ; relationalChartMachine =
        Chart.canonicalRelationalChartResidualMachine
    ; sparseExpertBoundary =
        Sparse.canonicalSparseExpertCoalitionBoundary
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; accessTheoryOnly =
        true
    ; accessTheoryOnlyIsTrue =
        refl
    ; singleIgnitionEventPromoted =
        false
    ; singleIgnitionEventPromotedIsFalse =
        refl
    ; phenomenalIdentityPromoted =
        false
    ; phenomenalIdentityPromotedIsFalse =
        refl
    ; clinicalAuthorityPromoted =
        false
    ; clinicalAuthorityPromotedIsFalse =
        refl
    }

canonicalCoalitionAccessCriteriaSatisfied :
  criteriaSatisfied (criteria canonicalConsciousAccessCoalition) ≡ true
canonicalCoalitionAccessCriteriaSatisfied =
  refl

canonicalCoalitionSingleIgnitionNotPromoted :
  singleIgnitionEventPromoted canonicalConsciousAccessCoalition ≡ false
canonicalCoalitionSingleIgnitionNotPromoted =
  singleIgnitionEventPromotedIsFalse canonicalConsciousAccessCoalition

canonicalCoalitionPhenomenalIdentityNotPromoted :
  phenomenalIdentityPromoted canonicalConsciousAccessCoalition ≡ false
canonicalCoalitionPhenomenalIdentityNotPromoted =
  phenomenalIdentityPromotedIsFalse canonicalConsciousAccessCoalition

------------------------------------------------------------------------
-- A representation is not intrinsically conscious: the same trace is
-- inaccessible in one context and available in another.

record RelationalAccessWitness : Set where
  constructor relationalAccessWitness
  field
    trace : Bool
    restrictedReading :
      available canonicalAccessRelation localRestrictedContext trace ≡ false
    globalReading :
      available canonicalAccessRelation recurrentGlobalContext trace ≡ true

canonicalRelationalAccessWitness : RelationalAccessWitness
canonicalRelationalAccessWitness =
  relationalAccessWitness false refl refl

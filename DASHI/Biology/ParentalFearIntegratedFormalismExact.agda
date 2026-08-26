module DASHI.Biology.ParentalFearIntegratedFormalismExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Biology.ParentalFearIndependentMobilityExact as Source
import DASHI.Biology.ParentalFearSourceAttributionExact as Attribution
import DASHI.Biology.ParentalFearObserverRefinementExact as ObserverBridge
import DASHI.Biology.ParentalFearConsumerSufficiencyBridgeExact as Sufficiency
import DASHI.Biology.ParentalFearDynamicQuotientBridgeExact as Dynamics

------------------------------------------------------------------------
-- Integrated source/provenance/observer/action/dynamics capstone.
--
-- Source:
-- Justen O'Connor and Alice Brown (2013),
-- "A qualitative study of 'fear' as a regulator of children's independent
-- physical activity in the suburbs", Health & Place 24, 157-164.
-- DOI: 10.1016/j.healthplace.2013.09.002.
--
-- This module intentionally does not invent another mathematical vocabulary.
-- It assembles the existing source-bound hypervoxel, typed attribution,
-- observer refinement, consumer descent/minimal sufficiency, and dynamic
-- quotient-safety owners into one inspectable object.
------------------------------------------------------------------------

-- Static theorem: intervention need does not factor through fear alone.
integratedFearOnlyNonFactorization :
  Consumer.FactorsThrough
    ObserverBridge.fearOnlyObserver
    ObserverBridge.interventionNeed →
  ⊥
integratedFearOnlyNonFactorization =
  Sufficiency.fearOnlyDoesNotFactorInterventionNeed

-- Static theorem: fear-only is not sufficient for the declared consumer.
integratedFearOnlyNotSufficient :
  Consumer.ConsumerSufficient
    ObserverBridge.fearOnlyObserver
    ObserverBridge.interventionNeed →
  ⊥
integratedFearOnlyNotSufficient =
  Sufficiency.fearOnlyNotConsumerSufficient

-- Dynamic theorem: the synthetic coarse fear projection is not trace-safe for
-- the declared future observation language.
integratedCoarseFearDynamicSafetyBlocked :
  Dynamic.DynamicConsumerSafety
    Dynamics.parentalFearSupportSystem
    Dynamics.coarseDynamicFearObserver →
  ⊥
integratedCoarseFearDynamicSafetyBlocked =
  Dynamics.coarseFearNotDynamicallySafeForThisLanguage

record ParentalFearIntegratedFormalism : Set₁ where
  constructor mkParentalFearIntegratedFormalism
  field
    source : Source.ParentalFearIndependentMobilitySource
    sourceIsCanonical :
      source ≡ Source.canonicalParentalFearIndependentMobilitySource

    attribution : Attribution.ParentalFearSourceAttribution
    attributionIsCanonical :
      attribution ≡ Attribution.canonicalParentalFearSourceAttribution

    ecologyBridge : Source.ParentalFearEcologyBridge
    ecologyBridgeIsCanonical :
      ecologyBridge ≡ Source.canonicalParentalFearEcologyBridge

    observerBridge : ObserverBridge.ParentalFearObserverRefinementBridge
    observerBridgeIsCanonical :
      observerBridge ≡
      ObserverBridge.canonicalParentalFearObserverRefinementBridge

    consumerSufficiencyBridge : Sufficiency.ParentalFearConsumerSufficiencyBridge
    consumerSufficiencyBridgeIsCanonical :
      consumerSufficiencyBridge ≡
      Sufficiency.canonicalParentalFearConsumerSufficiencyBridge

    dynamicQuotientBridge : Dynamics.ParentalFearDynamicQuotientBridge
    dynamicQuotientBridgeIsCanonical :
      dynamicQuotientBridge ≡
      Dynamics.canonicalParentalFearDynamicQuotientBridge

    provenanceSurvivesCrossPollination : Bool
    provenanceSurvivesCrossPollinationIsTrue :
      provenanceSurvivesCrossPollination ≡ true

    situatedStateNotCollapsedToFearScalar : Bool
    situatedStateNotCollapsedToFearScalarIsTrue :
      situatedStateNotCollapsedToFearScalar ≡ true

    contextualObserverStrictlyRefinesFearOnly : Bool
    contextualObserverStrictlyRefinesFearOnlyIsTrue :
      contextualObserverStrictlyRefinesFearOnly ≡ true

    fearOnlyConsumerSufficiencyBlocked : Bool
    fearOnlyConsumerSufficiencyBlockedIsTrue :
      fearOnlyConsumerSufficiencyBlocked ≡ true

    fearOnlyFactorizationBlocked : Bool
    fearOnlyFactorizationBlockedIsTrue :
      fearOnlyFactorizationBlocked ≡ true

    sameCurrentFearCanDivergeUnderSharedTrace : Bool
    sameCurrentFearCanDivergeUnderSharedTraceIsTrue :
      sameCurrentFearCanDivergeUnderSharedTrace ≡ true

    staticNonDescentDistinctFromDynamicUnsafety : Bool
    staticNonDescentDistinctFromDynamicUnsafetyIsTrue :
      staticNonDescentDistinctFromDynamicUnsafety ≡ true

    syntheticTheoremsNotPromotedToSourceFindings : Bool
    syntheticTheoremsNotPromotedToSourceFindingsIsTrue :
      syntheticTheoremsNotPromotedToSourceFindings ≡ true

    sourceEvidenceNotUniversalPrescription : Bool
    sourceEvidenceNotUniversalPrescriptionIsTrue :
      sourceEvidenceNotUniversalPrescription ≡ true

    reading : String

open ParentalFearIntegratedFormalism public

canonicalParentalFearIntegratedFormalism : ParentalFearIntegratedFormalism
canonicalParentalFearIntegratedFormalism =
  mkParentalFearIntegratedFormalism
    Source.canonicalParentalFearIndependentMobilitySource refl
    Attribution.canonicalParentalFearSourceAttribution refl
    Source.canonicalParentalFearEcologyBridge refl
    ObserverBridge.canonicalParentalFearObserverRefinementBridge refl
    Sufficiency.canonicalParentalFearConsumerSufficiencyBridge refl
    Dynamics.canonicalParentalFearDynamicQuotientBridge refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "Integrated DASHI formalism: a source-attributed situated fear/IAST hypervoxel is observed through a coarse fear projection and a contextual refinement. The contextual pair is strictly finer. The generic consumer-descent core proves that fear alone is insufficient and cannot factor the declared intervention-need consumer. Separately, a synthetic typed transition system gives a dynamic terminalisation defect: equal current fear labels can diverge after the same admissible support trace. Provenance and source boundaries remain attached throughout, and neither synthetic theorem is attributed back to O'Connor and Brown as an empirical finding."

module DASHI.Programmes.RTXAdmissibleConsumerMDLBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Programmes.RTXLightTransportRefinementExact as RTX

------------------------------------------------------------------------
-- RTX / MDL CROSS-POLLINATION
------------------------------------------------------------------------

record RTXConsumerMDLSurface
    (transport : RTX.LightTransportRefinementInterface) : Set₁ where
  constructor rtxConsumerMDLSurface
  field
    Admissible : RTX.State transport → Set
    ConsumerAdequate : RTX.State transport → Set
    adequacyRespectsObservation :
      (left right : RTX.State transport) →
      RTX.observe transport left ≡ RTX.observe transport right →
      ConsumerAdequate left →
      ConsumerAdequate right
    descriptionLength : RTX.State transport → Nat
    codingConventionReference : String
    consumerReference : String

open RTXConsumerMDLSurface public

rtxRefinementPreservesConsumerAdequacy :
  ∀ {transport}
    (surface : RTXConsumerMDLSurface transport)
    (state : RTX.State transport) →
  ConsumerAdequate surface state →
  ConsumerAdequate surface (RTX.refine transport state)
rtxRefinementPreservesConsumerAdequacy {transport} surface state adequate =
  adequacyRespectsObservation surface
    state
    (RTX.refine transport state)
    (sym (RTX.refinementPreservesObservation transport state))
    adequate

RTXRefines :
  ∀ {transport} →
  RTX.State transport → RTX.State transport → Set
RTXRefines {transport} coarse fine =
  RTX.refine transport coarse ≡ fine

rtxConsumerMDLProblem :
  ∀ {transport} →
  RTXConsumerMDLSurface transport →
  MDL.ConsumerMDLProblem
rtxConsumerMDLProblem {transport} surface =
  MDL.consumerMDLProblem
    (RTX.State transport)
    (Admissible surface)
    (ConsumerAdequate surface)
    (descriptionLength surface)
    (RTXRefines {transport = transport})
    (λ _ → "dashiRTX light-transport state/model")
    (codingConventionReference surface)
    (consumerReference surface)

record RTXAdmissibleMDLBoundary : Set where
  constructor rtxAdmissibleMDLBoundary
  field
    observationPreservingRefinementMayRemainConsumerAdequate : Bool
    observationPreservingRefinementMayRemainConsumerAdequateIsTrue :
      observationPreservingRefinementMayRemainConsumerAdequate ≡ true
    observationPreservationImpliesLowerDescriptionLength : Bool
    observationPreservationImpliesLowerDescriptionLengthIsFalse :
      observationPreservationImpliesLowerDescriptionLength ≡ false
    lowerDescriptionLengthImpliesPhysicalTruth : Bool
    lowerDescriptionLengthImpliesPhysicalTruthIsFalse :
      lowerDescriptionLengthImpliesPhysicalTruth ≡ false

canonicalRTXAdmissibleMDLBoundary : RTXAdmissibleMDLBoundary
canonicalRTXAdmissibleMDLBoundary =
  rtxAdmissibleMDLBoundary true refl false refl false refl

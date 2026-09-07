module DASHI.Core.CounterfactualModelContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COUNTERFACTUAL MODEL CONTRACT
--
-- DASHI-original generic machinery.
--
-- A difference between an observed world and an arbitrary alternative is not
-- yet a causal effect.  The counterfactual contract makes intervention change,
-- held-fixed coordinates, spatial/temporal alignment and justification
-- explicit before downstream causal/economic/climate promotion.
------------------------------------------------------------------------

record CounterfactualContract : Set₁ where
  constructor counterfactual-contract
  field
    World Coordinate Intervention Space Time : Set
    observedWorld : World
    counterfactualWorld : World
    observedIntervention : Intervention
    counterfactualIntervention : Intervention

    ChangedCoordinate HeldFixedCoordinate : Coordinate → Set
    changedCoordinateReceipt : Set
    heldFixedCoordinateReceipt : Set

    observedSpace counterfactualSpace : Space
    observedTime counterfactualTime : Time
    spatialAlignmentReceipt : Set
    temporalAlignmentReceipt : Set
    interventionDifferenceReceipt : Set
    heldFixedJustificationReceipt : Set

    sourceReference : String
    counterfactualMeaning : String

open CounterfactualContract public

record CounterfactualEffectReceipt (contract : CounterfactualContract) : Set₁ where
  constructor counterfactual-effect-receipt
  field
    Outcome : Set
    observedOutcome : Outcome
    counterfactualOutcome : Outcome
    comparisonReceipt : Set
    causalIdentificationReceipt : Set
    effectReference : String

open CounterfactualEffectReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ObservedMinusArbitraryAlternativeImpliesCausalEffectPermission : Set where

data SameEndpointImpliesSameCounterfactualPermission : Set where

data TemporalCoincidenceImpliesCounterfactualIdentityPermission : Set where

data SpatialAggregationImpliesUnitLevelCounterfactualPermission : Set where

observedMinusArbitraryAlternativeDoesNotAutoPromoteToCausalEffect :
  ObservedMinusArbitraryAlternativeImpliesCausalEffectPermission → ⊥
observedMinusArbitraryAlternativeDoesNotAutoPromoteToCausalEffect ()

sameEndpointDoesNotIdentifyCounterfactual :
  SameEndpointImpliesSameCounterfactualPermission → ⊥
sameEndpointDoesNotIdentifyCounterfactual ()

temporalCoincidenceDoesNotIdentifyCounterfactual :
  TemporalCoincidenceImpliesCounterfactualIdentityPermission → ⊥
temporalCoincidenceDoesNotIdentifyCounterfactual ()

spatialAggregationDoesNotAutoSupplyUnitCounterfactual :
  SpatialAggregationImpliesUnitLevelCounterfactualPermission → ⊥
spatialAggregationDoesNotAutoSupplyUnitCounterfactual ()

record CounterfactualBoundary : Set where
  constructor counterfactual-boundary
  field
    changedCoordinatesMustBeDeclared : Bool
    changedCoordinatesMustBeDeclaredIsTrue : changedCoordinatesMustBeDeclared ≡ true
    heldFixedCoordinatesNeedJustification : Bool
    heldFixedCoordinatesNeedJustificationIsTrue : heldFixedCoordinatesNeedJustification ≡ true
    arbitraryAlternativeIsCausalCounterfactual : Bool
    arbitraryAlternativeIsCausalCounterfactualIsFalse :
      arbitraryAlternativeIsCausalCounterfactual ≡ false

canonicalCounterfactualBoundary : CounterfactualBoundary
canonicalCounterfactualBoundary =
  counterfactual-boundary true refl true refl false refl

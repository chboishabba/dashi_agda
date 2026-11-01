module DASHI.Biology.Levin.MultilevelEvolutionCoupling where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Single-level evolutionary dynamics with explicit cross-level remainder.
--
-- Population-level learning is not assumed closed when molecular, organismal,
-- ecological, or cultural levels exert bottom-up or top-down influence.

record MultilevelEvolutionCoupling : Set₁ where
  field
    Level       : Set
    State       : Level → Set
    Tangent     : Level → Set

    intrinsicStep : (l : Level) → State l → Tangent l
    bottomUpCoupling : (l : Level) → State l → Tangent l
    topDownCoupling : (l : Level) → State l → Tangent l
    unresolvedRemainder : (l : Level) → State l → Tangent l

    isolatedLevelApproximation : Level → Bool
    couplingMayDominate : Level → Bool

    bidirectionalCouplingExplicit : Bool
    bidirectionalCouplingExplicitIsTrue :
      bidirectionalCouplingExplicit ≡ true

    noUniversalScaleClosure : Bool
    noUniversalScaleClosureIsFalse :
      noUniversalScaleClosure ≡ false

    couplingReading : String

open MultilevelEvolutionCoupling public

record MultilevelCouplingBoundary : Set where
  field
    populationIsNotOnlyAgentScale : Bool
    populationIsNotOnlyAgentScaleIsFalse :
      populationIsNotOnlyAgentScale ≡ false

    singleLevelFitDoesNotProveClosure : Bool
    singleLevelFitDoesNotProveClosureIsFalse :
      singleLevelFitDoesNotProveClosure ≡ false

    topDownAndBottomUpRemainModelled : Bool
    topDownAndBottomUpRemainModelledIsTrue :
      topDownAndBottomUpRemainModelled ≡ true

canonicalMultilevelCouplingBoundary : MultilevelCouplingBoundary
canonicalMultilevelCouplingBoundary = record
  { populationIsNotOnlyAgentScale = false
  ; populationIsNotOnlyAgentScaleIsFalse = refl
  ; singleLevelFitDoesNotProveClosure = false
  ; singleLevelFitDoesNotProveClosureIsFalse = refl
  ; topDownAndBottomUpRemainModelled = true
  ; topDownAndBottomUpRemainModelledIsTrue = refl
  }

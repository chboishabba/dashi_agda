module DASHI.Biology.Levin.PriceLandeLearningBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Exact identity -> approximate evolutionary learning boundary.
--
-- Price-style bookkeeping is kept separate from the Lande/natural-gradient
-- approximation obtained after inheritance, smoothness, and truncation gates.

record PriceLandeLearningBridge : Set₁ where
  field
    PopulationState : Set
    Trait           : Set
    Fitness         : Set
    Tangent         : Set
    Scalar          : Set

    meanTrait       : PopulationState → Trait
    logFitness      : Trait → Fitness
    covarianceStep  : PopulationState → Tangent
    higherOrderRemainder : PopulationState → Tangent
    transmissionRemainder : PopulationState → Tangent

    priceIdentityExact : Bool
    priceIdentityExactIsTrue : priceIdentityExact ≡ true

    smoothFitness : Bool
    smoothFitnessIsTrue : smoothFitness ≡ true

    smallVariationRegime : Bool
    smallVariationRegimeIsTrue : smallVariationRegime ≡ true

    faithfulTransmissionApproximation : Bool
    faithfulTransmissionApproximationIsTrue :
      faithfulTransmissionApproximation ≡ true

    landeLeadingOrderAvailable : Bool
    landeLeadingOrderAvailableIsTrue :
      landeLeadingOrderAvailable ≡ true

    naturalGradientReadingAvailable : Bool
    naturalGradientReadingAvailableIsTrue :
      naturalGradientReadingAvailable ≡ true

    bridgeReading : String

open PriceLandeLearningBridge public

record PriceLandeBoundary : Set where
  field
    priceIdentityIsNotDynamicsLaw : Bool
    priceIdentityIsNotDynamicsLawIsFalse :
      priceIdentityIsNotDynamicsLaw ≡ false

    landeEquationIsNotExactUniversally : Bool
    landeEquationIsNotExactUniversallyIsFalse :
      landeEquationIsNotExactUniversally ≡ false

    fitnessAscentIsNotGuaranteedGlobally : Bool
    fitnessAscentIsNotGuaranteedGloballyIsFalse :
      fitnessAscentIsNotGuaranteedGlobally ≡ false

    higherOrderTermsRemainExplicit : Bool
    higherOrderTermsRemainExplicitIsTrue :
      higherOrderTermsRemainExplicit ≡ true

canonicalPriceLandeBoundary : PriceLandeBoundary
canonicalPriceLandeBoundary = record
  { priceIdentityIsNotDynamicsLaw = false
  ; priceIdentityIsNotDynamicsLawIsFalse = refl
  ; landeEquationIsNotExactUniversally = false
  ; landeEquationIsNotExactUniversallyIsFalse = refl
  ; fitnessAscentIsNotGuaranteedGlobally = false
  ; fitnessAscentIsNotGuaranteedGloballyIsFalse = refl
  ; higherOrderTermsRemainExplicit = true
  ; higherOrderTermsRemainExplicitIsTrue = refl
  }

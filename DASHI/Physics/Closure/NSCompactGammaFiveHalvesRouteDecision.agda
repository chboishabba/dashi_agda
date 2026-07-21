module DASHI.Physics.Closure.NSCompactGammaFiveHalvesRouteDecision where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Sum.Base using (_⊎_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay

------------------------------------------------------------------------
-- Route A1: adjacent-shell recurrence.
------------------------------------------------------------------------

record AdjacentRecurrenceFiveHalvesControl
    (A : AbsorptionArithmetic) : Set₁ where
  field
    multiplicativeOrder : OrderedSemiringExtension A
    reflexiveOrder : ReflexiveOrderExtension A
    dynamics : FourierShellDynamics A multiplicativeOrder
    decay :
      TwoSidedGeometricShellDecay
        A multiplicativeOrder reflexiveOrder dynamics

open AdjacentRecurrenceFiveHalvesControl public

concreteAdjacentHighShellEstimate :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  ∀ q τ n →
  _≤_ A
    (highValue (dynamics C) q τ (suc n))
    (_+_ A
      (_*_ (multiplicativeOrder C)
        (rho (dynamics C))
        (highValue (dynamics C) q τ n))
      (highRemainder (dynamics C) q τ n))
concreteAdjacentHighShellEstimate C =
  fourierTriadsGiveAdjacentHighShellDecay (dynamics C)

concreteAdjacentLowShellEstimate :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  ∀ q τ n →
  _≤_ A
    (lowValue (dynamics C) q τ (suc n))
    (_+_ A
      (_*_ (multiplicativeOrder C)
        (rho (dynamics C))
        (lowValue (dynamics C) q τ n))
      (lowRemainder (dynamics C) q τ n))
concreteAdjacentLowShellEstimate C =
  fourierTriadsGiveAdjacentLowShellDecay (dynamics C)

concreteShellContraction :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  StrictlyBelow (multiplicativeOrder C)
    (rho (dynamics C)) (one (multiplicativeOrder C))
concreteShellContraction C =
  adjacentShellDecayFactorStrict (dynamics C)

periodicTwoSidedShellDecay :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  ∀ q j τ →
  _≤_ A
    (weightedFiveHalvesShell (dynamics C) j
      (selectedState (dynamics C) q τ))
    (_+_ A
      (decayCoefficient (decay C) q j)
      (compactGammaEnvelope (decay C) q τ))
periodicTwoSidedShellDecay C =
  iteratedTwoSidedFiveHalvesDecay (decay C)

periodicAdjacentRouteControlsFiveHalvesSum :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  ∀ q τ →
  _≤_ A
    (weightedShellSum (decay C) q τ)
    (compactGammaEnvelope (decay C) q τ)
periodicAdjacentRouteControlsFiveHalvesSum C =
  summedTwoSidedFiveHalvesEnvelope (decay C)

------------------------------------------------------------------------
-- Route A2: direct weighted-sum control.
------------------------------------------------------------------------

record DirectWeightedFiveHalvesControl
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Index Time State Shell : Set
    selectedState : Index → Time → State
    weightedFiveHalvesShell : Shell → State → Scalar A
    weightedShellSum compactGammaEnvelope : Index → Time → Scalar A

    periodicCompactGammaControlsFiveHalvesSum : ∀ q τ →
      _≤_ A
        (weightedShellSum q τ)
        (compactGammaEnvelope q τ)

open DirectWeightedFiveHalvesControl public

FiveHalvesControlRoute :
  AbsorptionArithmetic → Set₁
FiveHalvesControlRoute A =
  AdjacentRecurrenceFiveHalvesControl A
  ⊎ DirectWeightedFiveHalvesControl A

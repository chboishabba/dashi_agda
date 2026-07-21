module DASHI.Physics.Closure.NSCompactGammaFiveHalvesRouteDecision where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaGeometricShellDecay

------------------------------------------------------------------------
-- Route A1: adjacent-shell recurrence.
------------------------------------------------------------------------

record GeometricRemainderControl
    (A : AbsorptionArithmetic)
    (M : OrderedSemiringExtension A)
    (D : FourierShellDynamics A M) : Set₁ where
  field
    theta remainderConstant : Scalar A
    thetaStrict : StrictlyBelow M theta (one M)

    remainderEnvelope : Index D → Time D → Scalar A
    geometricMajorant : Index D → Time D → Nat → Scalar A

    geometricMajorantMeaning : ∀ q τ n →
      geometricMajorant q τ n ≡
      _*_ M remainderConstant
        (_*_ M (power M theta n) (remainderEnvelope q τ))

    highRemainderGeometric : ∀ q τ n →
      _≤_ A
        (highRemainder D q τ n)
        (geometricMajorant q τ n)

    lowRemainderGeometric : ∀ q τ n →
      _≤_ A
        (lowRemainder D q τ n)
        (geometricMajorant q τ n)

    summedMajorant uniformRemainderBound :
      Index D → Time D → Scalar A

    remainderMajorantSummable : ∀ q τ →
      _≤_ A (summedMajorant q τ) (uniformRemainderBound q τ)

open GeometricRemainderControl public

record AdjacentRecurrenceFiveHalvesControl
    (A : AbsorptionArithmetic) : Set₁ where
  field
    multiplicativeOrder : OrderedSemiringExtension A
    reflexiveOrder : ReflexiveOrderExtension A
    dynamics : FourierShellDynamics A multiplicativeOrder
    remainderControl :
      GeometricRemainderControl A multiplicativeOrder dynamics
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

concreteRemainderGeometric :
  ∀ {A : AbsorptionArithmetic} →
  (C : AdjacentRecurrenceFiveHalvesControl A) →
  ∀ q τ n →
  (_≤_ A
    (highRemainder (dynamics C) q τ n)
    (geometricMajorant (remainderControl C) q τ n))
  ×
  (_≤_ A
    (lowRemainder (dynamics C) q τ n)
    (geometricMajorant (remainderControl C) q τ n))
concreteRemainderGeometric C q τ n =
  highRemainderGeometric (remainderControl C) q τ n ,
  lowRemainderGeometric (remainderControl C) q τ n

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
    weightedShellSum directCompactGammaEnvelope : Index → Time → Scalar A

    periodicCompactGammaControlsFiveHalvesSum : ∀ q τ →
      _≤_ A
        (weightedShellSum q τ)
        (directCompactGammaEnvelope q τ)

open DirectWeightedFiveHalvesControl public

FiveHalvesControlRoute :
  AbsorptionArithmetic → Set₁
FiveHalvesControlRoute A =
  AdjacentRecurrenceFiveHalvesControl A
  ⊎ DirectWeightedFiveHalvesControl A

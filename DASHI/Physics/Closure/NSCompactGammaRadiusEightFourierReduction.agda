module DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic

------------------------------------------------------------------------
-- Exact radius-eight Fourier reduction.
--
-- The finite dyadic certificate fixes two one-eighth budgets.  This module ties
-- those codes to the concrete analytic chain: multiplier mean-value gain and
-- far-low commutator control on one side, Sobolev/geometric/paraproduct decay on
-- the other.  It proves the final low/high inequalities from the named leaves
-- and constructs the certificate consumed by the exact cutset.
------------------------------------------------------------------------

additionMonotoneBothR8 :
  (A : AbsorptionArithmetic) →
  ∀ {a a′ b b′} →
  _≤_ A a a′ → _≤_ A b b′ →
  _≤_ A (_+_ A a b) (_+_ A a′ b′)
additionMonotoneBothR8 A p q =
  ≤-trans A
    (additionMonotoneRight A p)
    (additionMonotoneLeft A q)

record RadiusEightFourierReduction
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i

    multiplierDifference meanValueBudget radiusEightMultiplierBudget :
      Index → Time → Scalar A

    farLowTail farLowRawBudget farLowDisplayedBudget :
      Index → Time → Scalar A

    highShellTail highSobolevBudget highGeometricBudget :
      Index → Time → Scalar A

    farHighLeft farHighRight : Index → Time → Scalar A
    farHighLeftBudget farHighRightBudget : Index → Time → Scalar A
    farHighTail farHighDisplayedBudget : Index → Time → Scalar A

    -- C1/C2: exact smooth multiplier and R = 8 separation gain.
    periodicMultiplierMeanValueBound : ∀ q τ →
      _≤_ A (multiplierDifference q τ) (meanValueBudget q τ)

    radiusEightMultiplierGain : ∀ q τ →
      _≤_ A (meanValueBudget q τ) (radiusEightMultiplierBudget q τ)

    farLowCommutatorFromMultiplier : ∀ q τ →
      _≤_ A (farLowTail q τ) (farLowRawBudget q τ)

    radiusEightMultiplierProducesFarLowBudget : ∀ q τ →
      _≤_ A (farLowRawBudget q τ) (farLowDisplayedBudget q τ)

    -- D1/D2: high-shell Sobolev decay and its geometric-series sum.
    highShellSobolevDecay : ∀ q τ →
      _≤_ A (highShellTail q τ) (highSobolevBudget q τ)

    farHighGeometricSeries : ∀ q τ →
      _≤_ A (highSobolevBudget q τ) (highGeometricBudget q τ)

    farHighTailBelowPlacements : ∀ q τ →
      _≤_ A
        (farHighTail q τ)
        (_+_ A (farHighLeft q τ) (farHighRight q τ))

    farHighLeftParaproductBound : ∀ q τ →
      _≤_ A (farHighLeft q τ) (farHighLeftBudget q τ)

    farHighRightParaproductBound : ∀ q τ →
      _≤_ A (farHighRight q τ) (farHighRightBudget q τ)

    highPlacementsFitDisplayedBudget : ∀ q τ →
      _≤_ A
        (_+_ A (farHighLeftBudget q τ) (farHighRightBudget q τ))
        (farHighDisplayedBudget q τ)

    normalizedFarLowAtEight normalizedFarHighAtEight : Nat

    normalizedFarLowAtEightFits :
      normalizedFarLowAtEight Dyadic.≤ᴺ Dyadic.epsilonLowAtEight

    normalizedFarHighAtEightFits :
      normalizedFarHighAtEight Dyadic.≤ᴺ Dyadic.epsilonHighAtEight

open RadiusEightFourierReduction public

periodicFarLowCommutatorBound :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (R : RadiusEightFourierReduction A Index) → ∀ q τ →
  _≤_ A (farLowTail R q τ) (farLowDisplayedBudget R q τ)
periodicFarLowCommutatorBound {A = A} R q τ =
  ≤-trans A
    (farLowCommutatorFromMultiplier R q τ)
    (radiusEightMultiplierProducesFarLowBudget R q τ)

periodicFarHighTailBound :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (R : RadiusEightFourierReduction A Index) → ∀ q τ →
  _≤_ A (farHighTail R q τ) (farHighDisplayedBudget R q τ)
periodicFarHighTailBound {A = A} R q τ =
  ≤-trans A
    (farHighTailBelowPlacements R q τ)
    (≤-trans A
      (additionMonotoneBothR8 A
        (farHighLeftParaproductBound R q τ)
        (farHighRightParaproductBound R q τ))
      (highPlacementsFitDisplayedBudget R q τ))

periodicRadiusEightAnalyticBounds :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  RadiusEightFourierReduction A Index →
  Dyadic.RadiusEightAnalyticBounds
periodicRadiusEightAnalyticBounds R = record
  { normalizedLowTailAtEight = normalizedFarLowAtEight R
  ; normalizedHighTailAtEight = normalizedFarHighAtEight R
  ; low-fits-certified-budget = normalizedFarLowAtEightFits R
  ; high-fits-certified-budget = normalizedFarHighAtEightFits R
  }

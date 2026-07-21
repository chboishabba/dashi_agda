module DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic
import DASHI.Physics.Closure.NSCompactGammaRadiusEightFourierReduction as RadiusEight

------------------------------------------------------------------------
-- Primitive analytic owners for the two radius-eight tails.
--
-- The far-low chain starts at the exact commutator produced by divergence-free
-- cancellation.  The far-high chain starts at the two Bony placements and passes
-- through one Sobolev shell tail and one geometric series.  The final constructor
-- builds the repository's coherent `RadiusEightFourierReduction` package.
------------------------------------------------------------------------

record FarLowPrimitiveInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time : Set i) : Set (lsuc i) where
  field
    farLowTail commutatorForm multiplierDifferenceTerm :
      Index → Time → Scalar A

    meanValueTerm separatedRadiusEightTerm displayedLowBudget :
      Index → Time → Scalar A

    -- Fourier cancellation and Leray/polarization reduction.
    farLowBecomesCommutator : ∀ q τ →
      _≤_ A (farLowTail q τ) (commutatorForm q τ)

    commutatorControlledByMultiplierDifference : ∀ q τ →
      _≤_ A (commutatorForm q τ) (multiplierDifferenceTerm q τ)

    -- Smooth multiplier mean-value estimate and |p| <= 2^(K-8).
    multiplierMeanValue : ∀ q τ →
      _≤_ A (multiplierDifferenceTerm q τ) (meanValueTerm q τ)

    radiusEightSeparationGain : ∀ q τ →
      _≤_ A (meanValueTerm q τ) (separatedRadiusEightTerm q τ)

    fullLowConstantFitsDisplayedBudget : ∀ q τ →
      _≤_ A (separatedRadiusEightTerm q τ) (displayedLowBudget q τ)

    normalizedFarLowAtEight : Nat
    normalizedFarLowAtEightFits :
      Dyadic._≤ᴺ_ normalizedFarLowAtEight Dyadic.epsilonLowAtEight

open FarLowPrimitiveInputs public

record FarHighPrimitiveInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time : Set i) : Set (lsuc i) where
  field
    farHighTail farHighLeft farHighRight :
      Index → Time → Scalar A

    farHighLeftProduct farHighRightProduct placementSum :
      Index → Time → Scalar A

    highShellTail sobolevTail geometricTail displayedHighBudget :
      Index → Time → Scalar A

    farHighSplitsIntoPlacements : ∀ q τ →
      _≤_ A
        (farHighTail q τ)
        (_+_ A (farHighLeft q τ) (farHighRight q τ))

    leftParaproductEstimate : ∀ q τ →
      _≤_ A (farHighLeft q τ) (farHighLeftProduct q τ)

    rightParaproductEstimate : ∀ q τ →
      _≤_ A (farHighRight q τ) (farHighRightProduct q τ)

    productPlacementsFitCommonSum : ∀ q τ →
      _≤_ A
        (_+_ A (farHighLeftProduct q τ) (farHighRightProduct q τ))
        (placementSum q τ)

    placementsControlledByHighShell : ∀ q τ →
      _≤_ A (placementSum q τ) (highShellTail q τ)

    highShellSobolevDecay : ∀ q τ →
      _≤_ A (highShellTail q τ) (sobolevTail q τ)

    sumGeometricFarHighTail : ∀ q τ →
      _≤_ A (sobolevTail q τ) (geometricTail q τ)

    fullHighConstantFitsDisplayedBudget : ∀ q τ →
      _≤_ A (geometricTail q τ) (displayedHighBudget q τ)

    normalizedFarHighAtEight : Nat
    normalizedFarHighAtEightFits :
      Dyadic._≤ᴺ_ normalizedFarHighAtEight Dyadic.epsilonHighAtEight

open FarHighPrimitiveInputs public

additionMonotoneBothPrimitive :
  (A : AbsorptionArithmetic) →
  ∀ {a a′ b b′} →
  _≤_ A a a′ → _≤_ A b b′ →
  _≤_ A (_+_ A a b) (_+_ A a′ b′)
additionMonotoneBothPrimitive A left right =
  ≤-trans A
    (additionMonotoneRight A left)
    (additionMonotoneLeft A right)

farLowRadiusEightFromPrimitive :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time : Set i} →
  (L : FarLowPrimitiveInputs A Index Time) → ∀ q τ →
  _≤_ A (farLowTail L q τ) (displayedLowBudget L q τ)
farLowRadiusEightFromPrimitive {A = A} L q τ =
  ≤-trans A
    (farLowBecomesCommutator L q τ)
    (≤-trans A
      (commutatorControlledByMultiplierDifference L q τ)
      (≤-trans A
        (multiplierMeanValue L q τ)
        (≤-trans A
          (radiusEightSeparationGain L q τ)
          (fullLowConstantFitsDisplayedBudget L q τ))))

farHighRadiusEightFromPrimitive :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time : Set i} →
  (H : FarHighPrimitiveInputs A Index Time) → ∀ q τ →
  _≤_ A (farHighTail H q τ) (displayedHighBudget H q τ)
farHighRadiusEightFromPrimitive {A = A} H q τ =
  ≤-trans A
    (farHighSplitsIntoPlacements H q τ)
    (≤-trans A
      (additionMonotoneBothPrimitive A
        (leftParaproductEstimate H q τ)
        (rightParaproductEstimate H q τ))
      (≤-trans A
        (productPlacementsFitCommonSum H q τ)
        (≤-trans A
          (placementsControlledByHighShell H q τ)
          (≤-trans A
            (highShellSobolevDecay H q τ)
            (≤-trans A
              (sumGeometricFarHighTail H q τ)
              (fullHighConstantFitsDisplayedBudget H q τ))))))

record RadiusEightPrimitiveInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i
    low : FarLowPrimitiveInputs A Index Time
    high : FarHighPrimitiveInputs A Index Time

open RadiusEightPrimitiveInputs public

primitiveInputsToRadiusEightReduction :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  RadiusEightPrimitiveInputs A Index →
  RadiusEight.RadiusEightFourierReduction A Index
primitiveInputsToRadiusEightReduction {A = A} P = record
  { Time = Time P
  ; multiplierDifference = multiplierDifferenceTerm (low P)
  ; meanValueBudget = meanValueTerm (low P)
  ; radiusEightMultiplierBudget = separatedRadiusEightTerm (low P)
  ; farLowTail = farLowTail (low P)
  ; farLowCommutatorBudget = commutatorForm (low P)
  ; farLowDisplayedBudget = displayedLowBudget (low P)
  ; highShellTail = highShellTail (high P)
  ; highSobolevBudget = sobolevTail (high P)
  ; highGeometricBudget = geometricTail (high P)
  ; farHighLeft = farHighLeft (high P)
  ; farHighRight = farHighRight (high P)
  ; farHighLeftBudget = farHighLeftProduct (high P)
  ; farHighRightBudget = farHighRightProduct (high P)
  ; farHighTail = farHighTail (high P)
  ; farHighDisplayedBudget = displayedHighBudget (high P)
  ; farLowTailBelowCommutatorBudget = farLowBecomesCommutator (low P)
  ; commutatorBudgetBelowMultiplierDifference =
      commutatorControlledByMultiplierDifference (low P)
  ; periodicMultiplierMeanValueBound = multiplierMeanValue (low P)
  ; radiusEightMultiplierGain = radiusEightSeparationGain (low P)
  ; radiusEightMultiplierProducesFarLowBudget =
      fullLowConstantFitsDisplayedBudget (low P)
  ; farHighTailBelowPlacements = farHighSplitsIntoPlacements (high P)
  ; farHighLeftParaproductBound = leftParaproductEstimate (high P)
  ; farHighRightParaproductBound = rightParaproductEstimate (high P)
  ; highPlacementsControlledByHighShell = λ q τ →
      ≤-trans A
        (productPlacementsFitCommonSum (high P) q τ)
        (placementsControlledByHighShell (high P) q τ)
  ; highShellSobolevDecay = highShellSobolevDecay (high P)
  ; farHighGeometricSeries = sumGeometricFarHighTail (high P)
  ; highGeometricFitsDisplayedBudget =
      fullHighConstantFitsDisplayedBudget (high P)
  ; normalizedFarLowAtEight = normalizedFarLowAtEight (low P)
  ; normalizedFarHighAtEight = normalizedFarHighAtEight (high P)
  ; normalizedFarLowAtEightFits = normalizedFarLowAtEightFits (low P)
  ; normalizedFarHighAtEightFits = normalizedFarHighAtEightFits (high P)
  }

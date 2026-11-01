module DASHI.Physics.Closure.NSPeriodicFourierRadiusEightAuthorityBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate as Dyadic
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority
import DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters as Selected
import DASHI.Physics.Closure.NSPeriodicFourierRadiusEightPrimitiveReduction as Primitive

------------------------------------------------------------------------
-- Standard multiplier-commutator and H^s tail estimates are consumed here.
--
-- The remaining radius-eight leaves are exact decomposition/normalization facts:
-- R=8 separation, the full constants fitting their one-eighth budgets, the
-- two-placement regrouping, and the geometric-series normalization.
------------------------------------------------------------------------

record RadiusEightAuthorityInterpretation
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Shell Time State : Set i)
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State) : Set (lsuc i) where
  field
    farLowTail separatedRadiusEightTerm displayedLowBudget :
      Index → Time → Scalar A

    farLowBecomesCommutator : ∀ q τ →
      _≤_ A
        (farLowTail q τ)
        (Authority.farLowCommutator
          (Selected.authority S) q τ (Selected.selectedState S q τ))

    radiusEightSeparationGain : ∀ q τ →
      _≤_ A
        (Authority.meanValueMajorant
          (Selected.authority S) q τ (Selected.selectedState S q τ))
        (separatedRadiusEightTerm q τ)

    fullLowConstantFitsDisplayedBudget : ∀ q τ →
      _≤_ A
        (separatedRadiusEightTerm q τ)
        (displayedLowBudget q τ)

    normalizedFarLowAtEight : Nat
    normalizedFarLowAtEightFits :
      Dyadic._≤ᴺ_ normalizedFarLowAtEight Dyadic.epsilonLowAtEight

    farHighTail placementSum geometricTail displayedHighBudget :
      Index → Time → Scalar A

    farHighSplitsIntoPlacements : ∀ q τ →
      _≤_ A
        (farHighTail q τ)
        (_+_ A
          (Authority.farHighLeft
            (Selected.authority S) q τ (Selected.selectedState S q τ))
          (Authority.farHighRight
            (Selected.authority S) q τ (Selected.selectedState S q τ)))

    productPlacementsFitCommonSum : ∀ q τ →
      _≤_ A
        (_+_ A
          (Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ))
          (Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ)))
        (placementSum q τ)

    placementsControlledByHighShell : ∀ q τ →
      _≤_ A
        (placementSum q τ)
        (Authority.highFiveHalvesTail
          (Selected.authority S) q τ (Selected.selectedState S q τ))

    sumGeometricFarHighTail : ∀ q τ →
      _≤_ A
        (Authority.hSobolevNorm
          (Selected.authority S) q τ (Selected.selectedState S q τ))
        (geometricTail q τ)

    fullHighConstantFitsDisplayedBudget : ∀ q τ →
      _≤_ A (geometricTail q τ) (displayedHighBudget q τ)

    normalizedFarHighAtEight : Nat
    normalizedFarHighAtEightFits :
      Dyadic._≤ᴺ_ normalizedFarHighAtEight Dyadic.epsilonHighAtEight

open RadiusEightAuthorityInterpretation public

authorityInterpretationToRadiusEightPrimitive :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i}
    {S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State} →
  RadiusEightAuthorityInterpretation A Index Shell Time State S →
  Primitive.RadiusEightPrimitiveInputs A Index
authorityInterpretationToRadiusEightPrimitive
    {A = A} {Time = Time} {S = S} I = record
  { Time = Time
  ; low = record
      { farLowTail = farLowTail I
      ; commutatorForm = λ q τ →
          Authority.farLowCommutator
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; multiplierDifferenceTerm = λ q τ →
          Authority.multiplierDifference
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; meanValueTerm = λ q τ →
          Authority.meanValueMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; separatedRadiusEightTerm = separatedRadiusEightTerm I
      ; displayedLowBudget = displayedLowBudget I
      ; farLowBecomesCommutator = farLowBecomesCommutator I
      ; commutatorControlledByMultiplierDifference =
          Selected.selectedFarLowCommutatorEstimate S
      ; multiplierMeanValue =
          Selected.selectedMultiplierMeanValueEstimate S
      ; radiusEightSeparationGain = radiusEightSeparationGain I
      ; fullLowConstantFitsDisplayedBudget =
          fullLowConstantFitsDisplayedBudget I
      ; normalizedFarLowAtEight = normalizedFarLowAtEight I
      ; normalizedFarLowAtEightFits = normalizedFarLowAtEightFits I
      }
  ; high = record
      { farHighTail = farHighTail I
      ; farHighLeft = λ q τ →
          Authority.farHighLeft
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; farHighRight = λ q τ →
          Authority.farHighRight
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; farHighLeftProduct = λ q τ →
          Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; farHighRightProduct = λ q τ →
          Authority.farHighSobolevMajorant
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; placementSum = placementSum I
      ; highShellTail = λ q τ →
          Authority.highFiveHalvesTail
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; sobolevTail = λ q τ →
          Authority.hSobolevNorm
            (Selected.authority S) q τ (Selected.selectedState S q τ)
      ; geometricTail = geometricTail I
      ; displayedHighBudget = displayedHighBudget I
      ; farHighSplitsIntoPlacements = farHighSplitsIntoPlacements I
      ; leftParaproductEstimate = Selected.selectedFarHighLeftEstimate S
      ; rightParaproductEstimate = Selected.selectedFarHighRightEstimate S
      ; productPlacementsFitCommonSum = productPlacementsFitCommonSum I
      ; placementsControlledByHighShell = placementsControlledByHighShell I
      ; highShellSobolevDecay = Selected.selectedHighSobolevTailEstimate S
      ; sumGeometricFarHighTail = sumGeometricFarHighTail I
      ; fullHighConstantFitsDisplayedBudget =
          fullHighConstantFitsDisplayedBudget I
      ; normalizedFarHighAtEight = normalizedFarHighAtEight I
      ; normalizedFarHighAtEightFits = normalizedFarHighAtEightFits I
      }
  }

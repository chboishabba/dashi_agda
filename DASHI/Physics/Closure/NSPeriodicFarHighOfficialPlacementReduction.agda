module DASHI.Physics.Closure.NSPeriodicFarHighOfficialPlacementReduction where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion as High
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Official far-high placement reduction.
--
-- The two placement estimates are no longer opaque fields.  Each is factored
-- through three named inequalities:
--
--   nonlinear placement -> Leibniz/Leray majorant
--                        -> cube-shell Bernstein majorant
--                        -> official Sobolev shell-tail term.
--
-- The geometric summation and radius-eight scalar comparison remain separate.
-- In particular, this module does not freeze the structural constant to eight.
------------------------------------------------------------------------

record FarHighTailSkeleton
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    Admissible : Index → Time → State → Set i

    farHighTotal leftPlacement rightPlacement placementSum :
      Index → Time → State → Scalar A

    highFiveHalvesTail hSobolevMajorant geometricTailMajorant :
      Index → Time → State → Scalar A

    radiusEightOfficialBudget : Index → Time → State → Scalar A

    exactPlacementDecomposition : ∀ q τ u →
      farHighTotal q τ u
      ≡ _+_ A (leftPlacement q τ u) (rightPlacement q τ u)

    placementSumMeaning : ∀ q τ u →
      placementSum q τ u
      ≡ _+_ A (highFiveHalvesTail q τ u) (highFiveHalvesTail q τ u)

    sobolevToHighShellTail : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (placementSum q τ u) (hSobolevMajorant q τ u)

    exactGeometricTailSummation : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (hSobolevMajorant q τ u) (geometricTailMajorant q τ u)

    radiusEightFullConstantFitsBudget : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (geometricTailMajorant q τ u) (radiusEightOfficialBudget q τ u)

    CutoffUniform : Set i
    cutoffUniform : CutoffUniform

open FarHighTailSkeleton public

record FarHighOfficialPlacementReductionInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    skeleton : FarHighTailSkeleton A Index Time State

    leftLeibnizMajorant leftBernsteinMajorant :
      Index → Time → State → Scalar A

    rightLeibnizMajorant rightBernsteinMajorant :
      Index → Time → State → Scalar A

    -- This proposition owns the genuine s>5/2 requirement in the official
    -- normalization.  It is carried explicitly into every analytic step.
    CriticalSurplusPositive : Set i
    criticalSurplusPositive : CriticalSurplusPositive

    leftLeibnizStep : ∀ q τ u →
      Admissible skeleton q τ u →
      _≤_ A
        (leftPlacement skeleton q τ u)
        (leftLeibnizMajorant q τ u)

    leftCubeBernsteinStep : ∀ q τ u →
      Admissible skeleton q τ u →
      _≤_ A
        (leftLeibnizMajorant q τ u)
        (leftBernsteinMajorant q τ u)

    leftSobolevConversion : ∀ q τ u →
      CriticalSurplusPositive →
      Admissible skeleton q τ u →
      _≤_ A
        (leftBernsteinMajorant q τ u)
        (highFiveHalvesTail skeleton q τ u)

    rightLeibnizStep : ∀ q τ u →
      Admissible skeleton q τ u →
      _≤_ A
        (rightPlacement skeleton q τ u)
        (rightLeibnizMajorant q τ u)

    rightCubeBernsteinStep : ∀ q τ u →
      Admissible skeleton q τ u →
      _≤_ A
        (rightLeibnizMajorant q τ u)
        (rightBernsteinMajorant q τ u)

    rightSobolevConversion : ∀ q τ u →
      CriticalSurplusPositive →
      Admissible skeleton q τ u →
      _≤_ A
        (rightBernsteinMajorant q τ u)
        (highFiveHalvesTail skeleton q τ u)

open FarHighOfficialPlacementReductionInputs public

leftPlacementProductEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FarHighOfficialPlacementReductionInputs A Index Time State) →
  ∀ q τ u → Admissible (skeleton I) q τ u →
  _≤_ A
    (leftPlacement (skeleton I) q τ u)
    (highFiveHalvesTail (skeleton I) q τ u)
leftPlacementProductEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (leftLeibnizStep I q τ u admissible)
    (≤-trans A
      (leftCubeBernsteinStep I q τ u admissible)
      (leftSobolevConversion I q τ u
        (criticalSurplusPositive I) admissible))

rightPlacementProductEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FarHighOfficialPlacementReductionInputs A Index Time State) →
  ∀ q τ u → Admissible (skeleton I) q τ u →
  _≤_ A
    (rightPlacement (skeleton I) q τ u)
    (highFiveHalvesTail (skeleton I) q τ u)
rightPlacementProductEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (rightLeibnizStep I q τ u admissible)
    (≤-trans A
      (rightCubeBernsteinStep I q τ u admissible)
      (rightSobolevConversion I q τ u
        (criticalSurplusPositive I) admissible))

farHighOfficialTailInputsFromPlacementReduction :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  FarHighOfficialPlacementReductionInputs A Index Time State →
  High.PeriodicFarHighTailInputs A Index Time State
farHighOfficialTailInputsFromPlacementReduction I = record
  { Admissible = Admissible (skeleton I)
  ; farHighTotal = farHighTotal (skeleton I)
  ; leftPlacement = leftPlacement (skeleton I)
  ; rightPlacement = rightPlacement (skeleton I)
  ; placementSum = placementSum (skeleton I)
  ; highFiveHalvesTail = highFiveHalvesTail (skeleton I)
  ; hSobolevMajorant = hSobolevMajorant (skeleton I)
  ; geometricTailMajorant = geometricTailMajorant (skeleton I)
  ; radiusEightOfficialBudget = radiusEightOfficialBudget (skeleton I)
  ; exactPlacementDecomposition = exactPlacementDecomposition (skeleton I)
  ; leftPlacementProductEstimate = leftPlacementProductEstimate I
  ; rightPlacementProductEstimate = rightPlacementProductEstimate I
  ; placementSumMeaning = placementSumMeaning (skeleton I)
  ; sobolevToHighShellTail = sobolevToHighShellTail (skeleton I)
  ; exactGeometricTailSummation = exactGeometricTailSummation (skeleton I)
  ; radiusEightFullConstantFitsBudget =
      radiusEightFullConstantFitsBudget (skeleton I)
  ; CutoffUniform = CutoffUniform (skeleton I)
  ; cutoffUniform = cutoffUniform (skeleton I)
  }

farHighPlacementReductionLevel : ProofLevel
farHighPlacementReductionLevel = machineChecked

farHighCubeBernsteinConstantLevel : ProofLevel
farHighCubeBernsteinConstantLevel = conditional

farHighOfficialSobolevConversionLevel : ProofLevel
farHighOfficialSobolevConversionLevel = conditional

farHighStructuralConstantDerivationLevel : ProofLevel
farHighStructuralConstantDerivationLevel = conditional

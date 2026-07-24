module DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Complete far-high Sobolev/geometric-tail theorem surface.
------------------------------------------------------------------------

record PeriodicFarHighTailInputs
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
      farHighTotal q τ u ≡
      _+_ A (leftPlacement q τ u) (rightPlacement q τ u)

    leftPlacementProductEstimate : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (leftPlacement q τ u) (highFiveHalvesTail q τ u)

    rightPlacementProductEstimate : ∀ q τ u →
      Admissible q τ u →
      _≤_ A (rightPlacement q τ u) (highFiveHalvesTail q τ u)

    placementSumMeaning : ∀ q τ u →
      placementSum q τ u ≡
      _+_ A (highFiveHalvesTail q τ u) (highFiveHalvesTail q τ u)

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

open PeriodicFarHighTailInputs public

farHighPlacementSumBound :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (F : PeriodicFarHighTailInputs A Index Time State) →
  ∀ q τ u →
  Admissible F q τ u →
  _≤_ A
    (_+_ A (leftPlacement F q τ u) (rightPlacement F q τ u))
    (placementSum F q τ u)
farHighPlacementSumBound {A = A} F q τ u admissible =
  subst
    (λ rhs →
      _≤_ A
        (_+_ A (leftPlacement F q τ u) (rightPlacement F q τ u))
        rhs)
    (sym (placementSumMeaning F q τ u))
    placementComponents
  where
  firstStep :
    _≤_ A
      (_+_ A (leftPlacement F q τ u) (rightPlacement F q τ u))
      (_+_ A (highFiveHalvesTail F q τ u) (rightPlacement F q τ u))
  firstStep =
    additionMonotoneRight A (leftPlacementProductEstimate F q τ u admissible)

  secondStep :
    _≤_ A
      (_+_ A (highFiveHalvesTail F q τ u) (rightPlacement F q τ u))
      (_+_ A
        (highFiveHalvesTail F q τ u)
        (highFiveHalvesTail F q τ u))
  secondStep =
    additionMonotoneLeft A (rightPlacementProductEstimate F q τ u admissible)

  placementComponents :
    _≤_ A
      (_+_ A (leftPlacement F q τ u) (rightPlacement F q τ u))
      (_+_ A
        (highFiveHalvesTail F q τ u)
        (highFiveHalvesTail F q τ u))
  placementComponents = ≤-trans A firstStep secondStep

periodicFarHighOfficialRadiusEightEstimate :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Time State : Set i} →
  (F : PeriodicFarHighTailInputs A Index Time State) →
  ∀ q τ u →
  Admissible F q τ u →
  _≤_ A
    (farHighTotal F q τ u)
    (radiusEightOfficialBudget F q τ u)
periodicFarHighOfficialRadiusEightEstimate {A = A} F q τ u admissible =
  ≤-trans A totalToPlacement
    (≤-trans A
      (sobolevToHighShellTail F q τ u admissible)
      (≤-trans A
        (exactGeometricTailSummation F q τ u admissible)
        (radiusEightFullConstantFitsBudget F q τ u admissible)))
  where
  totalToPlacement :
    _≤_ A
      (farHighTotal F q τ u)
      (placementSum F q τ u)
  totalToPlacement =
    subst
      (λ lhs → _≤_ A lhs (placementSum F q τ u))
      (sym (exactPlacementDecomposition F q τ u))
      (farHighPlacementSumBound F q τ u admissible)

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

farHighPlacementAssemblyLevel : ProofLevel
farHighPlacementAssemblyLevel = machineChecked

farHighSobolevTailLevel : ProofLevel
farHighSobolevTailLevel = conditional

farHighGeometricSummationLevel : ProofLevel
farHighGeometricSummationLevel = conditional

farHighRadiusEightFullBudgetLevel : ProofLevel
farHighRadiusEightFullBudgetLevel = conditional

farHighOfficialTailInputsInhabited : Bool
farHighOfficialTailInputsInhabited = false

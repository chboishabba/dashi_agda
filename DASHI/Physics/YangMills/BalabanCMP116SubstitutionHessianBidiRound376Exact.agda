module DASHI.Physics.YangMills.BalabanCMP116SubstitutionHessianBidiRound376Exact where

------------------------------------------------------------------------
-- ROUND376 / BIDI: R351 H_sub -> R375 MARKED-COEFFICIENT BRIDGE
--
-- R351 already separates the physical CMP116 displacement theorem
--
--   d_sub^src <= M_marked^src
--
-- from the selected same-object attachment and compiles
--
--   d_sub^selected <= M_marked^selected.
--
-- R375 still accepted `selectedBoundaryDistanceBelowMarkedInput` as a primitive
-- application field.  This owner removes that duplication.  On the SAME
-- decoupled boundary carrier, one coordinate equality identifies R373's selected
-- boundary substitution distance with R351's selected substitution distance.
-- Then R351 supplies nonnegativity and the marked-input upper mechanically.
--
-- No new CMP116 displacement estimate, Cauchy theorem, marked-walk resummation,
-- or Hessian inequality is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionMarkedSourceRound351Exact as R351
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116HessianBidiBridgeRound375Exact as R375

------------------------------------------------------------------------
-- Boundary carrier already selected by R373's literal decoupled Hessian object.
------------------------------------------------------------------------

JointBoundaryPoint : R373.JointBoundaryHessianPaymentData → Set
JointBoundaryPoint joint =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R373.decoupled joint))
    (Decoupled.componentIndices
      (R373.decoupled joint)
      (R373.component joint))

record CMP116SubstitutionHessianBidiData : Set₁ where
  field
    joint : R373.JointBoundaryHessianPaymentData

    substitutionSource :
      R351.CMP116SubstitutionMarkedSource (JointBoundaryPoint joint)

    substitutionAttachment :
      R351.SelectedSubstitutionMarkedAttachment substitutionSource

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R373.selectedLipschitz joint

    -- The only new same-object weld introduced by R376.
    boundaryDistanceIsSelectedSubstitutionDistance :
      ∀ s →
      R373.selectedBoundarySubstitutionDistance joint s
      ≡
      R351.selectedSubstitutionDistance substitutionAttachment s

open CMP116SubstitutionHessianBidiData public

selectedBoundaryDistanceNonnegativeFromR351 :
  (dataSet : CMP116SubstitutionHessianBidiData) →
  ∀ s →
  0ℝ ≤ℝ R373.selectedBoundarySubstitutionDistance (joint dataSet) s
selectedBoundaryDistanceNonnegativeFromR351 dataSet s
  rewrite boundaryDistanceIsSelectedSubstitutionDistance dataSet s
  | R351.selectedDistanceIsSource (substitutionAttachment dataSet) s =
  R351.sourceDistanceNonnegative (substitutionSource dataSet) s

selectedMarkedInputNonnegativeFromR351 :
  (dataSet : CMP116SubstitutionHessianBidiData) →
  0ℝ ≤ℝ R351.selectedMarkedInput (substitutionAttachment dataSet)
selectedMarkedInputNonnegativeFromR351 dataSet
  rewrite R351.selectedMarkedInputIsSource (substitutionAttachment dataSet) =
  R351.sourceMarkedInputNonnegative (substitutionSource dataSet)

selectedBoundaryDistanceBelowMarkedInputFromR351 :
  (dataSet : CMP116SubstitutionHessianBidiData) →
  ∀ s →
  R373.selectedBoundarySubstitutionDistance (joint dataSet) s
  ≤ℝ
  R351.selectedMarkedInput (substitutionAttachment dataSet)
selectedBoundaryDistanceBelowMarkedInputFromR351 dataSet s
  rewrite boundaryDistanceIsSelectedSubstitutionDistance dataSet s =
  R351.selectedSubstitutionMarkedFromSource
    (substitutionSource dataSet)
    (substitutionAttachment dataSet)
    s

asRound375BidiData :
  CMP116SubstitutionHessianBidiData →
  R375.CMP116HessianBidiBridgeData
asRound375BidiData dataSet = record
  { R375.CMP116HessianBidiBridgeData.joint = joint dataSet
  ; R375.CMP116HessianBidiBridgeData.markedInput =
      R351.selectedMarkedInput (substitutionAttachment dataSet)
  ; R375.CMP116HessianBidiBridgeData.selectedLipschitzNonnegative =
      selectedLipschitzNonnegative dataSet
  ; R375.CMP116HessianBidiBridgeData.selectedBoundaryDistanceNonnegative =
      selectedBoundaryDistanceNonnegativeFromR351 dataSet
  ; R375.CMP116HessianBidiBridgeData.markedInputNonnegative =
      selectedMarkedInputNonnegativeFromR351 dataSet
  ; R375.CMP116HessianBidiBridgeData.selectedBoundaryDistanceBelowMarkedInput =
      selectedBoundaryDistanceBelowMarkedInputFromR351 dataSet
  }

round376SelectedCoefficientDifferenceBound :
  (dataSet : CMP116SubstitutionHessianBidiData) →
  Cauchy.normValue
    (Decoupled.cauchy (R373.decoupled (joint dataSet)))
    (Cauchy._-Value_
      (Decoupled.cauchy (R373.decoupled (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.leftDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet)))
      (Decoupled.decoupledHessianCoefficient
        (R373.decoupled (joint dataSet))
        (R373.rightDomain (joint dataSet))
        (R373.component (joint dataSet))
        (R373.leftVariation (joint dataSet))
        (R373.rightVariation (joint dataSet))))
  ≤ℝ
  R373.selectedLipschitz (joint dataSet)
    *ℝ R351.selectedMarkedInput (substitutionAttachment dataSet)
round376SelectedCoefficientDifferenceBound dataSet =
  R375.selectedCoefficientDifferenceBound (asRound375BidiData dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round376HSubToBidiCompilerLevel : ProofLevel
round376HSubToBidiCompilerLevel = machineChecked

literalBoundaryDistanceCoordinateWeldLevel : ProofLevel
literalBoundaryDistanceCoordinateWeldLevel = conditional

hSubAttachmentFeedsHessianBidi : Bool
hSubAttachmentFeedsHessianBidi = true

hSubAttachmentFeedsHessianBidiIsTrue :
  hSubAttachmentFeedsHessianBidi ≡ true
hSubAttachmentFeedsHessianBidiIsTrue = refl

separateDistanceToMarkedInputPrimitiveAfterRound376 : Bool
separateDistanceToMarkedInputPrimitiveAfterRound376 = false

separateDistanceToMarkedInputPrimitiveAfterRound376IsFalse :
  separateDistanceToMarkedInputPrimitiveAfterRound376 ≡ false
separateDistanceToMarkedInputPrimitiveAfterRound376IsFalse = refl

boundaryDistanceCoordinateWeldStillRequired : Bool
boundaryDistanceCoordinateWeldStillRequired = true

boundaryDistanceCoordinateWeldStillRequiredIsTrue :
  boundaryDistanceCoordinateWeldStillRequired ≡ true
boundaryDistanceCoordinateWeldStillRequiredIsTrue = refl

record Round376Boundary : Set where
  constructor round376-boundary
  field
    r351DisplacementUpperReused : Bool
    r351DisplacementUpperReusedIsTrue :
      r351DisplacementUpperReused ≡ true

    freshHSubInequalityRequired : Bool
    freshHSubInequalityRequiredIsFalse :
      freshHSubInequalityRequired ≡ false

    oneSameObjectDistanceCoordinateWeldRemains : Bool
    oneSameObjectDistanceCoordinateWeldRemainsIsTrue :
      oneSameObjectDistanceCoordinateWeldRemains ≡ true

canonicalRound376Boundary : Round376Boundary
canonicalRound376Boundary =
  round376-boundary true refl false refl true refl

round376FrontierRefinementLevel : ProofLevel
round376FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

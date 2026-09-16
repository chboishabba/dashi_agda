module DASHI.Physics.YangMills.BalabanCMP116AffineArgumentDifferenceRound369Exact where

------------------------------------------------------------------------
-- ROUND369 / THE CMP116 AFFINE ARGUMENT DIFFERENCE IS GENERIC ALGEBRA
--
-- R366 left one source-facing coordinate in the chain
--
--   (A' - H_L X) - (A' - H_R X)
--      = (H_R - H_L) X.
--
-- The first equality is not a new Yang--Mills estimate.  It follows from the
-- ordinary laws of an abelian additive carrier together with the statement that
-- the selected operator subtraction acts pointwise as operator difference.
--
-- This file proves that generic cancellation and compiles it into the R367/R366
-- argument-defect inequality.  It does NOT identify the source CMP116
-- background carrier with this algebra, and it does NOT prove the CMP99 marked
-- H_L-H_R bound.  Those remain same-object / physical source payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP102CriticalMapLipschitzRound367Exact as R367

record AbelianDifferenceLaws (Point : Set) : Set₁ where
  field
    zero : Point
    add : Point → Point → Point
    negate : Point → Point
    subtract : Point → Point → Point
    subtractDefinition : ∀ left right →
      subtract left right ≡ add left (negate right)
    addAssociative : ∀ a b c →
      add (add a b) c ≡ add a (add b c)
    addCommutative : ∀ a b → add a b ≡ add b a
    addZeroLeft : ∀ a → add zero a ≡ a
    addInverseRight : ∀ a → add a (negate a) ≡ zero
    negateAdd : ∀ a b →
      negate (add a b) ≡ add (negate a) (negate b)
    negateNegate : ∀ a → negate (negate a) ≡ a

open AbelianDifferenceLaws public

commonBaseDifferenceCancellation :
  ∀ {Point}
    (laws : AbelianDifferenceLaws Point)
    base leftShift rightShift →
  subtract laws
    (subtract laws base leftShift)
    (subtract laws base rightShift)
  ≡ subtract laws rightShift leftShift
commonBaseDifferenceCancellation laws base leftShift rightShift
  rewrite subtractDefinition laws (subtract laws base leftShift) (subtract laws base rightShift)
        | subtractDefinition laws base leftShift
        | subtractDefinition laws base rightShift
        | negateAdd laws base (negate laws rightShift)
        | negateNegate laws rightShift =
  trans
    (addAssociative laws
      base (negate laws leftShift)
      (add laws (negate laws base) rightShift))
    (trans
      (cong (add laws base)
        (sym (addAssociative laws
          (negate laws leftShift) (negate laws base) rightShift)))
      (trans
        (cong (add laws base)
          (cong (λ pair → add laws pair rightShift)
            (addCommutative laws (negate laws leftShift) (negate laws base))))
        (trans
          (cong (add laws base)
            (addAssociative laws
              (negate laws base) (negate laws leftShift) rightShift))
          (trans
            (sym (addAssociative laws
              base (negate laws base)
              (add laws (negate laws leftShift) rightShift)))
            (trans
              (cong
                (λ cancelled → add laws cancelled
                  (add laws (negate laws leftShift) rightShift))
                (addInverseRight laws base))
              (trans
                (addZeroLeft laws
                  (add laws (negate laws leftShift) rightShift))
                (trans
                  (addCommutative laws (negate laws leftShift) rightShift)
                  (sym (subtractDefinition laws rightShift leftShift)))))))))

record DifferenceOperatorAction
    {Point : Set}
    (laws : AbelianDifferenceLaws Point) : Set₁ where
  field
    Operator : Set
    apply : Operator → Point → Point
    subtractOperator : Operator → Operator → Operator
    applyOperatorDifference : ∀ right left vector →
      apply (subtractOperator right left) vector
      ≡ subtract laws (apply right vector) (apply left vector)

open DifferenceOperatorAction public

record CMP116AffineArgumentData (Point : Set) : Set₁ where
  field
    laws : AbelianDifferenceLaws Point
    operators : DifferenceOperatorAction laws
    basePoint : Point
    leftOperator rightOperator : Operator operators
    candidate : Point
    size : Point → ℝ

open CMP116AffineArgumentData public

affineLeftArgument :
  ∀ {Point} → CMP116AffineArgumentData Point → Point
affineLeftArgument dataSet =
  subtract (laws dataSet)
    (basePoint dataSet)
    (apply (operators dataSet) (leftOperator dataSet) (candidate dataSet))

affineRightArgument :
  ∀ {Point} → CMP116AffineArgumentData Point → Point
affineRightArgument dataSet =
  subtract (laws dataSet)
    (basePoint dataSet)
    (apply (operators dataSet) (rightOperator dataSet) (candidate dataSet))

affineArgumentDifference :
  ∀ {Point} → CMP116AffineArgumentData Point → Point
affineArgumentDifference dataSet =
  subtract (laws dataSet)
    (affineLeftArgument dataSet)
    (affineRightArgument dataSet)

affinePropagatorDifferenceAction :
  ∀ {Point} → CMP116AffineArgumentData Point → Point
affinePropagatorDifferenceAction dataSet =
  apply (operators dataSet)
    (subtractOperator (operators dataSet)
      (rightOperator dataSet) (leftOperator dataSet))
    (candidate dataSet)

affineArgumentDifferenceIsOperatorDifferenceAction :
  ∀ {Point} (dataSet : CMP116AffineArgumentData Point) →
  affineArgumentDifference dataSet
  ≡ affinePropagatorDifferenceAction dataSet
affineArgumentDifferenceIsOperatorDifferenceAction dataSet =
  trans
    (commonBaseDifferenceCancellation
      (laws dataSet)
      (basePoint dataSet)
      (apply (operators dataSet) (leftOperator dataSet) (candidate dataSet))
      (apply (operators dataSet) (rightOperator dataSet) (candidate dataSet)))
    (sym
      (applyOperatorDifference
        (operators dataSet)
        (rightOperator dataSet)
        (leftOperator dataSet)
        (candidate dataSet)))

affineArgumentDefect :
  ∀ {Point} → CMP116AffineArgumentData Point → ℝ
affineArgumentDefect dataSet = size dataSet (affineArgumentDifference dataSet)

affinePropagatorActionDefect :
  ∀ {Point} → CMP116AffineArgumentData Point → ℝ
affinePropagatorActionDefect dataSet =
  size dataSet (affinePropagatorDifferenceAction dataSet)

affineArgumentDefectIsPropagatorActionDefect :
  ∀ {Point} (dataSet : CMP116AffineArgumentData Point) →
  affineArgumentDefect dataSet ≡ affinePropagatorActionDefect dataSet
affineArgumentDefectIsPropagatorActionDefect dataSet =
  cong (size dataSet) (affineArgumentDifferenceIsOperatorDifferenceAction dataSet)

affineArgumentDefectBelowPropagatorActionDefect :
  ∀ {Point} (dataSet : CMP116AffineArgumentData Point) →
  affineArgumentDefect dataSet ≤ℝ affinePropagatorActionDefect dataSet
affineArgumentDefectBelowPropagatorActionDefect dataSet
  rewrite affineArgumentDefectIsPropagatorActionDefect dataSet = ≤ℝ-refl

record CMP102CriticalMapAffineToR367Data (Point : Set) : Set₁ where
  field
    source : R367.CMP102CriticalMapContractionData Point
    affine : CMP116AffineArgumentData Point
    leftArgumentInSourceBall :
      R367.InSourceBall source (affineLeftArgument affine)
    rightArgumentInSourceBall :
      R367.InSourceBall source (affineRightArgument affine)
    mapDefect : ℝ
    propagatorDifference : ℝ
    candidateSize : ℝ
    candidateRadius : ℝ
    mapDefectNonnegative : 0ℝ ≤ℝ mapDefect
    argumentDefectNonnegative : 0ℝ ≤ℝ affineArgumentDefect affine
    propagatorActionDefectNonnegative :
      0ℝ ≤ℝ affinePropagatorActionDefect affine
    propagatorDifferenceNonnegative : 0ℝ ≤ℝ propagatorDifference
    candidateSizeNonnegative : 0ℝ ≤ℝ candidateSize
    candidateRadiusNonnegative : 0ℝ ≤ℝ candidateRadius
    mapDefectIsSourceDistance :
      mapDefect ≡
      R367.distance source
        (R367.criticalMap source (affineLeftArgument affine))
        (R367.criticalMap source (affineRightArgument affine))
    argumentDefectIsSourceDistance :
      affineArgumentDefect affine ≡
      R367.distance source
        (affineLeftArgument affine) (affineRightArgument affine)
    propagatorActionDefectBelowDifferenceTimesCandidate :
      affinePropagatorActionDefect affine
      ≤ℝ propagatorDifference *ℝ candidateSize
    candidateSizeBelowRadius : candidateSize ≤ℝ candidateRadius

open CMP102CriticalMapAffineToR367Data public

asR367CriticalMapData :
  ∀ {Point} →
  CMP102CriticalMapAffineToR367Data Point →
  R367.CMP102CriticalMapToR366Data Point
asR367CriticalMapData dataSet = record
  { R367.source = source dataSet
  ; R367.leftArgument = affineLeftArgument (affine dataSet)
  ; R367.rightArgument = affineRightArgument (affine dataSet)
  ; R367.leftArgumentInSourceBall = leftArgumentInSourceBall dataSet
  ; R367.rightArgumentInSourceBall = rightArgumentInSourceBall dataSet
  ; R367.mapDefect = mapDefect dataSet
  ; R367.argumentDefect = affineArgumentDefect (affine dataSet)
  ; R367.propagatorActionDefect = affinePropagatorActionDefect (affine dataSet)
  ; R367.propagatorDifference = propagatorDifference dataSet
  ; R367.candidateSize = candidateSize dataSet
  ; R367.candidateRadius = candidateRadius dataSet
  ; R367.mapDefectNonnegative = mapDefectNonnegative dataSet
  ; R367.argumentDefectNonnegative = argumentDefectNonnegative dataSet
  ; R367.propagatorActionDefectNonnegative =
      propagatorActionDefectNonnegative dataSet
  ; R367.propagatorDifferenceNonnegative = propagatorDifferenceNonnegative dataSet
  ; R367.candidateSizeNonnegative = candidateSizeNonnegative dataSet
  ; R367.candidateRadiusNonnegative = candidateRadiusNonnegative dataSet
  ; R367.mapDefectIsSourceDistance = mapDefectIsSourceDistance dataSet
  ; R367.argumentDefectIsSourceDistance = argumentDefectIsSourceDistance dataSet
  ; R367.argumentDefectBelowPropagatorAction =
      affineArgumentDefectBelowPropagatorActionDefect (affine dataSet)
  ; R367.propagatorActionDefectBelowDifferenceTimesCandidate =
      propagatorActionDefectBelowDifferenceTimesCandidate dataSet
  ; R367.candidateSizeBelowRadius = candidateSizeBelowRadius dataSet
  }

round369MapDefectBelowAssociatedSourceProduct :
  ∀ {Point} (dataSet : CMP102CriticalMapAffineToR367Data Point) →
  mapDefect dataSet
  ≤ℝ
  (R367.lipschitzConstant (source dataSet) *ℝ propagatorDifference dataSet)
    *ℝ candidateRadius dataSet
round369MapDefectBelowAssociatedSourceProduct dataSet =
  R367.round367MapDefectBelowAssociatedSourceProduct
    (asR367CriticalMapData dataSet)

affineDifferenceAlgebraCompilerLevel : ProofLevel
affineDifferenceAlgebraCompilerLevel = machineChecked

literalCMP116AffineOperationSameObjectAttachmentLevel : ProofLevel
literalCMP116AffineOperationSameObjectAttachmentLevel = conditional

literalCMP99ToCMP116PropagatorDifferenceAttachmentLevel : ProofLevel
literalCMP99ToCMP116PropagatorDifferenceAttachmentLevel =
  R367.literalCMP99ToCMP116PropagatorDifferenceAttachmentLevel

literalCMP102CriticalMapSameObjectAttachmentLevel : ProofLevel
literalCMP102CriticalMapSameObjectAttachmentLevel =
  R367.literalCMP102CriticalMapSameObjectAttachmentLevel

literalCMP116CommonCandidateRadiusAttachmentLevel : ProofLevel
literalCMP116CommonCandidateRadiusAttachmentLevel = conditional

argumentDefectScalarInequalityPrimitiveAfterRound369 : Bool
argumentDefectScalarInequalityPrimitiveAfterRound369 = false

argumentDefectScalarInequalityPrimitiveAfterRound369IsFalse :
  argumentDefectScalarInequalityPrimitiveAfterRound369 ≡ false
argumentDefectScalarInequalityPrimitiveAfterRound369IsFalse = refl

affineCancellationIsGenericNotNewYMAnalysis : Bool
affineCancellationIsGenericNotNewYMAnalysis = true

affineCancellationIsGenericNotNewYMAnalysisIsTrue :
  affineCancellationIsGenericNotNewYMAnalysis ≡ true
affineCancellationIsGenericNotNewYMAnalysisIsTrue = refl

sameObjectOperationAttachmentStillRequired : Bool
sameObjectOperationAttachmentStillRequired = true

sameObjectOperationAttachmentStillRequiredIsTrue :
  sameObjectOperationAttachmentStillRequired ≡ true
sameObjectOperationAttachmentStillRequiredIsTrue = refl

round369CompilerLevel : ProofLevel
round369CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false

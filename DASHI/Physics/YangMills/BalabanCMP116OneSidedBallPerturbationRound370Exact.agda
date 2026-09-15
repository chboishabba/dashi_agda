module DASHI.Physics.YangMills.BalabanCMP116OneSidedBallPerturbationRound370Exact where

------------------------------------------------------------------------
-- ROUND370 / R365 NEEDS CROSS-MEMBERSHIP, NOT EQUALITY OF SOURCE BALLS
--
-- R368 exposes, for every fixed decoupling parameter s, the literal CMP116
-- composite map F_s and one invariant contraction ball for that map.
--
-- The generic R365 perturbation proof contracts only the LEFT map between the
-- two fixed points.  Hence it does not require
--
--   sourceBall s_L == sourceBall s_R.
--
-- It needs only that both fixed points lie in the left source ball, together
-- with their own fixed-point equations and the one-step cross-parameter defect.
-- This file makes that least-privilege interface explicit and compiles it into
-- R365.  No new CMP116 analytic estimate is asserted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as QIF
import DASHI.Physics.YangMills.BalabanCMP116SubstitutionContractionRound365Exact as R365
import DASHI.Physics.YangMills.BalabanCMP116DirectDecoupledContractionRound368Exact as R368

ballMapAtIsSourceMap :
  ∀ {Parameter Point Bound}
    (source : R368.CMP116DecoupledCompositeContraction Parameter Point Bound)
    parameter point →
  QIF.map (R368.sourceBall source parameter) point
  ≡ R368.sourceMap source parameter point
ballMapAtIsSourceMap source parameter point =
  cong (λ map → map point) (R368.sourceBallUsesLiteralMap source parameter)

record OneSidedSourceBallPerturbationData
    (Parameter Point Bound : Set) : Set₁ where
  field
    source : R368.CMP116DecoupledCompositeContraction Parameter Point Bound

    add : Bound → Bound → Bound
    addMonotone : ∀ {left leftUpper right rightUpper} →
      QIF.LessEqual (R368.metric source) left leftUpper →
      QIF.LessEqual (R368.metric source) right rightUpper →
      QIF.LessEqual (R368.metric source)
        (add left right) (add leftUpper rightUpper)

    triangle : ∀ left middle right →
      QIF.LessEqual (R368.metric source)
        (QIF.distance (R368.metric source) left right)
        (add
          (QIF.distance (R368.metric source) left middle)
          (QIF.distance (R368.metric source) middle right))

    leftParameter rightParameter : Parameter
    leftPoint rightPoint : Point

    leftPointInLeftSourceBall :
      QIF.InBall (R368.sourceBall source leftParameter) leftPoint

    -- This is the least domain-overlap condition actually consumed by R365.
    -- Equality of the left/right balls is stronger and is not required.
    rightPointInLeftSourceBall :
      QIF.InBall (R368.sourceBall source leftParameter) rightPoint

    leftPointFixedBySourceMap :
      R368.sourceMap source leftParameter leftPoint ≡ leftPoint

    rightPointFixedBySourceMap :
      R368.sourceMap source rightParameter rightPoint ≡ rightPoint

    defect : Bound

    oneStepSourceMapDefect :
      QIF.LessEqual (R368.metric source)
        (QIF.distance (R368.metric source)
          (R368.sourceMap source leftParameter rightPoint)
          (R368.sourceMap source rightParameter rightPoint))
        defect

    amplification : Bound

    absorbContractedPlusDefect :
      ∀ factor value localDefect →
      QIF.StrictlyBelowOne (R368.metric source) factor →
      QIF.LessEqual (R368.metric source)
        value
        (add
          (QIF.multiply (R368.metric source) factor value)
          localDefect) →
      QIF.LessEqual (R368.metric source)
        value
        (QIF.multiply (R368.metric source) amplification localDefect)

open OneSidedSourceBallPerturbationData public

leftPointFixedInLeftBallMap :
  ∀ {Parameter Point Bound}
    (dataSet : OneSidedSourceBallPerturbationData Parameter Point Bound) →
  QIF.map (R368.sourceBall (source dataSet) (leftParameter dataSet))
    (leftPoint dataSet)
  ≡ leftPoint dataSet
leftPointFixedInLeftBallMap dataSet =
  trans
    (ballMapAtIsSourceMap
      (source dataSet) (leftParameter dataSet) (leftPoint dataSet))
    (leftPointFixedBySourceMap dataSet)

rightPointFixedInRightBallMap :
  ∀ {Parameter Point Bound}
    (dataSet : OneSidedSourceBallPerturbationData Parameter Point Bound) →
  QIF.map (R368.sourceBall (source dataSet) (rightParameter dataSet))
    (rightPoint dataSet)
  ≡ rightPoint dataSet
rightPointFixedInRightBallMap dataSet =
  trans
    (ballMapAtIsSourceMap
      (source dataSet) (rightParameter dataSet) (rightPoint dataSet))
    (rightPointFixedBySourceMap dataSet)

oneStepBallMapDefect :
  ∀ {Parameter Point Bound}
    (dataSet : OneSidedSourceBallPerturbationData Parameter Point Bound) →
  QIF.LessEqual (R368.metric (source dataSet))
    (QIF.distance (R368.metric (source dataSet))
      (QIF.map (R368.sourceBall (source dataSet) (leftParameter dataSet))
        (rightPoint dataSet))
      (QIF.map (R368.sourceBall (source dataSet) (rightParameter dataSet))
        (rightPoint dataSet)))
    (defect dataSet)
oneStepBallMapDefect dataSet
  rewrite ballMapAtIsSourceMap
      (source dataSet) (leftParameter dataSet) (rightPoint dataSet)
        | ballMapAtIsSourceMap
      (source dataSet) (rightParameter dataSet) (rightPoint dataSet) =
  oneStepSourceMapDefect dataSet

asR365ParametricFixedPointStability :
  ∀ {Parameter Point Bound} →
  OneSidedSourceBallPerturbationData Parameter Point Bound →
  R365.ParametricFixedPointStabilityData Point Bound
asR365ParametricFixedPointStability dataSet = record
  { R365.metric = R368.metric (source dataSet)
  ; R365.add = add dataSet
  ; R365.addMonotone = addMonotone dataSet
  ; R365.triangle = triangle dataSet
  ; R365.leftBall = R368.sourceBall (source dataSet) (leftParameter dataSet)
  ; R365.rightBall = R368.sourceBall (source dataSet) (rightParameter dataSet)
  ; R365.leftPoint = leftPoint dataSet
  ; R365.rightPoint = rightPoint dataSet
  ; R365.leftPointInLeftBall = leftPointInLeftSourceBall dataSet
  ; R365.rightPointInLeftBall = rightPointInLeftSourceBall dataSet
  ; R365.leftPointFixed = leftPointFixedInLeftBallMap dataSet
  ; R365.rightPointFixed = rightPointFixedInRightBallMap dataSet
  ; R365.defect = defect dataSet
  ; R365.oneStepMapDefect = oneStepBallMapDefect dataSet
  ; R365.amplification = amplification dataSet
  ; R365.absorbContractedPlusDefect = absorbContractedPlusDefect dataSet
  }

oneSidedSourceBallFixedPointStability :
  ∀ {Parameter Point Bound}
    (dataSet : OneSidedSourceBallPerturbationData Parameter Point Bound) →
  QIF.LessEqual (R368.metric (source dataSet))
    (QIF.distance (R368.metric (source dataSet))
      (leftPoint dataSet) (rightPoint dataSet))
    (QIF.multiply (R368.metric (source dataSet))
      (amplification dataSet) (defect dataSet))
oneSidedSourceBallFixedPointStability dataSet =
  R365.parametricFixedPointStability
    (asR365ParametricFixedPointStability dataSet)

------------------------------------------------------------------------
-- Pareto / payment boundary.
------------------------------------------------------------------------

round370OneSidedBallCompilerLevel : ProofLevel
round370OneSidedBallCompilerLevel = machineChecked

literalCMP116RightFixedPointInLeftSourceBallLevel : ProofLevel
literalCMP116RightFixedPointInLeftSourceBallLevel = conditional

literalCMP116CrossParameterMapDefectLevel : ProofLevel
literalCMP116CrossParameterMapDefectLevel = conditional

commonSourceBallEqualityPrimitiveAfterRound370 : Bool
commonSourceBallEqualityPrimitiveAfterRound370 = false

commonSourceBallEqualityPrimitiveAfterRound370IsFalse :
  commonSourceBallEqualityPrimitiveAfterRound370 ≡ false
commonSourceBallEqualityPrimitiveAfterRound370IsFalse = refl

oneSidedCrossMembershipStillRequired : Bool
oneSidedCrossMembershipStillRequired = true

oneSidedCrossMembershipStillRequiredIsTrue :
  oneSidedCrossMembershipStillRequired ≡ true
oneSidedCrossMembershipStillRequiredIsTrue = refl

crossParameterMapDefectStillRequired : Bool
crossParameterMapDefectStillRequired = true

crossParameterMapDefectStillRequiredIsTrue :
  crossParameterMapDefectStillRequired ≡ true
crossParameterMapDefectStillRequiredIsTrue = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false

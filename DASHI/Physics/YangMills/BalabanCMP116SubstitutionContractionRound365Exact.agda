module DASHI.Physics.YangMills.BalabanCMP116SubstitutionContractionRound365Exact where

------------------------------------------------------------------------
-- ROUND365 / H_subScale FROM PARAMETRIC FIXED-POINT STABILITY
--
-- R364 showed that the source-native CMP116 Hessian route only needs
--
--   H_local    : local Hessian stability along the substituted background;
--   H_subScale : pointwise substituted-background displacement is bounded by
--                one source displacement scale.
--
-- CMP116 constructs the substituted background by a contractive fixed-point
-- equation on one common analytic domain.  Therefore H_subScale should not be
-- treated as a primitive two-solution theorem if it can be reduced to the
-- standard perturbation estimate for two fixed points:
--
--   d(x_L,x_R)
--     <= d(F_L x_L,F_L x_R) + d(F_L x_R,F_R x_R)
--     <= q d(x_L,x_R) + delta.
--
-- After the scalar contraction is absorbed, only the one-step map defect
-- delta and the same-object identification of d(x_L,x_R) with the literal
-- CMP116 substituted-background distance remain source-facing.
--
-- This module proves that compiler and specializes it to the R364 ABI.  It
-- does NOT manufacture the literal CMP116 critical map, its common invariant
-- ball, the one-step parameter defect, the scalar absorption constant, or the
-- H_local Hessian estimate.
--
-- Safety boundary: this route imports R364 and the historical quantitative
-- implicit-function owner, neither of which is declared --safe.  This file
-- therefore intentionally makes no --safe claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-trans)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact as QIF
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanDecoupledActivityDirectStabilityRound364Exact as R364
import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352

------------------------------------------------------------------------
-- Generic least-privilege fixed-point perturbation compiler.
------------------------------------------------------------------------

record ParametricFixedPointStabilityData (Point Bound : Set) : Set₁ where
  field
    metric : QIF.QuantitativeMetricAlgebra Point Bound

    add : Bound → Bound → Bound
    addMonotone : ∀ {left leftUpper right rightUpper} →
      QIF.LessEqual metric left leftUpper →
      QIF.LessEqual metric right rightUpper →
      QIF.LessEqual metric
        (add left right)
        (add leftUpper rightUpper)

    triangle : ∀ left middle right →
      QIF.LessEqual metric
        (QIF.distance metric left right)
        (add
          (QIF.distance metric left middle)
          (QIF.distance metric middle right))

    leftBall rightBall : QIF.InvariantContractionBall metric

    leftPoint rightPoint : Point

    leftPointInLeftBall : QIF.InBall leftBall leftPoint
    rightPointInLeftBall : QIF.InBall leftBall rightPoint

    leftPointFixed : QIF.map leftBall leftPoint ≡ leftPoint
    rightPointFixed : QIF.map rightBall rightPoint ≡ rightPoint

    defect : Bound

    -- The only cross-parameter analytic input needed by the generic compiler:
    -- evaluate both critical maps at the SAME right fixed point.
    oneStepMapDefect :
      QIF.LessEqual metric
        (QIF.distance metric
          (QIF.map leftBall rightPoint)
          (QIF.map rightBall rightPoint))
        defect

    amplification : Bound

    -- Scalar ordered-field absorption.  For the usual q < 1 presentation this
    -- is the standard rearrangement of d <= q d + delta.  We keep it separate
    -- from the YM map-defect theorem.
    absorbContractedPlusDefect :
      ∀ factor value localDefect →
      QIF.StrictlyBelowOne metric factor →
      QIF.LessEqual metric
        value
        (add (QIF.multiply metric factor value) localDefect) →
      QIF.LessEqual metric
        value
        (QIF.multiply metric amplification localDefect)

open ParametricFixedPointStabilityData public

fixedPointDistanceBelowContractedPlusDefect :
  ∀ {Point Bound}
    (dataSet : ParametricFixedPointStabilityData Point Bound) →
  QIF.LessEqual (metric dataSet)
    (QIF.distance (metric dataSet)
      (leftPoint dataSet) (rightPoint dataSet))
    (add dataSet
      (QIF.multiply (metric dataSet)
        (QIF.contractionFactor (leftBall dataSet))
        (QIF.distance (metric dataSet)
          (leftPoint dataSet) (rightPoint dataSet)))
      (defect dataSet))
fixedPointDistanceBelowContractedPlusDefect dataSet =
  subst
    (λ lhs →
      QIF.LessEqual (metric dataSet) lhs
        (add dataSet
          (QIF.multiply (metric dataSet)
            (QIF.contractionFactor (leftBall dataSet))
            (QIF.distance (metric dataSet)
              (leftPoint dataSet) (rightPoint dataSet)))
          (defect dataSet)))
    (cong₂ (QIF.distance (metric dataSet))
      (leftPointFixed dataSet)
      (rightPointFixed dataSet))
    (QIF.transitive (metric dataSet)
      (triangle dataSet
        (QIF.map (leftBall dataSet) (leftPoint dataSet))
        (QIF.map (leftBall dataSet) (rightPoint dataSet))
        (QIF.map (rightBall dataSet) (rightPoint dataSet)))
      (addMonotone dataSet
        (QIF.mapContractive (leftBall dataSet)
          (leftPoint dataSet) (rightPoint dataSet)
          (leftPointInLeftBall dataSet)
          (rightPointInLeftBall dataSet))
        (oneStepMapDefect dataSet)))

parametricFixedPointStability :
  ∀ {Point Bound}
    (dataSet : ParametricFixedPointStabilityData Point Bound) →
  QIF.LessEqual (metric dataSet)
    (QIF.distance (metric dataSet)
      (leftPoint dataSet) (rightPoint dataSet))
    (QIF.multiply (metric dataSet)
      (amplification dataSet) (defect dataSet))
parametricFixedPointStability dataSet =
  absorbContractedPlusDefect dataSet
    (QIF.contractionFactor (leftBall dataSet))
    (QIF.distance (metric dataSet)
      (leftPoint dataSet) (rightPoint dataSet))
    (defect dataSet)
    (QIF.contractionFactorBelowOne (leftBall dataSet))
    (fixedPointDistanceBelowContractedPlusDefect dataSet)

------------------------------------------------------------------------
-- CMP116 specialization: construct R364 H_subScale from the contraction.
------------------------------------------------------------------------

record CMP116SubstitutionContractionData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    sourceLipschitz : ℝ
    sourceSubstitutionDistance : ℝ

    boundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    sourceLipschitzNonnegative : 0ℝ ≤ℝ sourceLipschitz
    boundarySubstitutionDistanceNonnegative :
      ∀ s → 0ℝ ≤ℝ boundarySubstitutionDistance s
    sourceSubstitutionDistanceNonnegative :
      0ℝ ≤ℝ sourceSubstitutionDistance

    -- H_local is passed through unchanged.  R365 only attacks H_subScale.
    boundaryHessianStable :
      ∀ s →
      Cauchy.normValue (Decoupled.cauchy decoupled)
        (Cauchy._-Value_ (Decoupled.cauchy decoupled)
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled leftDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s))
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled rightDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        ≤ℝ
      sourceLipschitz *ℝ boundarySubstitutionDistance s

    SubstitutedBackground : Set

    contractionAt :
      ∀ s → ParametricFixedPointStabilityData SubstitutedBackground ℝ

    -- Same-object weld: the metric distance between the two contractive
    -- fixed points is literally the boundary substitution distance consumed by
    -- the existing decoupled-Hessian theorem.
    fixedPointDistanceIsBoundarySubstitution :
      ∀ s →
      QIF.distance (metric (contractionAt s))
        (leftPoint (contractionAt s))
        (rightPoint (contractionAt s))
      ≡ boundarySubstitutionDistance s

    -- The generic metric relation must be the ordinary real order for the
    -- instantiated source payment; we need only this one direction.
    contractionOrderToReal :
      ∀ s {left right} →
      QIF.LessEqual (metric (contractionAt s)) left right →
      left ≤ℝ right

    -- The one-step forcing defect, after scalar contraction absorption, fits
    -- the one source scale consumed by R364.
    amplifiedDefectBelowSourceDistance :
      ∀ s →
      QIF.multiply (metric (contractionAt s))
        (amplification (contractionAt s))
        (defect (contractionAt s))
      ≤ℝ sourceSubstitutionDistance

open CMP116SubstitutionContractionData public

boundarySubstitutionBelowSourceDistanceFromContraction :
  (dataSet : CMP116SubstitutionContractionData) →
  ∀ s →
  boundarySubstitutionDistance dataSet s
    ≤ℝ sourceSubstitutionDistance dataSet
boundarySubstitutionBelowSourceDistanceFromContraction dataSet s =
  subst
    (λ left → left ≤ℝ sourceSubstitutionDistance dataSet)
    (fixedPointDistanceIsBoundarySubstitution dataSet s)
    (≤ℝ-trans
      (contractionOrderToReal dataSet s
        (parametricFixedPointStability (contractionAt dataSet s)))
      (amplifiedDefectBelowSourceDistance dataSet s))

round365ToR364 :
  CMP116SubstitutionContractionData →
  R364.CMP116DirectSubstitutionStabilityData
round365ToR364 dataSet = record
  { decoupled = decoupled dataSet
  ; leftDomain = leftDomain dataSet
  ; rightDomain = rightDomain dataSet
  ; component = component dataSet
  ; leftVariation = leftVariation dataSet
  ; rightVariation = rightVariation dataSet
  ; sourceLipschitz = sourceLipschitz dataSet
  ; sourceSubstitutionDistance = sourceSubstitutionDistance dataSet
  ; boundarySubstitutionDistance = boundarySubstitutionDistance dataSet
  ; sourceLipschitzNonnegative = sourceLipschitzNonnegative dataSet
  ; boundarySubstitutionDistanceNonnegative =
      boundarySubstitutionDistanceNonnegative dataSet
  ; sourceSubstitutionDistanceNonnegative =
      sourceSubstitutionDistanceNonnegative dataSet
  ; boundaryHessianStable = boundaryHessianStable dataSet
  ; boundarySubstitutionBelowSourceDistance =
      boundarySubstitutionBelowSourceDistanceFromContraction dataSet
  }

round365DirectR352Source :
  (dataSet : CMP116SubstitutionContractionData) →
  R352.CMP116LocalHessianStabilitySource ℝ
round365DirectR352Source dataSet =
  R364.round364ToR352Source (round365ToR364 dataSet)

------------------------------------------------------------------------
-- Pareto boundary.
------------------------------------------------------------------------

fullTwoSolutionSubstitutionScalePrimitive : Bool
fullTwoSolutionSubstitutionScalePrimitive = false

fullTwoSolutionSubstitutionScalePrimitiveIsFalse :
  fullTwoSolutionSubstitutionScalePrimitive ≡ false
fullTwoSolutionSubstitutionScalePrimitiveIsFalse = refl

oneStepCMP116MapDefectIsFirstSourceCoordinate : Bool
oneStepCMP116MapDefectIsFirstSourceCoordinate = true

oneStepCMP116MapDefectIsFirstSourceCoordinateIsTrue :
  oneStepCMP116MapDefectIsFirstSourceCoordinate ≡ true
oneStepCMP116MapDefectIsFirstSourceCoordinateIsTrue = refl

commonInvariantBallStillRequired : Bool
commonInvariantBallStillRequired = true

commonInvariantBallStillRequiredIsTrue :
  commonInvariantBallStillRequired ≡ true
commonInvariantBallStillRequiredIsTrue = refl

scalarContractionAbsorptionSeparateFromYMPhysics : Bool
scalarContractionAbsorptionSeparateFromYMPhysics = true

scalarContractionAbsorptionSeparateFromYMPhysicsIsTrue :
  scalarContractionAbsorptionSeparateFromYMPhysics ≡ true
scalarContractionAbsorptionSeparateFromYMPhysicsIsTrue = refl

parametricFixedPointPerturbationCompilerLevel : ProofLevel
parametricFixedPointPerturbationCompilerLevel = machineChecked

literalCMP116CriticalMapAttachmentLevel : ProofLevel
literalCMP116CriticalMapAttachmentLevel = conditional

literalCMP116OneStepMapDefectLevel : ProofLevel
literalCMP116OneStepMapDefectLevel = conditional

literalCMP116CommonInvariantBallLevel : ProofLevel
literalCMP116CommonInvariantBallLevel = conditional

round365ToR364CompilerLevel : ProofLevel
round365ToR364CompilerLevel = machineChecked

record Round365Boundary : Set where
  constructor round365-boundary
  field
    hSubScaleNoLongerPrimitive : Bool
    hSubScaleNoLongerPrimitiveIsTrue :
      hSubScaleNoLongerPrimitive ≡ true

    oneStepDefectStillPhysical : Bool
    oneStepDefectStillPhysicalIsTrue :
      oneStepDefectStillPhysical ≡ true

    sameObjectCriticalMapAttachmentStillPhysical : Bool
    sameObjectCriticalMapAttachmentStillPhysicalIsTrue :
      sameObjectCriticalMapAttachmentStillPhysical ≡ true

    hLocalStillIndependent : Bool
    hLocalStillIndependentIsTrue :
      hLocalStillIndependent ≡ true

canonicalRound365Boundary : Round365Boundary
canonicalRound365Boundary =
  round365-boundary true refl true refl true refl true refl

round365FrontierRefinementLevel : ProofLevel
round365FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116BoundaryScalarizationFactorRound386Exact where

------------------------------------------------------------------------
-- ROUND386 / FACTOR THE LAST R385 SCALARIZATION THROUGH POINTWISE IDENTITY
--
-- R385 leaves one proof-bearing equality:
--
--   Cauchy boundary norm of the two decoupled Hessian integrands
--     = target metric between two literal R103 marked-Hessian values.
--
-- That equality is not a new Yang--Mills estimate.  It factors through the
-- pointwise same-object identification of each boundary evaluation with the
-- corresponding literal R103 Hessian value.  This owner makes that factorization
-- explicit and then descends one level further through the generic historical
-- theorem `evaluatesAsHessianIntegrand`.
--
-- The remaining source-facing coordinate is therefore the actual same-object
-- statement at HessianValue level:
--
--   secondVariation (decoupledActivity ... selected assignment) u v
--     = literalHessianAsDecoupledValue (R103.cmp116PhysicalMarkedHessian ...).
--
-- No Lipschitz, clustering, spectral-gap, or continuum estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as R103
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373

Boundary :
  (D : Decoupled.DecoupledActivityHessianData) →
  Decoupled.Component D → Set
Boundary D Y =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy D)
    (Decoupled.componentIndices D Y)

------------------------------------------------------------------------
-- First factorization: two pointwise evaluation welds imply the whole norm weld.
------------------------------------------------------------------------

record LiteralBoundaryEvaluationData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData
    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier

    leftLiteralBackground rightLiteralBackground :
      Boundary decoupled component → Source.Background (R103.source literal)
    leftLiteralTangent rightLiteralTangent :
      Boundary decoupled component → Source.Tangent (R103.source literal)

    literalHessianToCauchyValue :
      ℝ → Cauchy.Value (Decoupled.cauchy decoupled)

    leftBoundaryEvaluationIsLiteralHessian :
      ∀ s →
      Cauchy.evaluate (Decoupled.cauchy decoupled)
        (Decoupled.asFunction decoupled leftDomain component
          leftVariation rightVariation)
        (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)
      ≡
      literalHessianToCauchyValue
        (R103.cmp116PhysicalMarkedHessian literal
          (leftLiteralBackground s)
          (leftLiteralTangent s) (rightLiteralTangent s))

    rightBoundaryEvaluationIsLiteralHessian :
      ∀ s →
      Cauchy.evaluate (Decoupled.cauchy decoupled)
        (Decoupled.asFunction decoupled rightDomain component
          leftVariation rightVariation)
        (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)
      ≡
      literalHessianToCauchyValue
        (R103.cmp116PhysicalMarkedHessian literal
          (rightLiteralBackground s)
          (leftLiteralTangent s) (rightLiteralTangent s))

open LiteralBoundaryEvaluationData public

literalHessianDistance :
  (dataSet : LiteralBoundaryEvaluationData) → ℝ → ℝ → ℝ
literalHessianDistance dataSet left right =
  Cauchy.normValue (Decoupled.cauchy (decoupled dataSet))
    (Cauchy._-Value_ (Decoupled.cauchy (decoupled dataSet))
      (literalHessianToCauchyValue dataSet left)
      (literalHessianToCauchyValue dataSet right))

boundaryNormIsLiteralHessianDistance :
  (dataSet : LiteralBoundaryEvaluationData) →
  ∀ s →
  R373.boundaryNormDifference
    (decoupled dataSet)
    (leftDomain dataSet) (rightDomain dataSet)
    (component dataSet)
    (leftVariation dataSet) (rightVariation dataSet) s
  ≡
  literalHessianDistance dataSet
    (R103.cmp116PhysicalMarkedHessian (literal dataSet)
      (leftLiteralBackground dataSet s)
      (leftLiteralTangent dataSet s) (rightLiteralTangent dataSet s))
    (R103.cmp116PhysicalMarkedHessian (literal dataSet)
      (rightLiteralBackground dataSet s)
      (leftLiteralTangent dataSet s) (rightLiteralTangent dataSet s))
boundaryNormIsLiteralHessianDistance dataSet s
  rewrite leftBoundaryEvaluationIsLiteralHessian dataSet s
        | rightBoundaryEvaluationIsLiteralHessian dataSet s = refl

------------------------------------------------------------------------
-- Second factorization: generic evaluatesAsHessianIntegrand + one physical
-- HessianValue same-object weld constructs the pointwise evaluation welds.
------------------------------------------------------------------------

record DecoupledLiteralHessianAttachment : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData
    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    literal : R103.LiteralDifferentiatedEffectiveDensityCarrier

    leftLiteralBackground rightLiteralBackground :
      Boundary decoupled component → Source.Background (R103.source literal)
    leftLiteralTangent rightLiteralTangent :
      Boundary decoupled component → Source.Tangent (R103.source literal)

    literalHessianAsDecoupledHessianValue :
      ℝ → Decoupled.HessianValue decoupled

    -- These are the genuine source-facing same-object receipts after R386.
    leftDecoupledSecondVariationIsLiteral :
      ∀ s →
      Decoupled.secondVariation decoupled
        (Decoupled.decoupledActivity decoupled leftDomain component
          (Decoupled.assignmentFromCauchy decoupled leftDomain component
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        leftVariation rightVariation
      ≡
      literalHessianAsDecoupledHessianValue
        (R103.cmp116PhysicalMarkedHessian literal
          (leftLiteralBackground s)
          (leftLiteralTangent s) (rightLiteralTangent s))

    rightDecoupledSecondVariationIsLiteral :
      ∀ s →
      Decoupled.secondVariation decoupled
        (Decoupled.decoupledActivity decoupled rightDomain component
          (Decoupled.assignmentFromCauchy decoupled rightDomain component
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        leftVariation rightVariation
      ≡
      literalHessianAsDecoupledHessianValue
        (R103.cmp116PhysicalMarkedHessian literal
          (rightLiteralBackground s)
          (leftLiteralTangent s) (rightLiteralTangent s))

open DecoupledLiteralHessianAttachment public

asBoundaryEvaluationData :
  DecoupledLiteralHessianAttachment → LiteralBoundaryEvaluationData
asBoundaryEvaluationData dataSet = record
  { LiteralBoundaryEvaluationData.decoupled = decoupled dataSet
  ; LiteralBoundaryEvaluationData.leftDomain = leftDomain dataSet
  ; LiteralBoundaryEvaluationData.rightDomain = rightDomain dataSet
  ; LiteralBoundaryEvaluationData.component = component dataSet
  ; LiteralBoundaryEvaluationData.leftVariation = leftVariation dataSet
  ; LiteralBoundaryEvaluationData.rightVariation = rightVariation dataSet
  ; LiteralBoundaryEvaluationData.literal = literal dataSet
  ; LiteralBoundaryEvaluationData.leftLiteralBackground = leftLiteralBackground dataSet
  ; LiteralBoundaryEvaluationData.rightLiteralBackground = rightLiteralBackground dataSet
  ; LiteralBoundaryEvaluationData.leftLiteralTangent = leftLiteralTangent dataSet
  ; LiteralBoundaryEvaluationData.rightLiteralTangent = rightLiteralTangent dataSet
  ; LiteralBoundaryEvaluationData.literalHessianToCauchyValue =
      λ h → Decoupled.hessianValue (decoupled dataSet)
        (literalHessianAsDecoupledHessianValue dataSet h)
  ; LiteralBoundaryEvaluationData.leftBoundaryEvaluationIsLiteralHessian =
      λ s → trans
        (Decoupled.evaluatesAsHessianIntegrand
          (decoupled dataSet)
          (leftDomain dataSet) (component dataSet)
          (leftVariation dataSet) (rightVariation dataSet)
          (Cauchy.boundaryAssignment (Decoupled.cauchy (decoupled dataSet)) s))
        (cong (Decoupled.hessianValue (decoupled dataSet))
          (leftDecoupledSecondVariationIsLiteral dataSet s))
  ; LiteralBoundaryEvaluationData.rightBoundaryEvaluationIsLiteralHessian =
      λ s → trans
        (Decoupled.evaluatesAsHessianIntegrand
          (decoupled dataSet)
          (rightDomain dataSet) (component dataSet)
          (leftVariation dataSet) (rightVariation dataSet)
          (Cauchy.boundaryAssignment (Decoupled.cauchy (decoupled dataSet)) s))
        (cong (Decoupled.hessianValue (decoupled dataSet))
          (rightDecoupledSecondVariationIsLiteral dataSet s))
  }

scalarizationFromLiteralActivityAttachment :
  (dataSet : DecoupledLiteralHessianAttachment) →
  ∀ s →
  R373.boundaryNormDifference
    (decoupled dataSet)
    (leftDomain dataSet) (rightDomain dataSet)
    (component dataSet)
    (leftVariation dataSet) (rightVariation dataSet) s
  ≡
  literalHessianDistance (asBoundaryEvaluationData dataSet)
    (R103.cmp116PhysicalMarkedHessian (literal dataSet)
      (leftLiteralBackground dataSet s)
      (leftLiteralTangent dataSet s) (rightLiteralTangent dataSet s))
    (R103.cmp116PhysicalMarkedHessian (literal dataSet)
      (rightLiteralBackground dataSet s)
      (leftLiteralTangent dataSet s) (rightLiteralTangent dataSet s))
scalarizationFromLiteralActivityAttachment dataSet =
  boundaryNormIsLiteralHessianDistance (asBoundaryEvaluationData dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round386ScalarizationFactorCompilerLevel : ProofLevel
round386ScalarizationFactorCompilerLevel = machineChecked

wholeBoundaryNormScalarizationPrimitiveAfterRound386 : Bool
wholeBoundaryNormScalarizationPrimitiveAfterRound386 = false

wholeBoundaryNormScalarizationPrimitiveAfterRound386IsFalse :
  wholeBoundaryNormScalarizationPrimitiveAfterRound386 ≡ false
wholeBoundaryNormScalarizationPrimitiveAfterRound386IsFalse = refl

literalDecoupledSecondVariationAttachmentStillRequired : Bool
literalDecoupledSecondVariationAttachmentStillRequired = true

literalDecoupledSecondVariationAttachmentStillRequiredIsTrue :
  literalDecoupledSecondVariationAttachmentStillRequired ≡ true
literalDecoupledSecondVariationAttachmentStillRequiredIsTrue = refl

record Round386Boundary : Set where
  constructor round386-boundary
  field
    genericEvaluationIdentityReused : Bool
    genericEvaluationIdentityReusedIsTrue : genericEvaluationIdentityReused ≡ true

    scalarizationReducedToPointwiseSameObject : Bool
    scalarizationReducedToPointwiseSameObjectIsTrue :
      scalarizationReducedToPointwiseSameObject ≡ true

    noNewAnalyticInequalityIntroduced : Bool
    noNewAnalyticInequalityIntroducedIsTrue :
      noNewAnalyticInequalityIntroduced ≡ true

canonicalRound386Boundary : Round386Boundary
canonicalRound386Boundary =
  round386-boundary true refl true refl true refl

round386FrontierRefinementLevel : ProofLevel
round386FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

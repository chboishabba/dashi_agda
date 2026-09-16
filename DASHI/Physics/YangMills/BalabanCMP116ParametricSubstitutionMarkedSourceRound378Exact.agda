{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ParametricSubstitutionMarkedSourceRound378Exact where

------------------------------------------------------------------------
-- ROUND378 / R370 ALREADY MANUFACTURES THE R351 SOURCE INEQUALITY
--
-- R351 exposed the source-facing H_sub theorem as
--
--   d_sub^src(s) <= M_marked^src.
--
-- On the preferred direct parametric route this inequality is no longer a
-- primitive analytic leaf.  R370 already proves, from one source-native CMP116
-- analytic fixed-point family plus ordinary Cauchy sensitivity,
--
--   boundarySubstitutionDistance(s)
--     <= sourceParametricLipschitz * sourceParameterDistance.
--
-- This owner packages that existing theorem directly as R351's proof-bearing
-- source ABI.  It does NOT identify the resulting upper coordinate with any
-- older CMP99/marked-walk semantic quantity.  Such an identity would be a
-- separate same-object theorem and is not needed by the present H_sub consumer.
--
-- Hence the direct path is now
--
--   CMP116 published parametric family (R371)
--     -> generic Cauchy sensitivity (R370)
--     -> R351 source H_sub package (R378)
--     -> canonical selected-distance attachment (R377)
--     -> R376 -> R375 marked Hessian coefficient payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanSelectedSubstitutionMarkedSourceRound351Exact as R351

------------------------------------------------------------------------
-- R370 and R351 use the same boundary-assignment shape.
------------------------------------------------------------------------

ParametricBoundaryPoint :
  R370.CMP116DirectParametricSensitivityData → Set
ParametricBoundaryPoint dataSet =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R370.decoupled dataSet))
    (Decoupled.componentIndices
      (R370.decoupled dataSet)
      (R370.component dataSet))

------------------------------------------------------------------------
-- Direct compiler: no new inequality is assumed.
------------------------------------------------------------------------

parametricSensitivityToR351Source :
  (dataSet : R370.CMP116DirectParametricSensitivityData) →
  R351.CMP116SubstitutionMarkedSource (ParametricBoundaryPoint dataSet)
parametricSensitivityToR351Source dataSet = record
  { R351.sourceSubstitutionDistance =
      R370.boundarySubstitutionDistance dataSet
  ; R351.sourceMarkedInput =
      R370.sourceSubstitutionDistance dataSet
  ; R351.sourceDistanceNonnegative =
      R370.boundarySubstitutionDistanceNonnegativeFromParametric dataSet
  ; R351.sourceMarkedInputNonnegative =
      R370.sourceSubstitutionDistanceNonnegativeFromParametric dataSet
  ; R351.sourceSubstitutionMarked =
      R370.boundarySubstitutionBelowSourceDistanceFromParametric dataSet
  }

r378SourceDistance :
  (dataSet : R370.CMP116DirectParametricSensitivityData) →
  ParametricBoundaryPoint dataSet →
  DASHI.Foundations.RealAnalysisAxioms.ℝ
r378SourceDistance dataSet =
  R351.sourceSubstitutionDistance
    (parametricSensitivityToR351Source dataSet)

r378MarkedUpper :
  (dataSet : R370.CMP116DirectParametricSensitivityData) →
  DASHI.Foundations.RealAnalysisAxioms.ℝ
r378MarkedUpper dataSet =
  R351.sourceMarkedInput
    (parametricSensitivityToR351Source dataSet)

r378SourcePayment :
  (dataSet : R370.CMP116DirectParametricSensitivityData) →
  ∀ s →
  DASHI.Foundations.RealAnalysisAxioms._≤ℝ_
    (r378SourceDistance dataSet s)
    (r378MarkedUpper dataSet)
r378SourcePayment dataSet =
  R351.sourceSubstitutionMarked
    (parametricSensitivityToR351Source dataSet)

------------------------------------------------------------------------
-- Pareto / WrongType boundary.
------------------------------------------------------------------------

round378ParametricToR351CompilerLevel : ProofLevel
round378ParametricToR351CompilerLevel = machineChecked

r351SourceInequalityPrimitiveOnDirectParametricRoute : Bool
r351SourceInequalityPrimitiveOnDirectParametricRoute = false

r351SourceInequalityPrimitiveOnDirectParametricRouteIsFalse :
  r351SourceInequalityPrimitiveOnDirectParametricRoute ≡ false
r351SourceInequalityPrimitiveOnDirectParametricRouteIsFalse = refl

directParametricHSubProducerAvailable : Bool
directParametricHSubProducerAvailable = true

directParametricHSubProducerAvailableIsTrue :
  directParametricHSubProducerAvailable ≡ true
directParametricHSubProducerAvailableIsTrue = refl

historicalMarkedInputIdentityAutomaticallyProved : Bool
historicalMarkedInputIdentityAutomaticallyProved = false

historicalMarkedInputIdentityAutomaticallyProvedIsFalse :
  historicalMarkedInputIdentityAutomaticallyProved ≡ false
historicalMarkedInputIdentityAutomaticallyProvedIsFalse = refl

r353MarkedWalkScaleMandatoryAfterRound378 : Bool
r353MarkedWalkScaleMandatoryAfterRound378 = false

r353MarkedWalkScaleMandatoryAfterRound378IsFalse :
  r353MarkedWalkScaleMandatoryAfterRound378 ≡ false
r353MarkedWalkScaleMandatoryAfterRound378IsFalse = refl

record Round378Boundary : Set where
  constructor round378-boundary
  field
    r370ConstructsR351SourceUpper : Bool
    r370ConstructsR351SourceUpperIsTrue :
      r370ConstructsR351SourceUpper ≡ true

    sourceInequalityNoLongerIndependent : Bool
    sourceInequalityNoLongerIndependentIsTrue :
      sourceInequalityNoLongerIndependent ≡ true

    sameObjectBoundaryAttachmentStillRequired : Bool
    sameObjectBoundaryAttachmentStillRequiredIsTrue :
      sameObjectBoundaryAttachmentStillRequired ≡ true

    sourceFamilyDomainRadiusCalibrationStillRequired : Bool
    sourceFamilyDomainRadiusCalibrationStillRequiredIsTrue :
      sourceFamilyDomainRadiusCalibrationStillRequired ≡ true

    historicalMarkIdentityNotManufactured : Bool
    historicalMarkIdentityNotManufacturedIsTrue :
      historicalMarkIdentityNotManufactured ≡ true

canonicalRound378Boundary : Round378Boundary
canonicalRound378Boundary =
  round378-boundary
    true refl
    true refl
    true refl
    true refl
    true refl

round378FrontierRefinementLevel : ProofLevel
round378FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

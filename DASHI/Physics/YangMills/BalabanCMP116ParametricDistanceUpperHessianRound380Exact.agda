{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116ParametricDistanceUpperHessianRound380Exact where

------------------------------------------------------------------------
-- ROUND380 / R370 PARAMETRIC UPPER -> R379 COEFFICIENT CONSUMER
--
-- R379 showed that the downstream Hessian-coefficient consumer only needs a
-- proof-bearing upper U on the selected substitution distance.  R370 already
-- manufactures
--
--   U_par = L_par * d_parameter
--
-- and proves its own boundary fixed-point distance is <= U_par.
--
-- Therefore the only additional coordinate required to feed R379 is a
-- same-object boundary map identifying R373's selected distance with R370's
-- boundary distance.  No historical marked-input scalar is needed on this
-- preferred coefficient route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373
import DASHI.Physics.YangMills.BalabanCMP116DistanceUpperHessianBidiRound379Exact as R379

R373Boundary : R373.JointBoundaryHessianPaymentData → Set
R373Boundary joint =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R373.decoupled joint))
    (Decoupled.componentIndices
      (R373.decoupled joint)
      (R373.component joint))

R370Boundary : R370.CMP116DirectParametricSensitivityData → Set
R370Boundary parametric =
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy (R370.decoupled parametric))
    (Decoupled.componentIndices
      (R370.decoupled parametric)
      (R370.component parametric))

record CMP116ParametricDistanceUpperHessianData : Set₁ where
  field
    joint : R373.JointBoundaryHessianPaymentData
    parametric : R370.CMP116DirectParametricSensitivityData

    jointBoundaryToParametricBoundary :
      R373Boundary joint → R370Boundary parametric

    selectedDistanceIsParametricBoundaryDistance :
      ∀ s →
      R373.selectedBoundarySubstitutionDistance joint s ≡
      R370.boundarySubstitutionDistance parametric
        (jointBoundaryToParametricBoundary s)

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R373.selectedLipschitz joint

open CMP116ParametricDistanceUpperHessianData public

selectedDistanceNonnegativeFromParametric :
  (dataSet : CMP116ParametricDistanceUpperHessianData) →
  ∀ s → 0ℝ ≤ℝ R373.selectedBoundarySubstitutionDistance (joint dataSet) s
selectedDistanceNonnegativeFromParametric dataSet s =
  subst
    (λ distance → 0ℝ ≤ℝ distance)
    (sym (selectedDistanceIsParametricBoundaryDistance dataSet s))
    (R370.boundarySubstitutionDistanceNonnegativeFromParametric
      (parametric dataSet)
      (jointBoundaryToParametricBoundary dataSet s))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

selectedDistanceBelowParametricUpper :
  (dataSet : CMP116ParametricDistanceUpperHessianData) →
  ∀ s →
  R373.selectedBoundarySubstitutionDistance (joint dataSet) s
    ≤ℝ R370.sourceSubstitutionDistance (parametric dataSet)
selectedDistanceBelowParametricUpper dataSet s =
  subst
    (λ distance →
      distance ≤ℝ R370.sourceSubstitutionDistance (parametric dataSet))
    (sym (selectedDistanceIsParametricBoundaryDistance dataSet s))
    (R370.boundarySubstitutionBelowSourceDistanceFromParametric
      (parametric dataSet)
      (jointBoundaryToParametricBoundary dataSet s))
  where
  open import Relation.Binary.PropositionalEquality using (sym)

asRound379 :
  CMP116ParametricDistanceUpperHessianData →
  R379.CMP116DistanceUpperHessianBidiData
asRound379 dataSet = record
  { joint = joint dataSet
  ; distanceUpper = R370.sourceSubstitutionDistance (parametric dataSet)
  ; distanceUpperNonnegative =
      R370.sourceSubstitutionDistanceNonnegativeFromParametric
        (parametric dataSet)
  ; selectedBoundaryDistanceNonnegative =
      selectedDistanceNonnegativeFromParametric dataSet
  ; selectedLipschitzNonnegative = selectedLipschitzNonnegative dataSet
  ; selectedBoundaryDistanceBelowUpper =
      selectedDistanceBelowParametricUpper dataSet
  }

selectedCoefficientDifferenceFromParametricUpper :
  (dataSet : CMP116ParametricDistanceUpperHessianData) →
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
  R373.selectedLipschitz (joint dataSet) R379.*ℝ
    R370.sourceSubstitutionDistance (parametric dataSet)
selectedCoefficientDifferenceFromParametricUpper dataSet =
  R379.selectedCoefficientDifferenceBelowDistanceUpper (asRound379 dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round380ParametricCoefficientCompilerLevel : ProofLevel
round380ParametricCoefficientCompilerLevel = machineChecked

historicalMarkedCalibrationMandatoryAfterRound380 : Bool
historicalMarkedCalibrationMandatoryAfterRound380 = false

historicalMarkedCalibrationMandatoryAfterRound380IsFalse :
  historicalMarkedCalibrationMandatoryAfterRound380 ≡ false
historicalMarkedCalibrationMandatoryAfterRound380IsFalse = refl

selectedBoundarySameObjectMapStillRequired : Bool
selectedBoundarySameObjectMapStillRequired = true

selectedBoundarySameObjectMapStillRequiredIsTrue :
  selectedBoundarySameObjectMapStillRequired ≡ true
selectedBoundarySameObjectMapStillRequiredIsTrue = refl

record Round380Boundary : Set where
  constructor round380-boundary
  field
    r370UpperFeedsR379Directly : Bool
    r370UpperFeedsR379DirectlyIsTrue :
      r370UpperFeedsR379Directly ≡ true

    r351R378HistoricalMarkRouteStillValid : Bool
    r351R378HistoricalMarkRouteStillValidIsTrue :
      r351R378HistoricalMarkRouteStillValid ≡ true

    r351R378HistoricalMarkRouteMandatoryForCoefficient : Bool
    r351R378HistoricalMarkRouteMandatoryForCoefficientIsFalse :
      r351R378HistoricalMarkRouteMandatoryForCoefficient ≡ false

    sameObjectBoundaryTransportStillProofBearing : Bool
    sameObjectBoundaryTransportStillProofBearingIsTrue :
      sameObjectBoundaryTransportStillProofBearing ≡ true

canonicalRound380Boundary : Round380Boundary
canonicalRound380Boundary =
  round380-boundary true refl true refl false refl true refl

round380FrontierRefinementLevel : ProofLevel
round380FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false

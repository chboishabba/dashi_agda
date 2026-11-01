module DASHI.Physics.YangMills.BalabanCMP116DirectHessianParameterUpperRound382Exact where

------------------------------------------------------------------------
-- ROUND382 / REMOVE THE R372 INTERMEDIATE DISTANCE COORDINATE
--
-- R381 weakened R380's exact distance equality to
--
--   d_Hessian^R372(s) <= U_par^R370.
--
-- But R372's `sourceSubstitutionDistance` is itself only an upper coordinate
-- for the actual parameter distance consumed by the Cauchy theorem.  The
-- coefficient lift does not need that intermediate scalar either.
--
-- The least-privilege route is therefore:
--
--   actual Hessian-family parameter distance <= U_par^R370
--   + selected Hessian family / scalarization
--   + Cauchy parametric sensitivity
--   -------------------------------------------------------
--   literal boundary Hessian difference <= L_Hessian * U_par
--   -------------------------------------------------------
--   coefficient Hessian difference <= L_Hessian * U_par.
--
-- The coefficient theorem is instantiated with the constant substitution
-- distance d(s) := U_par, so its final `d(s) <= markedInput` premise is just
-- real-order reflexivity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373

record CMP116DirectHessianParameterUpperData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    hessian : R372.CMP116DirectHessianSensitivityData
    parametric : R370.CMP116DirectParametricSensitivityData

    boundaryToHessianBoundary :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) →
      R372.Boundary hessian

    hessianDifferenceIsBoundaryNorm :
      ∀ s →
      R372.sourceHessianDifference hessian
        (boundaryToHessianBoundary s)
      ≡
      R373.boundaryNormDifference decoupled leftDomain rightDomain component
        leftVariation rightVariation s

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R372.sourceHessianLipschitz hessian

    -- Actual Cauchy-consumed parameter distance, with no R372 auxiliary upper.
    hessianParameterDistanceBelowParametricUpper :
      ∀ s →
      R370.parameterDistance (R372.sensitivity hessian)
        (R372.leftSubstituted hessian (boundaryToHessianBoundary s))
        (R372.rightSubstituted hessian (boundaryToHessianBoundary s))
      ≤ℝ R370.sourceSubstitutionDistance parametric

open CMP116DirectHessianParameterUpperData public

boundaryHessianStableFromActualParameterUpper :
  (dataSet : CMP116DirectHessianParameterUpperData) →
  ∀ s →
  R373.boundaryNormDifference
      (decoupled dataSet)
      (leftDomain dataSet)
      (rightDomain dataSet)
      (component dataSet)
      (leftVariation dataSet)
      (rightVariation dataSet)
      s
    ≤ℝ
  R372.sourceHessianLipschitz (hessian dataSet) *ℝ
    R370.sourceSubstitutionDistance (parametric dataSet)
boundaryHessianStableFromActualParameterUpper dataSet s
  rewrite sym (hessianDifferenceIsBoundaryNorm dataSet s)
        | R372.sourceHessianDifferenceIsTargetDistance
            (hessian dataSet) (boundaryToHessianBoundary dataSet s) =
  R370.cauchySensitivityWithDistanceUpper
    (R372.sensitivity (hessian dataSet))
    (R372.hessianFamily (hessian dataSet)
      (boundaryToHessianBoundary dataSet s))
    (R372.sourceMagnitudeBound (hessian dataSet))
    (R372.sourceRadius (hessian dataSet))
    (R372.leftSubstituted (hessian dataSet)
      (boundaryToHessianBoundary dataSet s))
    (R372.rightSubstituted (hessian dataSet)
      (boundaryToHessianBoundary dataSet s))
    (R370.sourceSubstitutionDistance (parametric dataSet))
    (R372.sourceHessianAnalytic (hessian dataSet)
      (boundaryToHessianBoundary dataSet s))
    (R372.sourceHessianUniformlyBounded (hessian dataSet)
      (boundaryToHessianBoundary dataSet s))
    (R372.sourceRadiusPositive (hessian dataSet))
    (R372.selectedSubstitutedBackgroundsShareNeighbourhood
      (hessian dataSet) (boundaryToHessianBoundary dataSet s))
    (hessianParameterDistanceBelowParametricUpper dataSet s)

selectedCoefficientDifferenceBelowParametricUpper :
  (dataSet : CMP116DirectHessianParameterUpperData) →
  Cauchy.normValue
    (Decoupled.cauchy (decoupled dataSet))
    (Cauchy._-Value_
      (Decoupled.cauchy (decoupled dataSet))
      (Decoupled.decoupledHessianCoefficient
        (decoupled dataSet)
        (leftDomain dataSet)
        (component dataSet)
        (leftVariation dataSet)
        (rightVariation dataSet))
      (Decoupled.decoupledHessianCoefficient
        (decoupled dataSet)
        (rightDomain dataSet)
        (component dataSet)
        (leftVariation dataSet)
        (rightVariation dataSet)))
  ≤ℝ
  R372.sourceHessianLipschitz (hessian dataSet) *ℝ
    R370.sourceSubstitutionDistance (parametric dataSet)
selectedCoefficientDifferenceBelowParametricUpper dataSet =
  Decoupled.markedSubstitutionStabilityLiftsToCoefficient
    (decoupled dataSet)
    (leftDomain dataSet)
    (rightDomain dataSet)
    (component dataSet)
    (leftVariation dataSet)
    (rightVariation dataSet)
    (R372.sourceHessianLipschitz (hessian dataSet))
    (R370.sourceSubstitutionDistance (parametric dataSet))
    (λ _ → R370.sourceSubstitutionDistance (parametric dataSet))
    (selectedLipschitzNonnegative dataSet)
    (λ _ →
      R370.sourceSubstitutionDistanceNonnegativeFromParametric
        (parametric dataSet))
    (R370.sourceSubstitutionDistanceNonnegativeFromParametric
      (parametric dataSet))
    (boundaryHessianStableFromActualParameterUpper dataSet)
    (λ _ → ≤ℝ-refl)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round382ActualParameterCompilerLevel : ProofLevel
round382ActualParameterCompilerLevel = machineChecked

r372AuxiliaryDistanceMandatoryForCoefficient : Bool
r372AuxiliaryDistanceMandatoryForCoefficient = false

r372AuxiliaryDistanceMandatoryForCoefficientIsFalse :
  r372AuxiliaryDistanceMandatoryForCoefficient ≡ false
r372AuxiliaryDistanceMandatoryForCoefficientIsFalse = refl

r380ExactDistanceEqualityMandatoryAfterRound382 : Bool
r380ExactDistanceEqualityMandatoryAfterRound382 = false

r380ExactDistanceEqualityMandatoryAfterRound382IsFalse :
  r380ExactDistanceEqualityMandatoryAfterRound382 ≡ false
r380ExactDistanceEqualityMandatoryAfterRound382IsFalse = refl

actualHessianParameterDistanceUpperStillProofBearing : Bool
actualHessianParameterDistanceUpperStillProofBearing = true

actualHessianParameterDistanceUpperStillProofBearingIsTrue :
  actualHessianParameterDistanceUpperStillProofBearing ≡ true
actualHessianParameterDistanceUpperStillProofBearingIsTrue = refl

record Round382Boundary : Set where
  constructor round382-boundary
  field
    coefficientConsumerSeesActualParameterUpper : Bool
    coefficientConsumerSeesActualParameterUpperIsTrue :
      coefficientConsumerSeesActualParameterUpper ≡ true

    intermediateDistanceCoordinateRemoved : Bool
    intermediateDistanceCoordinateRemovedIsTrue :
      intermediateDistanceCoordinateRemoved ≡ true

    selectedPhysicalHessianAttachmentStillRequired : Bool
    selectedPhysicalHessianAttachmentStillRequiredIsTrue :
      selectedPhysicalHessianAttachmentStillRequired ≡ true

canonicalRound382Boundary : Round382Boundary
canonicalRound382Boundary =
  round382-boundary true refl true refl true refl

round382FrontierRefinementLevel : ProofLevel
round382FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

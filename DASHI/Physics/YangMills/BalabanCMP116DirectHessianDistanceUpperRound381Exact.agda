module DASHI.Physics.YangMills.BalabanCMP116DirectHessianDistanceUpperRound381Exact where

------------------------------------------------------------------------
-- ROUND381 / CONSUMER-FIRST RECUT OF R380
--
-- R380 asks for an exact equality between two distance coordinates:
--
--   d_selected^R373(s) = d_boundary^R370(iota s).
--
-- But the old coefficient lift does not inspect that equality.  It consumes
-- only a pointwise substitution-distance function d(s), its nonnegativity,
-- and a global upper U with d(s) <= U.
--
-- Therefore the least-privilege direct route is:
--
--   R372 pointwise Hessian sensitivity
--   + literal boundary-scalar attachment
--   + d_Hessian(s) <= U_par^R370
--   ------------------------------------------------
--   coefficient Hessian difference <= L_Hessian * U_par^R370.
--
-- This removes the exact R373<->R370 distance equality from the mandatory
-- coefficient route.  It does NOT identify the selected physical families,
-- manufacture the pointwise upper, or claim continuum clustering/mass gap.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372
import DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact as R373

record CMP116DirectHessianDistanceUpperData : Set₁ where
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

    -- Same-object scalarization of the selected Hessian family into the
    -- literal boundary norm consumed by the finite-polydisc coefficient lift.
    hessianDifferenceIsBoundaryNorm :
      ∀ s →
      R372.sourceHessianDifference hessian
        (boundaryToHessianBoundary s)
      ≡
      R373.boundaryNormDifference decoupled leftDomain rightDomain component
        leftVariation rightVariation s

    selectedLipschitzNonnegative :
      0ℝ ≤ℝ R372.sourceHessianLipschitz hessian

    -- This is strictly weaker than R380's exact equality of distance
    -- coordinates.  Only the upper actually observed by the consumer remains.
    hessianDistanceBelowParametricUpper :
      ∀ s →
      R372.sourceSubstitutionDistance hessian
        (boundaryToHessianBoundary s)
      ≤ℝ R370.sourceSubstitutionDistance parametric

open CMP116DirectHessianDistanceUpperData public

boundaryHessianStableFromR372 :
  (dataSet : CMP116DirectHessianDistanceUpperData) →
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
    R372.sourceSubstitutionDistance (hessian dataSet)
      (boundaryToHessianBoundary dataSet s)
boundaryHessianStableFromR372 dataSet s
  rewrite sym (hessianDifferenceIsBoundaryNorm dataSet s) =
  R372.sourceHessianStableFromCauchy
    (hessian dataSet)
    (boundaryToHessianBoundary dataSet s)

selectedCoefficientDifferenceBelowParametricUpper :
  (dataSet : CMP116DirectHessianDistanceUpperData) →
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
    (λ s →
      R372.sourceSubstitutionDistance (hessian dataSet)
        (boundaryToHessianBoundary dataSet s))
    (selectedLipschitzNonnegative dataSet)
    (λ s →
      R372.sourceSubstitutionDistanceNonnegative (hessian dataSet)
        (boundaryToHessianBoundary dataSet s))
    (R370.sourceSubstitutionDistanceNonnegativeFromParametric
      (parametric dataSet))
    (boundaryHessianStableFromR372 dataSet)
    (hessianDistanceBelowParametricUpper dataSet)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round381DirectUpperCompilerLevel : ProofLevel
round381DirectUpperCompilerLevel = machineChecked

r380ExactDistanceEqualityMandatoryForCoefficient : Bool
r380ExactDistanceEqualityMandatoryForCoefficient = false

r380ExactDistanceEqualityMandatoryForCoefficientIsFalse :
  r380ExactDistanceEqualityMandatoryForCoefficient ≡ false
r380ExactDistanceEqualityMandatoryForCoefficientIsFalse = refl

pointwiseHessianDistanceUpperStillProofBearing : Bool
pointwiseHessianDistanceUpperStillProofBearing = true

pointwiseHessianDistanceUpperStillProofBearingIsTrue :
  pointwiseHessianDistanceUpperStillProofBearing ≡ true
pointwiseHessianDistanceUpperStillProofBearingIsTrue = refl

literalHessianScalarizationStillProofBearing : Bool
literalHessianScalarizationStillProofBearing = true

literalHessianScalarizationStillProofBearingIsTrue :
  literalHessianScalarizationStillProofBearing ≡ true
literalHessianScalarizationStillProofBearingIsTrue = refl

record Round381Boundary : Set where
  constructor round381-boundary
  field
    equalityReplacedByConsumerSufficientUpper : Bool
    equalityReplacedByConsumerSufficientUpperIsTrue :
      equalityReplacedByConsumerSufficientUpper ≡ true

    r380HistoricalRouteStillValid : Bool
    r380HistoricalRouteStillValidIsTrue :
      r380HistoricalRouteStillValid ≡ true

    selectedPhysicalFamilyAttachmentStillRequired : Bool
    selectedPhysicalFamilyAttachmentStillRequiredIsTrue :
      selectedPhysicalFamilyAttachmentStillRequired ≡ true

canonicalRound381Boundary : Round381Boundary
canonicalRound381Boundary =
  round381-boundary true refl true refl true refl

round381FrontierRefinementLevel : ProofLevel
round381FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

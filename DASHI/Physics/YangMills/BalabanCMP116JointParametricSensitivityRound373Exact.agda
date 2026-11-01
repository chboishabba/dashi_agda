module DASHI.Physics.YangMills.BalabanCMP116JointParametricSensitivityRound373Exact where

------------------------------------------------------------------------
-- ROUND373 / R372 PAYS R371'S OPAQUE H_local SOCKET
--
-- R371's direct fixed-point sensitivity route still accepted one opaque field
--
--   boundaryHessianStable
--
-- for the orthogonal H_local payment.  R372 has since shown that H_local is
-- itself compiler output from the same generic Cauchy parametric-sensitivity
-- theorem once the selected Hessian family is attached.
--
-- This owner performs only the missing same-object splice.  It does NOT claim
-- that CMP116 source analyticity automatically identifies the selected R352
-- Hessian scalar.  Instead it asks for exactly three equalities:
--
--   * R372 target distance = the literal R371/R364 boundary Hessian norm;
--   * R372 Cauchy Lipschitz constant = the selected R371 source Lipschitz;
--   * R372 substitution-distance coordinate = the selected boundary distance.
--
-- Once those coordinates are welded, the inequality consumed by R371 is
-- compiler-owned.  No separately named H_local theorem remains primitive.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectHessianSensitivityRound372Exact as R372

------------------------------------------------------------------------
-- Literal scalar consumed by the older R364/R370/R371 H_local socket.
------------------------------------------------------------------------

boundaryNormDifference :
  (decoupled : Decoupled.DecoupledActivityHessianData) →
  (leftDomain rightDomain : Decoupled.DomainSequence decoupled) →
  (component : Decoupled.Component decoupled) →
  (leftVariation rightVariation : Decoupled.FieldVariation decoupled) →
  Cauchy.BoundaryAssignment
    (Decoupled.cauchy decoupled)
    (Decoupled.componentIndices decoupled component) →
  ℝ
boundaryNormDifference decoupled leftDomain rightDomain component
  leftVariation rightVariation s =
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

------------------------------------------------------------------------
-- Least-privilege splice from R372 into the literal boundary consumer.
------------------------------------------------------------------------

record JointBoundaryHessianPaymentData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    selectedLipschitz : ℝ
    selectedBoundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    hessian : R372.CMP116DirectHessianSensitivityData

    boundaryToHessianBoundary :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) →
      R372.Boundary hessian

    -- Same-object scalarization only.  This is strictly weaker than asking for
    -- another analytic inequality.
    hessianDifferenceIsBoundaryNorm :
      ∀ s →
      R372.sourceHessianDifference hessian
        (boundaryToHessianBoundary s)
      ≡
      boundaryNormDifference decoupled leftDomain rightDomain component
        leftVariation rightVariation s

    hessianLipschitzIsSelectedLipschitz :
      R372.sourceHessianLipschitz hessian ≡ selectedLipschitz

    hessianDistanceIsSelectedBoundaryDistance :
      ∀ s →
      R372.sourceSubstitutionDistance hessian
        (boundaryToHessianBoundary s)
      ≡ selectedBoundarySubstitutionDistance s

open JointBoundaryHessianPaymentData public

boundaryHessianStableFromR372 :
  (dataSet : JointBoundaryHessianPaymentData) →
  ∀ s →
  boundaryNormDifference
      (decoupled dataSet)
      (leftDomain dataSet)
      (rightDomain dataSet)
      (component dataSet)
      (leftVariation dataSet)
      (rightVariation dataSet)
      s
    ≤ℝ
  selectedLipschitz dataSet *ℝ
    selectedBoundarySubstitutionDistance dataSet s
boundaryHessianStableFromR372 dataSet s
  rewrite sym (hessianDifferenceIsBoundaryNorm dataSet s)
        | sym (hessianLipschitzIsSelectedLipschitz dataSet)
        | sym (hessianDistanceIsSelectedBoundaryDistance dataSet s) =
  R372.sourceHessianStableFromCauchy
    (hessian dataSet)
    (boundaryToHessianBoundary dataSet s)

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round373R372ToR371HLocalCompilerLevel : ProofLevel
round373R372ToR371HLocalCompilerLevel = machineChecked

literalHessianScalarizationAttachmentLevel : ProofLevel
literalHessianScalarizationAttachmentLevel = conditional

literalHessianLipschitzCoordinateAttachmentLevel : ProofLevel
literalHessianLipschitzCoordinateAttachmentLevel = conditional

literalHessianDistanceCoordinateAttachmentLevel : ProofLevel
literalHessianDistanceCoordinateAttachmentLevel = conditional

hLocalOpaquePrimitiveAfterRound373 : Bool
hLocalOpaquePrimitiveAfterRound373 = false

hLocalOpaquePrimitiveAfterRound373IsFalse :
  hLocalOpaquePrimitiveAfterRound373 ≡ false
hLocalOpaquePrimitiveAfterRound373IsFalse = refl

sameObjectScalarizationStillRequiredAfterRound373 : Bool
sameObjectScalarizationStillRequiredAfterRound373 = true

sameObjectScalarizationStillRequiredAfterRound373IsTrue :
  sameObjectScalarizationStillRequiredAfterRound373 ≡ true
sameObjectScalarizationStillRequiredAfterRound373IsTrue = refl

record Round373Boundary : Set where
  constructor round373-boundary
  field
    r372CanPayR371BoundaryHessian : Bool
    r372CanPayR371BoundaryHessianIsTrue :
      r372CanPayR371BoundaryHessian ≡ true

    secondOpaqueHLocalInequalityRequired : Bool
    secondOpaqueHLocalInequalityRequiredIsFalse :
      secondOpaqueHLocalInequalityRequired ≡ false

    sameObjectCoordinateWeldsRemain : Bool
    sameObjectCoordinateWeldsRemainIsTrue :
      sameObjectCoordinateWeldsRemain ≡ true

canonicalRound373Boundary : Round373Boundary
canonicalRound373Boundary =
  round373-boundary true refl false refl true refl

round373FrontierRefinementLevel : ProofLevel
round373FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

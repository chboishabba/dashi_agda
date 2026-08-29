{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: PHYSICAL B-HESSIAN OF A CMP116 LOCAL ACTIVITY
--
-- CMP116 Sect.1 first writes local analytic E(X,U,J,A), then substitutes analytic
-- nonlocal/localized expressions A=A(B) (for example H_k(B')).  Therefore the
-- physical background Hessian is the Hessian of the COMPOSITE E∘A.
--
-- The generic second-order chain rule is
--
--   D_B²(E∘A)[u,v]
--     = D_A²E[A'u,A'v] + D_AE[A''(u,v)].
--
-- The second term is kept explicitly.  It may vanish in a special affine
-- substitution, but no such cancellation is assumed generically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SubstitutedActivitySecondVariation : Set₁ where
  field
    Background LocalCoordinate BackgroundTangent LocalTangent : Set

    localActivity : LocalCoordinate → ℝ
    substitution : Background → LocalCoordinate

    firstActivityVariation : LocalCoordinate → LocalTangent → ℝ
    secondActivityVariation :
      LocalCoordinate → LocalTangent → LocalTangent → ℝ

    firstSubstitutionVariation :
      Background → BackgroundTangent → LocalTangent
    secondSubstitutionVariation :
      Background → BackgroundTangent → BackgroundTangent → LocalTangent

    physicalSecondVariation :
      Background → BackgroundTangent → BackgroundTangent → ℝ

    -- Standard twice-differentiable chain rule on the literal source maps.
    physicalSecondVariationChainRule : ∀ background u v →
      physicalSecondVariation background u v
      ≡ secondActivityVariation
          (substitution background)
          (firstSubstitutionVariation background u)
          (firstSubstitutionVariation background v)
        +ℝ firstActivityVariation
          (substitution background)
          (secondSubstitutionVariation background u v)

open SubstitutedActivitySecondVariation public

intrinsicHessianTerm :
  (dataSet : SubstitutedActivitySecondVariation) →
  Background dataSet → BackgroundTangent dataSet → BackgroundTangent dataSet → ℝ
intrinsicHessianTerm dataSet background u v =
  secondActivityVariation dataSet
    (substitution dataSet background)
    (firstSubstitutionVariation dataSet background u)
    (firstSubstitutionVariation dataSet background v)

substitutionCurvatureTerm :
  (dataSet : SubstitutedActivitySecondVariation) →
  Background dataSet → BackgroundTangent dataSet → BackgroundTangent dataSet → ℝ
substitutionCurvatureTerm dataSet background u v =
  firstActivityVariation dataSet
    (substitution dataSet background)
    (secondSubstitutionVariation dataSet background u v)

physicalHessianSplitsIntrinsicPlusSubstitution :
  (dataSet : SubstitutedActivitySecondVariation) →
  ∀ background u v →
  physicalSecondVariation dataSet background u v
  ≡ intrinsicHessianTerm dataSet background u v
      +ℝ substitutionCurvatureTerm dataSet background u v
physicalHessianSplitsIntrinsicPlusSubstitution dataSet =
  physicalSecondVariationChainRule dataSet

record AffineSubstitutionSpecialCase
    (dataSet : SubstitutedActivitySecondVariation) : Set₁ where
  field
    substitutionCurvatureVanishes : ∀ background u v →
      substitutionCurvatureTerm dataSet background u v
      ≡ DASHI.Foundations.RealAnalysisAxioms.0ℝ

open AffineSubstitutionSpecialCase public

cmp116SubstitutedActivityChainRuleLevel : ProofLevel
cmp116SubstitutedActivityChainRuleLevel = standardImported

cmp116PhysicalHessianSplitLevel : ProofLevel
cmp116PhysicalHessianSplitLevel = machineChecked

-- Source work: instantiate the maps by the actual CMP116 substitutions H_k(B'),
-- D(A'), A_0(...), etc.  CMP116 proves their analyticity on its declared common
-- domain; the exact derivative values remain part of the literal coordinate weld.
literalCMP116SubstitutionDerivativeIdentificationLevel : ProofLevel
literalCMP116SubstitutionDerivativeIdentificationLevel = conditional

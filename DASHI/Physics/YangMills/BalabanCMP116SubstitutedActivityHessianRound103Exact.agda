{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: PHYSICAL B-HESSIAN OF A CMP116 LOCAL ACTIVITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)
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
      substitutionCurvatureTerm dataSet background u v ≡ 0ℝ

open AffineSubstitutionSpecialCase public

cmp116SubstitutedActivityChainRuleLevel : ProofLevel
cmp116SubstitutedActivityChainRuleLevel = standardImported

cmp116PhysicalHessianSplitLevel : ProofLevel
cmp116PhysicalHessianSplitLevel = machineChecked

literalCMP116SubstitutionDerivativeIdentificationLevel : ProofLevel
literalCMP116SubstitutionDerivativeIdentificationLevel = conditional

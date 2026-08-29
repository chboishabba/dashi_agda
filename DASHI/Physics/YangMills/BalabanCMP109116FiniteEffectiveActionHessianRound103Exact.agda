{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: FINITE LOCALIZED EFFECTIVE ACTION -> SAME SECOND VARIATION
--
-- CMP109 Sect.5 defines Pi by the second background variation of E^(j), while
-- CMP116 localizes the same finite-cutoff effective action into analytic pieces.
-- This file proves the finite-sum differentiation algebra.  The source-facing
-- content is reduced to the pointwise identity between the CMP109 potential and
-- the CMP116 localized sum, plus the literal identification of CMP109 E^(2)/Pi
-- with D² of that potential.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

sumℝ : List ℝ → ℝ
sumℝ [] = 0ℝ
sumℝ (x ∷ xs) = x +ℝ sumℝ xs

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

sumFunctions : ∀ {A : Set} → List (A → ℝ) → A → ℝ
sumFunctions [] _ = 0ℝ
sumFunctions (f ∷ fs) x = f x +ℝ sumFunctions fs x

record FiniteLocalizedEffectiveAction : Set₁ where
  field
    Configuration Tangent Component : Set
    components : List Component
    localActivity : Component → Configuration → ℝ
    cmp109EffectivePotential : Configuration → ℝ

    cmp109PotentialIsLocalizedSum : ∀ configuration →
      cmp109EffectivePotential configuration
      ≡ sumFunctions (mapList localActivity components) configuration

open FiniteLocalizedEffectiveAction public

localizedPotential :
  (dataSet : FiniteLocalizedEffectiveAction) → Configuration dataSet → ℝ
localizedPotential dataSet =
  sumFunctions
    (mapList (localActivity dataSet) (components dataSet))

record SecondVariationLinearity
    (Configuration Tangent : Set) : Set₁ where
  field
    secondVariation :
      (Configuration → ℝ) → Configuration → Tangent → Tangent → ℝ

    secondVariationCong :
      ∀ f g → (∀ x → f x ≡ g x) → ∀ configuration u v →
      secondVariation f configuration u v
      ≡ secondVariation g configuration u v

    zeroSecondVariation : ∀ configuration u v →
      secondVariation (λ _ → 0ℝ) configuration u v ≡ 0ℝ

    addSecondVariation :
      ∀ f g configuration u v →
      secondVariation (λ x → f x +ℝ g x) configuration u v
      ≡ secondVariation f configuration u v
          +ℝ secondVariation g configuration u v

open SecondVariationLinearity public

localHessianValues :
  (dataSet : FiniteLocalizedEffectiveAction) →
  SecondVariationLinearity (Configuration dataSet) (Tangent dataSet) →
  Configuration dataSet → Tangent dataSet → Tangent dataSet → List ℝ
localHessianValues dataSet calculus configuration u v =
  mapList
    (λ component →
      secondVariation calculus (localActivity dataSet component) configuration u v)
    (components dataSet)

finiteLocalizedSecondVariation :
  (dataSet : FiniteLocalizedEffectiveAction) →
  SecondVariationLinearity (Configuration dataSet) (Tangent dataSet) →
  Configuration dataSet → Tangent dataSet → Tangent dataSet → ℝ
finiteLocalizedSecondVariation dataSet calculus configuration u v =
  sumℝ (localHessianValues dataSet calculus configuration u v)

secondVariationFiniteSum :
  ∀ {Configuration Tangent}
    (calculus : SecondVariationLinearity Configuration Tangent)
    (functions : List (Configuration → ℝ)) configuration u v →
  secondVariation calculus (sumFunctions functions) configuration u v
  ≡ sumℝ
      (mapList
        (λ f → secondVariation calculus f configuration u v)
        functions)
secondVariationFiniteSum calculus [] configuration u v =
  zeroSecondVariation calculus configuration u v
secondVariationFiniteSum calculus (f ∷ functions) configuration u v =
  trans
    (addSecondVariation calculus f (sumFunctions functions) configuration u v)
    (cong
      (λ tail → secondVariation calculus f configuration u v +ℝ tail)
      (secondVariationFiniteSum calculus functions configuration u v))

secondVariationOfLocalizedSum :
  (dataSet : FiniteLocalizedEffectiveAction) →
  (calculus : SecondVariationLinearity
    (Configuration dataSet) (Tangent dataSet)) →
  ∀ configuration u v →
  secondVariation calculus (localizedPotential dataSet) configuration u v
  ≡ finiteLocalizedSecondVariation dataSet calculus configuration u v
secondVariationOfLocalizedSum dataSet calculus =
  secondVariationFiniteSum calculus
    (mapList (localActivity dataSet) (components dataSet))

sourcePotentialReplacementUnderD2 :
  (dataSet : FiniteLocalizedEffectiveAction) →
  (calculus : SecondVariationLinearity
    (Configuration dataSet) (Tangent dataSet)) →
  ∀ configuration u v →
  secondVariation calculus
      (cmp109EffectivePotential dataSet) configuration u v
  ≡ secondVariation calculus
      (localizedPotential dataSet) configuration u v
sourcePotentialReplacementUnderD2 dataSet calculus =
  secondVariationCong calculus
    (cmp109EffectivePotential dataSet)
    (localizedPotential dataSet)
    (cmp109PotentialIsLocalizedSum dataSet)

record CMP109E2FromSamePotential
    (dataSet : FiniteLocalizedEffectiveAction)
    (calculus : SecondVariationLinearity
      (Configuration dataSet) (Tangent dataSet)) : Set₁ where
  field
    cmp109E2 : Configuration dataSet → Tangent dataSet → Tangent dataSet → ℝ
    cmp109E2IsSecondVariation : ∀ configuration u v →
      cmp109E2 configuration u v
      ≡ secondVariation calculus
          (cmp109EffectivePotential dataSet) configuration u v

open CMP109E2FromSamePotential public

cmp109E2IsFiniteLocalizedHessian :
  (dataSet : FiniteLocalizedEffectiveAction) →
  (calculus : SecondVariationLinearity
    (Configuration dataSet) (Tangent dataSet)) →
  (source : CMP109E2FromSamePotential dataSet calculus) →
  ∀ configuration u v →
  cmp109E2 source configuration u v
  ≡ finiteLocalizedSecondVariation dataSet calculus configuration u v
cmp109E2IsFiniteLocalizedHessian dataSet calculus source configuration u v =
  trans
    (cmp109E2IsSecondVariation source configuration u v)
    (trans
      (sourcePotentialReplacementUnderD2 dataSet calculus configuration u v)
      (secondVariationOfLocalizedSum dataSet calculus configuration u v))

finiteSecondVariationLinearityLevel : ProofLevel
finiteSecondVariationLinearityLevel = machineChecked

finiteEffectiveActionHessianAssemblyLevel : ProofLevel
finiteEffectiveActionHessianAssemblyLevel = machineChecked

literalCMP109PotentialCMP116LocalizedSumLevel : ProofLevel
literalCMP109PotentialCMP116LocalizedSumLevel = conditional

literalCMP109E2SamePotentialLevel : ProofLevel
literalCMP109E2SamePotentialLevel = conditional

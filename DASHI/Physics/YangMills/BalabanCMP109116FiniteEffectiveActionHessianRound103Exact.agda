{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: FINITE LOCALIZED EFFECTIVE ACTION -> SAME SECOND VARIATION
--
-- BIDI role:
--   * backward: the CMP116/Heat-Doob consumer needs the Hessian of the SAME
--     finite-cutoff effective potential;
--   * forward: CMP116 represents that potential by localized analytic activity
--     pieces E(X,...), while CMP109 differentiates the finite-cutoff effective
--     action to obtain E^(2)/Pi.
--
-- This file owns the finite algebra between those descriptions.  The only
-- analytic input is the standard linearity of the second derivative.  No
-- Yang--Mills estimate is hidden in the finite summation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

sumℝ : List ℝ → ℝ
sumℝ [] = 0ℝ
sumℝ (x ∷ xs) = x +ℝ sumℝ xs

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

record FiniteLocalizedEffectiveAction : Set₁ where
  field
    Configuration Tangent Component : Set
    components : List Component

    localActivity : Component → Configuration → ℝ
    cmp109EffectivePotential : Configuration → ℝ

    -- Literal source equality: the CMP109 finite-cutoff effective action is the
    -- sum of the CMP116 localized activity pieces on the SAME configuration.
    cmp109PotentialIsLocalizedSum : ∀ configuration →
      cmp109EffectivePotential configuration
      ≡ sumℝ (mapList (λ component → localActivity component configuration) components)

open FiniteLocalizedEffectiveAction public

localizedPotential : FiniteLocalizedEffectiveAction → Configuration _ → ℝ
localizedPotential dataSet configuration =
  sumℝ
    (mapList
      (λ component → localActivity dataSet component configuration)
      (components dataSet))

record SecondVariationLinearity
    (Configuration Tangent : Set) : Set₁ where
  field
    secondVariation :
      (Configuration → ℝ) → Configuration → Tangent → Tangent → ℝ

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

-- The recursive finite-sum theorem is deliberately stated as the standard
-- derivative-linearity consequence consumed by the physical carrier.  In the
-- repository's abstract real-analysis surface the function-extensional
-- replacement needed to rewrite `localizedPotential` is not primitive; the
-- calculus implementation supplies this conventional finite linearity fact.
record FiniteSecondVariationCommutation
    (dataSet : FiniteLocalizedEffectiveAction)
    (calculus : SecondVariationLinearity
      (Configuration dataSet) (Tangent dataSet)) : Set₁ where
  field
    secondVariationOfLocalizedSum : ∀ configuration u v →
      secondVariation calculus (localizedPotential dataSet) configuration u v
      ≡ finiteLocalizedSecondVariation dataSet calculus configuration u v

open FiniteSecondVariationCommutation public

record CMP109E2FromSamePotential
    (dataSet : FiniteLocalizedEffectiveAction)
    (calculus : SecondVariationLinearity
      (Configuration dataSet) (Tangent dataSet)) : Set₁ where
  field
    cmp109E2 : Configuration dataSet → Tangent dataSet → Tangent dataSet → ℝ

    -- This is the CMP109 source-definition seam: E^(2)/Pi is the second
    -- background variation of the SAME effective potential above.
    cmp109E2IsSecondVariation : ∀ configuration u v →
      cmp109E2 configuration u v
      ≡ secondVariation calculus
          (cmp109EffectivePotential dataSet) configuration u v

    -- Explicit transport of the source potential equality through D².  Keeping
    -- this field named prevents an equivalent-but-differently-normalized action
    -- from silently entering the carrier.
    sourcePotentialReplacementUnderD2 : ∀ configuration u v →
      secondVariation calculus
          (cmp109EffectivePotential dataSet) configuration u v
      ≡ secondVariation calculus
          (localizedPotential dataSet) configuration u v

open CMP109E2FromSamePotential public

cmp109E2IsFiniteLocalizedHessian :
  (dataSet : FiniteLocalizedEffectiveAction) →
  (calculus : SecondVariationLinearity
    (Configuration dataSet) (Tangent dataSet)) →
  (commutation : FiniteSecondVariationCommutation dataSet calculus) →
  (source : CMP109E2FromSamePotential dataSet calculus) →
  ∀ configuration u v →
  cmp109E2 source configuration u v
  ≡ finiteLocalizedSecondVariation dataSet calculus configuration u v
cmp109E2IsFiniteLocalizedHessian dataSet calculus commutation source configuration u v
  rewrite cmp109E2IsSecondVariation source configuration u v
  | sourcePotentialReplacementUnderD2 source configuration u v
  | secondVariationOfLocalizedSum commutation configuration u v = refl

finiteEffectiveActionHessianAssemblyLevel : ProofLevel
finiteEffectiveActionHessianAssemblyLevel = machineChecked

finiteSecondVariationLinearityLevel : ProofLevel
finiteSecondVariationLinearityLevel = standardImported

-- Physical/source obligations left visible:
--   (i) instantiate `cmp109PotentialIsLocalizedSum` with the actual CMP109/CMP116
--       finite-cutoff action and activities;
--   (ii) instantiate `cmp109E2IsSecondVariation` in the exact source coordinate;
--   (iii) discharge the explicit D² replacement after convention alignment.
literalCMP109PotentialCMP116LocalizedSumLevel : ProofLevel
literalCMP109PotentialCMP116LocalizedSumLevel = conditional

literalCMP109E2SamePotentialLevel : ProofLevel
literalCMP109E2SamePotentialLevel = conditional

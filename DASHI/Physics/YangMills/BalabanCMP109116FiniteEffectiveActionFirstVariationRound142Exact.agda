{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact where

------------------------------------------------------------------------
-- ROUND142: FIRST VARIATION OF THE EXACT CMP109/CMP116 FINITE LOCALIZED SUM
--
-- Round103 already proves the corresponding second-variation finite-sum
-- theorem.  Stress is first order, so we need the same elementary algebra for
-- D rather than reusing a second-order theorem or treating one local activity
-- as the whole generated action.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite

record FirstVariationLinearity
    (Configuration Tangent : Set) : Set₁ where
  field
    firstVariation :
      (Configuration → ℝ) → Configuration → Tangent → ℝ

    firstVariationCong :
      ∀ f g → (∀ x → f x ≡ g x) → ∀ configuration u →
      firstVariation f configuration u
      ≡ firstVariation g configuration u

    zeroFirstVariation : ∀ configuration u →
      firstVariation (λ _ → 0ℝ) configuration u ≡ 0ℝ

    addFirstVariation :
      ∀ f g configuration u →
      firstVariation (λ x → f x +ℝ g x) configuration u
      ≡ firstVariation f configuration u
          +ℝ firstVariation g configuration u

open FirstVariationLinearity public

localFirstVariationValues :
  (dataSet : Finite.FiniteLocalizedEffectiveAction) →
  FirstVariationLinearity
    (Finite.Configuration dataSet) (Finite.Tangent dataSet) →
  Finite.Configuration dataSet → Finite.Tangent dataSet → List ℝ
localFirstVariationValues dataSet calculus configuration u =
  Finite.mapList
    (λ component →
      firstVariation calculus
        (Finite.localActivity dataSet component) configuration u)
    (Finite.components dataSet)

finiteLocalizedFirstVariation :
  (dataSet : Finite.FiniteLocalizedEffectiveAction) →
  FirstVariationLinearity
    (Finite.Configuration dataSet) (Finite.Tangent dataSet) →
  Finite.Configuration dataSet → Finite.Tangent dataSet → ℝ
finiteLocalizedFirstVariation dataSet calculus configuration u =
  Finite.sumℝ (localFirstVariationValues dataSet calculus configuration u)

firstVariationFiniteSum :
  ∀ {Configuration Tangent}
    (calculus : FirstVariationLinearity Configuration Tangent)
    (functions : List (Configuration → ℝ)) configuration u →
  firstVariation calculus (Finite.sumFunctions functions) configuration u
  ≡ Finite.sumℝ
      (Finite.mapList
        (λ f → firstVariation calculus f configuration u)
        functions)
firstVariationFiniteSum calculus [] configuration u =
  zeroFirstVariation calculus configuration u
firstVariationFiniteSum calculus (f ∷ functions) configuration u =
  trans
    (addFirstVariation calculus f (Finite.sumFunctions functions) configuration u)
    (cong
      (λ tail → firstVariation calculus f configuration u +ℝ tail)
      (firstVariationFiniteSum calculus functions configuration u))

firstVariationOfLocalizedSum :
  (dataSet : Finite.FiniteLocalizedEffectiveAction) →
  (calculus : FirstVariationLinearity
    (Finite.Configuration dataSet) (Finite.Tangent dataSet)) →
  ∀ configuration u →
  firstVariation calculus (Finite.localizedPotential dataSet) configuration u
  ≡ finiteLocalizedFirstVariation dataSet calculus configuration u
firstVariationOfLocalizedSum dataSet calculus =
  firstVariationFiniteSum calculus
    (Finite.mapList (Finite.localActivity dataSet) (Finite.components dataSet))

sourcePotentialReplacementUnderD1 :
  (dataSet : Finite.FiniteLocalizedEffectiveAction) →
  (calculus : FirstVariationLinearity
    (Finite.Configuration dataSet) (Finite.Tangent dataSet)) →
  ∀ configuration u →
  firstVariation calculus
      (Finite.cmp109EffectivePotential dataSet) configuration u
  ≡ firstVariation calculus
      (Finite.localizedPotential dataSet) configuration u
sourcePotentialReplacementUnderD1 dataSet calculus =
  firstVariationCong calculus
    (Finite.cmp109EffectivePotential dataSet)
    (Finite.localizedPotential dataSet)
    (Finite.cmp109PotentialIsLocalizedSum dataSet)

cmp109FirstVariationIsFiniteLocalizedSum :
  (dataSet : Finite.FiniteLocalizedEffectiveAction) →
  (calculus : FirstVariationLinearity
    (Finite.Configuration dataSet) (Finite.Tangent dataSet)) →
  ∀ configuration u →
  firstVariation calculus
      (Finite.cmp109EffectivePotential dataSet) configuration u
  ≡ finiteLocalizedFirstVariation dataSet calculus configuration u
cmp109FirstVariationIsFiniteLocalizedSum dataSet calculus configuration u =
  trans
    (sourcePotentialReplacementUnderD1 dataSet calculus configuration u)
    (firstVariationOfLocalizedSum dataSet calculus configuration u)

finiteFirstVariationLinearityLevel : ProofLevel
finiteFirstVariationLinearityLevel = machineChecked

finiteEffectiveActionFirstVariationAssemblyLevel : ProofLevel
finiteEffectiveActionFirstVariationAssemblyLevel = machineChecked

-- The source equality `cmp109PotentialIsLocalizedSum` is reused from Round103;
-- no new physical finite-sum identity is introduced here.  A concrete derivative
-- calculus still has to instantiate the ordinary linearity laws above.

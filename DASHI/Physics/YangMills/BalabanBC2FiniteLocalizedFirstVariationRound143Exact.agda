{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact where

------------------------------------------------------------------------
-- ROUND143: BC2'S ACTUAL FIRST DERIVATIVE -> EXACT BC1 LOCALIZED D1 SUM
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _+ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

record PresentCutBC2FirstVariationLinearity
    {History Cell : Set} {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff) : Set₁ where
  field
    firstVariationCong :
      ∀ f g → (∀ x → f x ≡ g x) → ∀ background u →
      BC2.firstVariation (Present.bc2 present) f background u
      ≡ BC2.firstVariation (Present.bc2 present) g background u

    zeroFirstVariation : ∀ background u →
      BC2.firstVariation (Present.bc2 present) (λ _ → 0ℝ) background u
      ≡ 0ℝ

    addFirstVariation :
      ∀ f g background u →
      BC2.firstVariation (Present.bc2 present)
        (λ x → f x +ℝ g x) background u
      ≡ BC2.firstVariation (Present.bc2 present) f background u
          +ℝ BC2.firstVariation (Present.bc2 present) g background u

open PresentCutBC2FirstVariationLinearity public

asFirstVariationLinearity :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff} →
  PresentCutBC2FirstVariationLinearity present →
  D1.FirstVariationLinearity
    (Finite.Configuration (Carrier.finiteAction (Present.bc1Carrier present)))
    (Finite.Tangent (Carrier.finiteAction (Present.bc1Carrier present)))
asFirstVariationLinearity {present = present} laws = record
  { D1.FirstVariationLinearity.firstVariation =
      BC2.firstVariation (Present.bc2 present)
  ; D1.FirstVariationLinearity.firstVariationCong = firstVariationCong laws
  ; D1.FirstVariationLinearity.zeroFirstVariation = zeroFirstVariation laws
  ; D1.FirstVariationLinearity.addFirstVariation = addFirstVariation laws
  }

bc2GlobalFirstVariationIsFiniteLocalizedSum :
  ∀ {History Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (laws : PresentCutBC2FirstVariationLinearity present) →
  ∀ background tangent →
  BC2.firstVariation (Present.bc2 present)
      (Carrier.effectivePotential (Present.bc1Carrier present))
      background tangent
  ≡ D1.finiteLocalizedFirstVariation
      (Carrier.finiteAction (Present.bc1Carrier present))
      (asFirstVariationLinearity laws)
      background tangent
bc2GlobalFirstVariationIsFiniteLocalizedSum {present = present} laws =
  D1.cmp109FirstVariationIsFiniteLocalizedSum
    (Carrier.finiteAction (Present.bc1Carrier present))
    (asFirstVariationLinearity laws)

bc2FiniteLocalizedFirstVariationCompilerLevel : ProofLevel
bc2FiniteLocalizedFirstVariationCompilerLevel = machineChecked

-- These three linearity/congruence laws are ordinary first-derivative algebra;
-- they are separated from the physical stress identification.  Once supplied,
-- the exact BC1 finite localized sum is theorem-generated.
presentCutBC2FirstVariationLinearityLevel : ProofLevel
presentCutBC2FirstVariationLinearityLevel = conditional

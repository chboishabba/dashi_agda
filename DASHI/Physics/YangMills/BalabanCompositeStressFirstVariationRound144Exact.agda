{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCompositeStressFirstVariationRound144Exact where

------------------------------------------------------------------------
-- ROUND144: THE STRESS FIRST VARIATION IS THE WHOLE LOCALIZED D1 SUM
--
-- This is the stronger producer for Round133.  Instead of postulating directly
-- that one substituted stress activity equals the derivative of the global BC1
-- potential, we route both through the exact finite localized first-variation
-- sum constructed in Rounds142--143.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact as R133

record CompositeStressFirstVariationInputs
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present)
    (laws : R143.PresentCutBC2FirstVariationLinearity present) : Set₁ where
  field
    stressActivity : Chain.SubstitutedActivitySecondVariation

    globalBackgroundToStressBackground :
      Source.Background (Carrier.source (Present.bc1Carrier present)) →
      Chain.Background stressActivity

    globalTangentToStressTangent :
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) →
      Chain.BackgroundTangent stressActivity

    -- The physical stress leaf is now explicitly the whole localized first
    -- derivative, not an unnamed direct equality with the global action.
    stressFirstVariationIsFiniteLocalizedSum :
      ∀ background tangent →
      First.substitutedFirstVariation stressActivity
        (globalBackgroundToStressBackground background)
        (globalTangentToStressTangent tangent)
      ≡ D1.finiteLocalizedFirstVariation
          (Carrier.finiteAction (Present.bc1Carrier present))
          (R143.asFirstVariationLinearity laws)
          background tangent

open CompositeStressFirstVariationInputs public

asUnifiedGeneratedActionFirstVariation :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws} →
  CompositeStressFirstVariationInputs
    {trajectory = trajectory} {split = split} {inputs = inputs}
    {History = History} {Cell = Cell} {cutoff = cutoff}
    {present = present} actionWeld laws →
  R133.UnifiedGeneratedActionFirstVariation actionWeld
asUnifiedGeneratedActionFirstVariation {present = present} {laws = laws} dataSet = record
  { R133.UnifiedGeneratedActionFirstVariation.stressActivity =
      stressActivity dataSet
  ; R133.UnifiedGeneratedActionFirstVariation.globalBackgroundToStressBackground =
      globalBackgroundToStressBackground dataSet
  ; R133.UnifiedGeneratedActionFirstVariation.globalTangentToStressTangent =
      globalTangentToStressTangent dataSet
  ; R133.UnifiedGeneratedActionFirstVariation.bc2GlobalFirstVariationIsStressActivityFirstVariation =
      λ background tangent →
        trans
          (R143.bc2GlobalFirstVariationIsFiniteLocalizedSum laws background tangent)
          (sym (stressFirstVariationIsFiniteLocalizedSum dataSet background tangent))
  }

compositeStressBuildsGlobalFirstVariation :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld laws}
    (dataSet : CompositeStressFirstVariationInputs
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld laws) →
  ∀ background tangent →
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    background tangent
  ≡ First.substitutedFirstVariation (stressActivity dataSet)
      (globalBackgroundToStressBackground dataSet background)
      (globalTangentToStressTangent dataSet tangent)
compositeStressBuildsGlobalFirstVariation dataSet =
  R133.sameActionFirstVariation
    (asUnifiedGeneratedActionFirstVariation dataSet)

compositeStressFirstVariationCompilerLevel : ProofLevel
compositeStressFirstVariationCompilerLevel = machineChecked

-- Remaining physical first-order seam is now the displayed equality between the
-- selected stress insertion and the sum of the literal CMP116 localized D1
-- contributions.  The global BC1/BC2 differentiation is downstream algebra.
literalCompositeStressFirstVariationIdentificationLevel : ProofLevel
literalCompositeStressFirstVariationIdentificationLevel = conditional

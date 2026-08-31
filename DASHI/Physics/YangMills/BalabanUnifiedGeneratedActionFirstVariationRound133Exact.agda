{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionFirstVariationRound133Exact where

------------------------------------------------------------------------
-- ROUND133: FIRST-ORDER STRESS VIEW OF THE SAME BC1/BC2 GENERATED ACTION
--
-- Round132 identifies the beta-driven density with the exact BC1 effective
-- potential.  BC2 already owns a first-variation operator applied literally to
-- that potential.  This file makes the remaining first-order source statement
-- explicit: the stress-generating substituted CMP116 activity is a first-order
-- view of that SAME global generated action, after declared background/tangent
-- transports.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as Source
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityFirstVariationRound105Exact as First
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

record UnifiedGeneratedActionFirstVariation
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) : Set₁ where
  field
    -- The stress insertion is allowed to use its natural substituted-activity
    -- carrier; it is not definitionally equated with the global finite action.
    stressActivity : Chain.SubstitutedActivitySecondVariation

    globalBackgroundToStressBackground :
      Source.Background (Carrier.source (Present.bc1Carrier present)) →
      Chain.Background stressActivity

    globalTangentToStressTangent :
      Source.Tangent (Carrier.source (Present.bc1Carrier present)) →
      Chain.BackgroundTangent stressActivity

    -- This is the key first-order same-action theorem.  The LHS is BC2's
    -- derivative operator applied to the exact BC1 potential.  The RHS is the
    -- substituted CMP116 first variation used by the stress lane.
    bc2GlobalFirstVariationIsStressActivityFirstVariation :
      ∀ background tangent →
      BC2.firstVariation (Present.bc2 present)
        (Carrier.effectivePotential (Present.bc1Carrier present))
        background tangent
      ≡ First.substitutedFirstVariation stressActivity
          (globalBackgroundToStressBackground background)
          (globalTangentToStressTangent tangent)

open UnifiedGeneratedActionFirstVariation public

sameActionFirstVariation :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld}
    (weld : UnifiedGeneratedActionFirstVariation
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld) →
  ∀ background tangent →
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    background tangent
  ≡ First.substitutedFirstVariation (stressActivity weld)
      (globalBackgroundToStressBackground weld background)
      (globalTangentToStressTangent weld tangent)
sameActionFirstVariation = bc2GlobalFirstVariationIsStressActivityFirstVariation

-- Round132 plus this theorem means the first derivative feeding stress and the
-- first derivative appearing in the same-density Heat/Doob calculus are now
-- views of the same represented beta-driven generated action.  No additional
-- equality between a BC2 density and a stress density should be introduced.
unifiedGeneratedActionFirstVariationCompilerLevel : ProofLevel
unifiedGeneratedActionFirstVariationCompilerLevel = machineChecked

literalUnifiedGeneratedActionFirstVariationLevel : ProofLevel
literalUnifiedGeneratedActionFirstVariationLevel = conditional

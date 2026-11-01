{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA2HistoryRound137Exact where

------------------------------------------------------------------------
-- ROUND137: A2 RESPONSE AND THE GENERATED DENSITY USE ONE COUPLING HISTORY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2Producer
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

record UnifiedGeneratedActionA2History
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {HistoryCarrier Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff}
    (actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) : Set₁ where
  field
    -- The A2 response producer and the complete-density flow are forced onto the
    -- same source coupling at every finite active scale.
    a2CouplingIsBetaDrivenDensityCoupling :
      ∀ j → j ℕ.< cutoff →
      Direct.coupling
        (Quartic.direct (A2Producer.quartic (Present.a2 present))) j
      ≡ History.couplingAt (BetaDensity.betaHistory inputs) j

open UnifiedGeneratedActionA2History public

a2UsesExactBetaDrivenDensityCoupling :
  ∀ {trajectory split inputs HistoryCarrier Cell cutoff present actionWeld}
    (weld : UnifiedGeneratedActionA2History
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld) →
  ∀ j → j ℕ.< cutoff →
  Direct.coupling
    (Quartic.direct (A2Producer.quartic (Present.a2 present))) j
  ≡ History.couplingAt (BetaDensity.betaHistory inputs) j
a2UsesExactBetaDrivenDensityCoupling = a2CouplingIsBetaDrivenDensityCoupling

-- The finite-prefix q<1 theorem remains exactly the already-owned Round122 A2
-- consequence.  This record adds only the missing same-history provenance; it
-- does not re-prove any Cauchy, cubic-telescope, response-kernel or summability
-- estimate.
unifiedGeneratedActionA2HistoryCompilerLevel : ProofLevel
unifiedGeneratedActionA2HistoryCompilerLevel = machineChecked

literalUnifiedGeneratedActionA2HistoryLevel : ProofLevel
literalUnifiedGeneratedActionA2HistoryLevel = conditional

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA1HistoryRound138Exact where

------------------------------------------------------------------------
-- ROUND138: A1 TWO-JET/FIVE-CHANNEL SHELLS USE THE SAME DENSITY COUPLING
--
-- The A1 history carrier is intentionally abstract, so we do not identify it
-- with the CMP122 history type.  The physically relevant scalar is exposed by
-- the five-channel interaction itself.  This file requires that scalar to equal
-- the beta-driven complete-density coupling at the same shell index.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as BetaHistory
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as A1
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as AbsFive
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132

record UnifiedGeneratedActionA1History
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) : Set₁ where
  field
    a1ShellCouplingIsBetaDrivenDensityCoupling :
      ∀ K k (k<K : k ℕ.< K) →
      let reduced = Present.a1Reduced present
          shellHistory = A1.historyForShell reduced K k k<K
      in
      Five.coupling
        (AbsFive.lowerData
          (Cert.interaction (A1.certificate reduced) shellHistory))
      ≡ BetaHistory.couplingAt (BetaDensity.betaHistory inputs) k

open UnifiedGeneratedActionA1History public

a1UsesExactBetaDrivenDensityCoupling :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld}
    (weld : UnifiedGeneratedActionA1History
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld) →
  ∀ K k (k<K : k ℕ.< K) →
  let reduced = Present.a1Reduced present
      shellHistory = A1.historyForShell reduced K k k<K
  in
  Five.coupling
    (AbsFive.lowerData
      (Cert.interaction (A1.certificate reduced) shellHistory))
  ≡ BetaHistory.couplingAt (BetaDensity.betaHistory inputs) k
a1UsesExactBetaDrivenDensityCoupling = a1ShellCouplingIsBetaDrivenDensityCoupling

unifiedGeneratedActionA1HistoryCompilerLevel : ProofLevel
unifiedGeneratedActionA1HistoryCompilerLevel = machineChecked

literalUnifiedGeneratedActionA1HistoryLevel : ProofLevel
literalUnifiedGeneratedActionA1HistoryLevel = conditional

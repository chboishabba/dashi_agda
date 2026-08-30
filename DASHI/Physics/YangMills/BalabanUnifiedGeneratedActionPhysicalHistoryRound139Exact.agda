{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionPhysicalHistoryRound139Exact where

------------------------------------------------------------------------
-- ROUND139: ONE PHYSICAL COUPLING HISTORY FOR A1, A2 AND THE GENERATED DENSITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as A1
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticBetaAdapterExact as Five
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as AbsFive
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2Producer
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA2HistoryRound137Exact as R137
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA1HistoryRound138Exact as R138

record UnifiedGeneratedActionPhysicalHistory
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {History Cell : Set} {cutoff : Nat}
    {present : Present.PresentCutPhysicalSourceInputs History Cell cutoff}
    (actionWeld : R132.UnifiedGeneratedActionDensity
      {trajectory = trajectory} {split = split} {inputs = inputs} present) : Set₁ where
  field
    a1History : R138.UnifiedGeneratedActionA1History actionWeld
    a2History : R137.UnifiedGeneratedActionA2History actionWeld

open UnifiedGeneratedActionPhysicalHistory public

a1AndA2UseSamePhysicalCoupling :
  ∀ {trajectory split inputs History Cell cutoff present actionWeld}
    (history : UnifiedGeneratedActionPhysicalHistory
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {History = History} {Cell = Cell} {cutoff = cutoff}
      {present = present} actionWeld) →
  ∀ K k (k<K : k ℕ.< K) (k<cutoff : k ℕ.< cutoff) →
  let reduced = Present.a1Reduced present
      shellHistory = A1.historyForShell reduced K k k<K
  in
  Five.coupling
    (AbsFive.lowerData
      (Cert.interaction (A1.certificate reduced) shellHistory))
  ≡ Direct.coupling
      (Quartic.direct (A2Producer.quartic (Present.a2 present))) k
a1AndA2UseSamePhysicalCoupling history K k k<K k<cutoff =
  trans
    (R138.a1UsesExactBetaDrivenDensityCoupling
      (a1History history) K k k<K)
    (sym
      (R137.a2UsesExactBetaDrivenDensityCoupling
        (a2History history) k k<cutoff))

unifiedGeneratedActionPhysicalHistoryCompilerLevel : ProofLevel
unifiedGeneratedActionPhysicalHistoryCompilerLevel = machineChecked

-- This is deliberately a provenance theorem, not a new beta estimate.  All A1
-- bounds and A2 q<1 summation remain the existing downstream compilers.
literalUnifiedGeneratedActionPhysicalHistoryLevel : ProofLevel
literalUnifiedGeneratedActionPhysicalHistoryLevel = conditional

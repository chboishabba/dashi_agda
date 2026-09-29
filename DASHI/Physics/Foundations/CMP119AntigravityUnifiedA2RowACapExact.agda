{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2Producer
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseCanonicalChoiceExact as WardChoice
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionDensityRound132Exact as R132
import DASHI.Physics.YangMills.BalabanUnifiedGeneratedActionA2HistoryRound137Exact as R137
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- UNIFIED GENERATED-ACTION A2 -> SAME BETA-HISTORY ROW-A CAP
------------------------------------------------------------------------

rowAConstantsFromA2 :
  ∀ {HistoryCarrier Cell cutoff} →
  Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff →
  RowA.FiniteQuarticResponseConstants
rowAConstantsFromA2 present =
  WardChoice.asFiniteQuarticResponseConstants
    (A2Producer.producerWardConstants (Present.a2 present))

rowAGammaFromA2 :
  ∀ {HistoryCarrier Cell cutoff} →
  Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff →
  ℚ
rowAGammaFromA2 present =
  RowA.canonicalQuarticResponseGamma (rowAConstantsFromA2 present)

a2CapIsRowAGamma :
  ∀ {HistoryCarrier Cell cutoff}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff) →
  Quartic.couplingCap (A2Producer.quartic (Present.a2 present))
  ≡ rowAGammaFromA2 present
a2CapIsRowAGamma present =
  A2Producer.couplingCapIsCanonical (Present.a2 present)

betaHistoryCouplingBelowA2Cap :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {HistoryCarrier Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff}
    (actionWeld :
      R132.UnifiedGeneratedActionDensity
        {trajectory = trajectory} {split = split} {inputs = inputs} present)
    (historyWeld : R137.UnifiedGeneratedActionA2History actionWeld) →
  ∀ j → j ℕ.< cutoff →
  History.couplingAt (BetaDensity.betaHistory inputs) j
  ≤ Quartic.couplingCap (A2Producer.quartic (Present.a2 present))
betaHistoryCouplingBelowA2Cap
    {inputs = inputs} {present = present}
    actionWeld historyWeld j j<cutoff =
  let
    producer = Present.a2 present
    quartic = A2Producer.quartic producer

    raw :
      Direct.coupling (Quartic.direct quartic) j
      ≤ Quartic.couplingCap quartic
    raw = Quartic.couplingBelowCap quartic j j<cutoff

    sameCoupling :
      Direct.coupling (Quartic.direct quartic) j
      ≡ History.couplingAt
          (BetaDensity.betaHistory inputs) j
    sameCoupling =
      R137.a2UsesExactBetaDrivenDensityCoupling historyWeld j j<cutoff
  in
  subst
    (λ lower → lower ≤ Quartic.couplingCap quartic)
    sameCoupling
    raw

betaHistoryCouplingBelowCanonicalRowA :
  ∀ {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {HistoryCarrier Cell cutoff}
    {present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff}
    (actionWeld :
      R132.UnifiedGeneratedActionDensity
        {trajectory = trajectory} {split = split} {inputs = inputs} present)
    (historyWeld : R137.UnifiedGeneratedActionA2History actionWeld) →
  ∀ j → j ℕ.< cutoff →
  History.couplingAt (BetaDensity.betaHistory inputs) j
  ≤ RowA.canonicalQuarticResponseGamma (rowAConstantsFromA2 present)
betaHistoryCouplingBelowCanonicalRowA
    {inputs = inputs} {present = present}
    actionWeld historyWeld j j<cutoff =
  subst
    (λ upper →
      History.couplingAt (BetaDensity.betaHistory inputs) j ≤ upper)
    (a2CapIsRowAGamma present)
    (betaHistoryCouplingBelowA2Cap
      actionWeld historyWeld j j<cutoff)

postHocA2ToBetaCouplingEqualityRequired : Bool
postHocA2ToBetaCouplingEqualityRequired = false

postHocA2CapToRowAGammaEqualityRequired : Bool
postHocA2CapToRowAGammaEqualityRequired = false

postHocA2ToBetaCouplingEqualityRequiredIsFalse :
  postHocA2ToBetaCouplingEqualityRequired ≡ false
postHocA2ToBetaCouplingEqualityRequiredIsFalse = refl

postHocA2CapToRowAGammaEqualityRequiredIsFalse :
  postHocA2CapToRowAGammaEqualityRequired ≡ false
postHocA2CapToRowAGammaEqualityRequiredIsFalse = refl

unifiedA2RowACapCompilerLevel : ProofLevel
unifiedA2RowACapCompilerLevel = machineChecked

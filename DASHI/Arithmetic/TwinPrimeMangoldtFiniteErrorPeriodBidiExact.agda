module DASHI.Arithmetic.TwinPrimeMangoldtFiniteErrorPeriodBidiExact where

------------------------------------------------------------------------
-- MAX-CUT M13 x M14 x M15: TOTAL PERIOD RESIDUAL ↔ PRIME / ERROR
--
-- Every Nat interval, including short nonboundary segments,
-- admits the ORIGINAL lossless 270-period plan.
-- Every ORIGINAL Mangoldt pair contribution is exactly a genuine
-- exponent-one pair term OR a retained non-prime error term.
--
-- The two source-written BIDI modules are COMPOSED here, not
-- recoded. The existing Weil scalar does NOT supply left/right
-- unit, associativity or interchange laws; they are explicit
-- required structures. No positive gap-two lower bound or
-- proper-prime-power error estimate is assumed or concluded.
--
-- Reuse owners: RiemannVonMangoldtSpecification,
-- TwinPrimeMangoldtTotalIntervalPlanExact,
-- TwinPrimeMangoldtPrimeErrorFiniteSplitExact.
-- Source-written, Agda kernel pending, 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact as WeilBridge
import DASHI.Arithmetic.TwinPrimeMangoldtTotalIntervalPlanExact as Total
import DASHI.Arithmetic.TwinPrimeMangoldtTwoCaseIntervalPlanExact as Plan
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact as Split

finiteCodedPeriodToPrimeError :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (monoid : WeilBridge.WeilAdditiveLaws space)
  (splitLaws : Split.AdditiveInterchangeLaws space) →
  (start count : Nat) →
  Plan.planCorrelationSum (WeilBridge.weilAdditive space)
    (Actual.actualMangoldtPair space arithmetic mangoldt)
    start count (Total.completeIntervalPlan start count)
  ≡ Weil.WeilTestSpace._+S_ space
      (Sum.sumInterval (WeilBridge.weilAdditive space)
        (Split.primeOnlyAtNat space arithmetic mangoldt) start count)
      (Sum.sumInterval (WeilBridge.weilAdditive space)
        (Split.nonPrimeErrorAtNat space arithmetic mangoldt) start count)
finiteCodedPeriodToPrimeError space arithmetic mangoldt monoid
    splitLaws start count =
  trans
    (Total.totalIntervalCorrelationBackward
      (WeilBridge.weilAdditive space)
      (WeilBridge.weilMonoid space monoid)
      (Actual.actualMangoldtPair space arithmetic mangoldt)
      start count)
    (Split.finiteMangoldtPrimeErrorSplit
      space arithmetic mangoldt splitLaws start count)

finitePrimeErrorToCodedPeriod :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (monoid : WeilBridge.WeilAdditiveLaws space)
  (splitLaws : Split.AdditiveInterchangeLaws space) →
  (start count : Nat) →
  Weil.WeilTestSpace._+S_ space
    (Sum.sumInterval (WeilBridge.weilAdditive space)
      (Split.primeOnlyAtNat space arithmetic mangoldt) start count)
    (Sum.sumInterval (WeilBridge.weilAdditive space)
      (Split.nonPrimeErrorAtNat space arithmetic mangoldt) start count)
  ≡ Plan.planCorrelationSum (WeilBridge.weilAdditive space)
      (Actual.actualMangoldtPair space arithmetic mangoldt)
      start count (Total.completeIntervalPlan start count)
finitePrimeErrorToCodedPeriod space arithmetic mangoldt monoid
    splitLaws start count =
  sym (finiteCodedPeriodToPrimeError
    space arithmetic mangoldt monoid splitLaws start count)

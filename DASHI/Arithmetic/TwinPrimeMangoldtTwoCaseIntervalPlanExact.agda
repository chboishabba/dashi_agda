module DASHI.Arithmetic.TwinPrimeMangoldtTwoCaseIntervalPlanExact where

------------------------------------------------------------------------
-- M13 CORRECTION: SHORT INTERVALS DO NOT REACH THE NEXT 270 BOUNDARY.
--
-- The previous aligned schedule cannot apply to [59,60) because
-- 59 + 1 is not a multiple of 270. Correct decomposition MUST
-- have two cases:
--   (1) contained in one period: exact pointwise coded fold;
--   (2) crosses a boundary: certified prefix/full rows/suffix.
--
-- Both cases reuse the ORIGINAL unbounded NatPeriod270
-- inverse, finite-sum consumer BIDI and certified schedule.
-- Neither case creates a prime density theorem.
-- Source-written; Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.DivMod using (_%_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact as Multi
import DASHI.Arithmetic.TwinPrimeMangoldtCertifiedIntervalScheduleExact as Schedule

-- A witness that the entire indexed segment fits without wraparound.
-- The 270 here is the ACTUAL Nat residue radix, not the number
-- of 27 certified 2/3/5 pair-surviving cube points.
data CompleteIntervalPlan (start count : Nat) : Set where
  withinOnePeriod :
    start % 270 + count ≤ 270 →
    CompleteIntervalPlan start count
  crossingPeriod :
    Schedule.CertifiedIntervalSchedule start count →
    CompleteIntervalPlan start count

-- The two branches share the SAME actual arithmetic correlation.
-- A within-period segment remains coded by the original exact
-- encode, not by any of the 14/15 lossy orbit quotients.
planCorrelationSum :
  (S : Sum.AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  CompleteIntervalPlan start count →
  Sum.Scalar S
planCorrelationSum S C start count (withinOnePeriod bounded) =
  Sum.sumDecodedInterval S (Bidi.pairCorrelationAtPeriod C) start count
planCorrelationSum S C start count (crossingPeriod schedule) =
  Sum.add S
    (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
      start (Schedule.prefixLength schedule))
    (Sum.add S
      (Multi.codeBlockRows S C
        (Schedule.firstWholePeriod schedule)
        (Schedule.wholePeriods schedule))
      (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (Schedule.firstWholePeriod schedule * 270
          + Schedule.wholePeriods schedule * 270)
        (Schedule.suffixLength schedule)))

completePlanForward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  (plan : CompleteIntervalPlan start count) →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
    ≡ planCorrelationSum S C start count plan
completePlanForward S M C start count (withinOnePeriod bounded) =
  Sum.pairFiniteSumBidiBackward S C start count
completePlanForward S M C start count (crossingPeriod schedule) =
  Schedule.scheduleCorrelationForward S M C start count schedule

completePlanBackward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  (plan : CompleteIntervalPlan start count) →
  planCorrelationSum S C start count plan
    ≡ Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
completePlanBackward S M C start count plan =
  sym (completePlanForward S M C start count plan)

-- Constructing a CompleteIntervalPlan for EVERY (start,count) is
-- the remaining Euclidean-division arithmetic/induction cut.
-- Unlike the older aligned-only schedule, this two-case target is
-- logically totalisable. Neither branch itself asserts positivity.

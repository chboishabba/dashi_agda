module DASHI.Arithmetic.TwinPrimeMangoldtTotalIntervalPlanExact where

------------------------------------------------------------------------
-- M13 TOTAL CONSTRUCTOR: EVERY NAT INTERVAL HAS A LOSSLESS 270-PLAN.
--
-- REUSE:
--   original NatPeriod270 / Euclidean division source,
--   TwinPrimeMangoldtTwoCaseIntervalPlanExact,
--   original certified prefix/full-block/suffix BIDI.
--
-- Explicitly distinguishes a short within-period interval from
-- a boundary-crossing interval; the former cannot satisfy the
-- aligned-only schedule (e.g. [59,60)).
--
-- Everything below is finite Nat arithmetic. No density, prime
-- distribution, sieve parity bypass or unproved analysis is used.
-- SOURCE-WRITTEN, AGDA KERNEL PENDING. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _∸_; z≤n; s≤s)
open import Data.Nat.DivMod using
  (_/_; _%_; m%n<n; m≡m%n+[m/n]*n)
import Data.Nat.Properties as NP
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (cong; trans; sym; subst)

import DASHI.Arithmetic.TwinPrimeMangoldtTwoCaseIntervalPlanExact as Plan
import DASHI.Arithmetic.TwinPrimeMangoldtCertifiedIntervalScheduleExact as Schedule
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact as Multi

-- The natural distance to the next STRICTLY FUTURE boundary.
-- At a residue of zero the distance is 270, not zero: an
-- interval shorter than one full period uses the 'within' case.
distanceToBoundary : Nat → Nat
distanceToBoundary start = 270 ∸ (start % 270)

nextBoundaryPeriod : Nat → Nat
nextBoundaryPeriod start = suc (start / 270)

residueIsAtMost270 : (start : Nat) → start % 270 ≤ 270
residueIsAtMost270 start =
  NP.≤-trans (NP.n≤1+n (start % 270)) (m%n<n start 270)

-- Convert the inherited Euclidean bound into a precise complement.
residueCompletes270 : (start : Nat) →
  start % 270 + distanceToBoundary start ≡ 270
residueCompletes270 start =
  trans
    (NP.+-comm (start % 270) (distanceToBoundary start))
    (NP.m∸n+n≡m (residueIsAtMost270 start))

-- Associativity + commutation used ONLY for Nat indices, not for
-- scalar summation (which remains ordered throughout).
moveTail : (a b c : Nat) →
  (a + b) + c ≡ (a + c) + b
moveTail a b c =
  trans
    (NP.+-assoc a b c)
    (trans
      (cong (a +_) (NP.+-comm b c))
      (sym (NP.+-assoc a c b)))

firstBoundaryExactForAnyStart : (start : Nat) →
  start + distanceToBoundary start
    ≡ nextBoundaryPeriod start * 270
firstBoundaryExactForAnyStart start =
  trans
    (cong (_+ distanceToBoundary start)
      (m≡m%n+[m/n]*n start 270))
    (trans
      (moveTail (start % 270)
        ((start / 270) * 270) (distanceToBoundary start))
      (cong
        (_+ ((start / 270) * 270))
        (residueCompletes270 start)))

-- Nat-translation preserves ≤; no scalar monotonicity claimed.
plusLeftMonotone :
  (prefix : Nat) {m n : Nat} →
  m ≤ n → prefix + m ≤ prefix + n
plusLeftMonotone zero bound = bound
plusLeftMonotone (suc prefix) bound =
  s≤s (plusLeftMonotone prefix bound)

shortWhenWithinDistance :
  (start count : Nat) →
  count ≤ distanceToBoundary start →
  start % 270 + count ≤ 270
shortWhenWithinDistance start count short =
  subst
    (λ end → start % 270 + count ≤ end)
    (residueCompletes270 start)
    (plusLeftMonotone (start % 270) short)

-- The arithmetic reverse of the 'within' comparison.
-- If r+count is NOT ≤270, then count ≥270-r.
mustCrossBoundary :
  (start count : Nat) →
  (start % 270 + count ≤ 270 → ⊥) →
  distanceToBoundary start ≤ count
mustCrossBoundary start count notWithin
  with NP.≤-total count (distanceToBoundary start)
... | inj₁ short =
  ⊥-elim (notWithin (shortWhenWithinDistance start count short))
... | inj₂ crosses = crosses

remainderAfterBoundary : Nat → Nat → Nat
remainderAfterBoundary start count =
  count ∸ distanceToBoundary start

-- EXACT interval length: prefix + q*270 + r.
-- The proof uses the same stdlib Euclidean identity as the original
-- full NatPeriod270 codec; it does not use a bounded search table.
splitCountAtBoundary :
  (start count : Nat) →
  distanceToBoundary start ≤ count →
  count ≡
    distanceToBoundary start
      + ((remainderAfterBoundary start count / 270) * 270
          + remainderAfterBoundary start count % 270)
splitCountAtBoundary start count prefix≤count =
  trans
    (sym (NP.m∸n+n≡m prefix≤count))
    (trans
      (NP.+-comm
        (remainderAfterBoundary start count)
        (distanceToBoundary start))
      (cong
        (distanceToBoundary start +_)
        (trans
          (m≡m%n+[m/n]*n
            (remainderAfterBoundary start count) 270)
          (NP.+-comm
            (remainderAfterBoundary start count % 270)
            ((remainderAfterBoundary start count / 270) * 270)))))

-- This is the formerly missing TOTAL CASE SPLIT.
-- One case uses a direct residual fold; the other constructs
-- the precise prefix/whole-period/suffix evidence.
completeIntervalPlan :
  (start count : Nat) →
  Plan.CompleteIntervalPlan start count
completeIntervalPlan start count
  with NP._≤?_ (start % 270 + count) 270
... | yes contained = Plan.withinOnePeriod contained
... | no notContained =
  Plan.crossingPeriod
    (Schedule.certified-interval-schedule
      (distanceToBoundary start)
      (nextBoundaryPeriod start)
      (remainderAfterBoundary start count / 270)
      (remainderAfterBoundary start count % 270)
      (firstBoundaryExactForAnyStart start)
      (splitCountAtBoundary start count
        (mustCrossBoundary start count notContained)))

-- Compose TOTAL constructive plan with the original proof-bearing
-- paired-correlation BIDI. All intervals, both directions.
totalIntervalCorrelationForward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
  ≡
  Plan.planCorrelationSum S C start count
    (completeIntervalPlan start count)
totalIntervalCorrelationForward S M C start count =
  Plan.completePlanForward S M C start count
    (completeIntervalPlan start count)

totalIntervalCorrelationBackward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  Plan.planCorrelationSum S C start count
    (completeIntervalPlan start count)
  ≡
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
totalIntervalCorrelationBackward S M C start count =
  Plan.completePlanBackward S M C start count
    (completeIntervalPlan start count)

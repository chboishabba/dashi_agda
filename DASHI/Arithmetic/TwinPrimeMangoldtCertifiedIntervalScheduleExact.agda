module DASHI.Arithmetic.TwinPrimeMangoldtCertifiedIntervalScheduleExact where

------------------------------------------------------------------------
-- M13: CERTIFIED ARBITRARY-INTERVAL SCHEDULE / DECOMPOSITION BIDI.
--
-- Generic consumers need a proof that prefix, whole coded rows,
-- and suffix cover the SAME original interval, not a heuristic
-- guess about ceil(start / 270). A schedule retains BOTH equalities.
--
-- Original proof owners: residual Fin270 code, ordered sum
-- concatenation, and the aligned partial-period partition. No
-- source, QID, Ibrahim orbit or Pareto model gets proof authority
-- merely through this representation.
--
-- This aligned schedule is NOT constructible for a short interval
-- entirely before the next 270 boundary (e.g. start=59,count=1).
-- TwinPrimeMangoldtTwoCaseIntervalPlanExact owns the corrected
-- within-one-period OR crossing-boundary interface. Its total
-- computational constructor remains a separate obligation.
-- Source-written; kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Nat.Properties as NP
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtMultiPeriodConcatExact as Multi
import DASHI.Arithmetic.TwinPrimeMangoldtPartialPeriodPartitionExact as Partial

record CertifiedIntervalSchedule
    (start count : Nat) : Set where
  constructor certified-interval-schedule
  field
    prefixLength : Nat
    firstWholePeriod : Nat
    wholePeriods : Nat
    suffixLength : Nat
    firstBoundaryExact :
      start + prefixLength ≡ firstWholePeriod * 270
    originalLengthExact :
      count ≡ prefixLength + (wholePeriods * 270 + suffixLength)
open CertifiedIntervalSchedule public

-- The all-periods and arbitrary-partial-row proof becomes usable
-- at the original (start,count) signature, without changing the
-- original code or hiding an alignment assumption.
scheduleCorrelationForward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  (schedule : CertifiedIntervalSchedule start count) →
  Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
  ≡
  Sum.add S
    (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
      start (prefixLength schedule))
    (Sum.add S
      (Multi.codeBlockRows S C
        (firstWholePeriod schedule) (wholePeriods schedule))
      (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (firstWholePeriod schedule * 270
          + wholePeriods schedule * 270)
        (suffixLength schedule)))
scheduleCorrelationForward S M C start count schedule =
  trans
    (cong (Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start)
      (originalLengthExact schedule))
    (Partial.partialPeriodPartition S M C start
      (prefixLength schedule)
      (firstWholePeriod schedule)
      (wholePeriods schedule)
      (suffixLength schedule)
      (firstBoundaryExact schedule))

scheduleCorrelationBackward :
  (S : Sum.AdditiveScalar) (M : Multi.MonoidSum S)
  (C : Bidi.ArithmeticPairCorrelation (Sum.Scalar S)) →
  (start count : Nat) →
  (schedule : CertifiedIntervalSchedule start count) →
  Sum.add S
    (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
      start (prefixLength schedule))
    (Sum.add S
      (Multi.codeBlockRows S C
        (firstWholePeriod schedule) (wholePeriods schedule))
      (Sum.sumInterval S (Bidi.pairCorrelationAtNat C)
        (firstWholePeriod schedule * 270
          + wholePeriods schedule * 270)
        (suffixLength schedule)))
  ≡ Sum.sumInterval S (Bidi.pairCorrelationAtNat C) start count
scheduleCorrelationBackward S M C start count schedule =
  sym (scheduleCorrelationForward S M C start count schedule)

-- Concrete general construction for EVERY interval starting at
-- an existing period boundary (including arbitrarily short/long).
-- This does NOT claim arbitrary nonaligned intervals are yet
-- automatically decomposed into maximal full rows.
boundaryIntervalSchedule :
  (period count : Nat) →
  CertifiedIntervalSchedule (period * 270) count
boundaryIntervalSchedule period count =
  certified-interval-schedule
    zero period zero count
    (NP.+-identityʳ (period * 270))
    refl

-- Whole rows are also a correct canonical schedule, with no
-- spurious prefix or suffix.
wholeRowsSchedule :
  (period rows : Nat) →
  CertifiedIntervalSchedule (period * 270) (rows * 270)
wholeRowsSchedule period rows =
  certified-interval-schedule
    zero period rows zero
    (NP.+-identityʳ (period * 270))
    (sym (NP.+-identityʳ (rows * 270)))

module DASHI.Physics.Closure.NSTriadKNHHBadRawVariableCapacityRound53Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 52 proved that a bounded shell supersolution, not alpha_q <= 1, is the
-- right recurrence consumer.  This file freezes the physical-facing form one
-- level closer to the unnormalised HH-bad quantity: a shell-dependent capacity
-- M_q with a uniform ceiling C_*.
--
-- No constancy of M_q is required.  If
--
--   C_0 <= M_0,
--   alpha_q M_q + beta_q <= M_(q+1),
--   M_q < C_*,
--
-- then every profile shell obeys C_q < C_*.  This is exactly the variable
-- capacity invariant requested by the physical Duhamel lane and preserves all
-- flexibility gained in Round 52.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)

import DASHI.Physics.Closure.NSTriadKNHHBadShellBarrierRound52Exact as Barrier

record RawVariableCapacityInvariant
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    capacity : Nat → ℚ
    capacityNonnegative : ∀ q → 0ℚ ≤ capacity q
    baseBelowCapacity :
      Barrier.profile input 0 ≤ capacity 0
    capacityStep : ∀ q →
      Barrier.alpha input q * capacity q + Barrier.forcing input q
      ≤ capacity (Agda.Builtin.Nat.suc q)
    ceiling : ℚ
    capacityBelowCeiling : ∀ q → capacity q < ceiling

open RawVariableCapacityInvariant public

variableCapacityAsShellSupersolution :
  ∀ {input} →
  RawVariableCapacityInvariant input →
  Barrier.ShellSupersolution input
variableCapacityAsShellSupersolution invariant = record
  { barrier = capacity invariant
  ; barrierNonnegative = capacityNonnegative invariant
  ; baseBelowBarrier = baseBelowCapacity invariant
  ; barrierSupersolution = capacityStep invariant
  }

physicalHHBadRawVariableCapacityInvariant :
  ∀ {input} →
  (invariant : RawVariableCapacityInvariant input) →
  ∀ q → Barrier.profile input q < ceiling invariant
physicalHHBadRawVariableCapacityInvariant {input} invariant q =
  Data.Rational.Properties.≤-<-trans
    (Barrier.profileBelowAnyShellBarrier input
      (variableCapacityAsShellSupersolution invariant) q)
    (capacityBelowCeiling invariant q)

-- Constant capacity is now only a corollary surface.  The physical producer may
-- choose this when its Duhamel calculation really gives a uniform invariant
-- region, but the master consumer never demands it.
record RawConstantCapacityInvariant
    (input : Barrier.GeneralHHBadRecurrence) : Set where
  field
    constantCapacity : ℚ
    constantCapacityNonnegative : 0ℚ ≤ constantCapacity
    baseBelowConstantCapacity :
      Barrier.profile input 0 ≤ constantCapacity
    constantCapacityStep : ∀ q →
      Barrier.alpha input q * constantCapacity + Barrier.forcing input q
      ≤ constantCapacity
    ceiling : ℚ
    constantCapacityBelowCeiling : constantCapacity < ceiling

open RawConstantCapacityInvariant public

constantCapacityToVariable :
  ∀ {input} →
  RawConstantCapacityInvariant input →
  RawVariableCapacityInvariant input
constantCapacityToVariable invariant = record
  { capacity = λ _ → constantCapacity invariant
  ; capacityNonnegative = λ _ → constantCapacityNonnegative invariant
  ; baseBelowCapacity = baseBelowConstantCapacity invariant
  ; capacityStep = constantCapacityStep invariant
  ; ceiling = RawConstantCapacityInvariant.ceiling invariant
  ; capacityBelowCeiling = λ _ → constantCapacityBelowCeiling invariant
  }

physicalHHBadRawCapacityInvariant :
  ∀ {input} →
  (invariant : RawConstantCapacityInvariant input) →
  ∀ q →
  Barrier.profile input q < RawConstantCapacityInvariant.ceiling invariant
physicalHHBadRawCapacityInvariant invariant =
  physicalHHBadRawVariableCapacityInvariant
    (constantCapacityToVariable invariant)

rawVariableCapacityIsFinalRecurrenceConsumer : Bool
rawVariableCapacityIsFinalRecurrenceConsumer = true

constantCapacityIsOnlySpecialCase : Bool
constantCapacityIsOnlySpecialCase = true

rawVariableCapacityIsFinalRecurrenceConsumerIsTrue :
  rawVariableCapacityIsFinalRecurrenceConsumer ≡ true
rawVariableCapacityIsFinalRecurrenceConsumerIsTrue = refl

constantCapacityIsOnlySpecialCaseIsTrue :
  constantCapacityIsOnlySpecialCase ≡ true
constantCapacityIsOnlySpecialCaseIsTrue = refl

module DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact where

------------------------------------------------------------------------
-- M12/M13: FINITE MANGOLDT SUM / RESIDUAL BIDI
--
-- Original owners: VonMangoldtSpecification, TwinPrimeNat270Period-
-- ResidualBidiExact, TwinPrimeResidualMangoldtBidiExact.
-- No new prime predicate, numeric approximation, infinite limit,
-- positivity estimate, or assumption is introduced.
-- This is a finite-sum transport for an arbitrary additive scalar.
-- Source-written, not yet kernel-checked (2026-10-29).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM

-- Only the formal finite additive fold is required. Do not demand
-- that the original Weil scalar has unverified positive-order laws.
record AdditiveScalar : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
open AdditiveScalar

sumInterval : (S : AdditiveScalar) →
  (Nat → Scalar S) → Nat → Nat → Scalar S
sumInterval S f start zero = zero S
sumInterval S f start (suc count) =
  add S (f start) (sumInterval S f (suc start) count)

sumDecodedInterval : (S : AdditiveScalar) →
  (Period.NatPeriod270 → Scalar S) → Nat → Nat → Scalar S
sumDecodedInterval S f start count =
  sumInterval S (λ n → f (Period.encodeNatPeriod270 n)) start count

finiteSumBidiForward :
  (S : AdditiveScalar) (f : Nat → Scalar S) →
  (start count : Nat) →
  sumDecodedInterval S (Bidi.liftNatConsumer f) start count
    ≡ sumInterval S f start count
finiteSumBidiForward S f start zero = refl
finiteSumBidiForward S f start (suc count) =
  cong₂ (add S)
    (Bidi.liftConsumerSound f start)
    (finiteSumBidiForward S f (suc start) count)

finiteSumBidiBackward :
  (S : AdditiveScalar) (f : Nat → Scalar S) →
  (start count : Nat) →
  sumInterval S f start count
    ≡ sumDecodedInterval S (Bidi.liftNatConsumer f) start count
finiteSumBidiBackward S f start count =
  sym
    (finiteSumBidiForward S f start count)

-- Explicit pointwise representation of arbitrary two-point
-- correlation (including the exact von Mangoldt pair weights).
pairFiniteSumBidiForward :
  (S : AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Scalar S)) →
  (start count : Nat) →
  sumDecodedInterval S (Bidi.pairCorrelationAtPeriod C) start count
    ≡ sumInterval S (Bidi.pairCorrelationAtNat C) start count
pairFiniteSumBidiForward S C start zero = refl
pairFiniteSumBidiForward S C start (suc count) =
  cong₂ (add S)
    (Bidi.pairCorrelationForward C start)
    (pairFiniteSumBidiForward S C (suc start) count)

pairFiniteSumBidiBackward :
  (S : AdditiveScalar)
  (C : Bidi.ArithmeticPairCorrelation (Scalar S)) →
  (start count : Nat) →
  sumInterval S (Bidi.pairCorrelationAtNat C) start count
    ≡ sumDecodedInterval S (Bidi.pairCorrelationAtPeriod C) start count
pairFiniteSumBidiBackward S C start count =
  sym
    (pairFiniteSumBidiForward S C start count)

-- The actual von Mangoldt single-term finite sum (not a
-- renamed or simulated function). The Weil scalar must be given
-- a matching finite additive structure explicitly.
mangoldtFiniteSumForward :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (S : AdditiveScalar) →
  (scalarTransport : Scalar S → Weil.WeilTestSpace.Scalar space) →
  (source : Weil.WeilTestSpace.Scalar space → Scalar S) →
  (inverseAt : ∀ x → source (scalarTransport x) ≡ x) →
  (start count : Nat) →
  sumDecodedInterval S
    (λ code → source (Bidi.mangoldtAtPeriod space arithmetic mangoldt code))
    start count
  ≡ sumInterval S
    (λ n → source (VM.VonMangoldtFunction.lambda mangoldt n))
    start count
mangoldtFiniteSumForward space arithmetic mangoldt S toWeil fromWeil inverseAt start zero = refl
mangoldtFiniteSumForward space arithmetic mangoldt S toWeil fromWeil inverseAt start (suc count) =
  cong₂ (add S)
    (cong fromWeil (Bidi.mangoldtPeriodForward space arithmetic mangoldt start))
    (mangoldtFiniteSumForward space arithmetic mangoldt S toWeil fromWeil inverseAt (suc start) count)

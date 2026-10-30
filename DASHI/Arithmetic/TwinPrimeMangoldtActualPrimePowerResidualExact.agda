module DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact where

------------------------------------------------------------------------
-- M11/M14: THE ACTUAL VON MANGOLDT WEIGHT AT AN ARBITRARY PRIME POWER
--
-- Do not use the finite SSP valuation-depth proxy: the original
-- RiemannVonMangoldtSpecification.lambdaAtPrimePower theorem gives
-- Lambda(p^(k+1)) = log p (WITHOUT a factor of k+1).
-- PrimePowerCounting's occurrence family supplies the witness
-- for any later prime-power exception accounting. This module
-- reuses the actual Weil scalar, not a fabricated Nat-valued log.
--
-- Source-written, Agda kernel pending, 30 October 2026.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Analysis.RiemannPrimePowerCounting as PrimePower
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi

actualMangoldtPair :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  VM.VonMangoldtFunction space arithmetic →
  Bidi.ArithmeticPairCorrelation (Weil.WeilTestSpace.Scalar space)
actualMangoldtPair space arithmetic mangoldt = record
  { lambdaWeight = VM.VonMangoldtFunction.lambda mangoldt
  ; multiply = VM.AllPrimeArithmetic._*S_ arithmetic
  }

actualPairPeriodBidi :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  Bidi.pairCorrelationAtPeriod
    (actualMangoldtPair space arithmetic mangoldt)
    (Period.encodeNatPeriod270 n)
  ≡
  VM.AllPrimeArithmetic._*S_ arithmetic
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (VM.VonMangoldtFunction.lambda mangoldt (n + 2))
actualPairPeriodBidi space arithmetic mangoldt n =
  Bidi.pairCorrelationForward
    (actualMangoldtPair space arithmetic mangoldt) n

actualPairPeriodBidiBack :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (code : Period.NatPeriod270) →
  Bidi.pairCorrelationAtNat
    (actualMangoldtPair space arithmetic mangoldt)
    (Period.decodeNatPeriod270 code)
  ≡
  Bidi.pairCorrelationAtPeriod
    (actualMangoldtPair space arithmetic mangoldt) code
actualPairPeriodBidiBack space arithmetic mangoldt code =
  Bidi.pairCorrelationBackward
    (actualMangoldtPair space arithmetic mangoldt) code

mangoldtPrimePowerPeriod :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (p : VM.AllPrimeArithmetic.Prime arithmetic) →
  (exponentIndex : Nat) →
  Bidi.mangoldtAtPeriod space arithmetic mangoldt
    (Period.encodeNatPeriod270
      (VM.primePowerNat space arithmetic p exponentIndex))
  ≡ VM.AllPrimeArithmetic.logPrimeWeight arithmetic p
mangoldtPrimePowerPeriod space arithmetic mangoldt p exponentIndex =
  trans
    (Bidi.mangoldtPeriodForward space arithmetic mangoldt
      (VM.primePowerNat space arithmetic p exponentIndex))
    (VM.lambdaAtPrimePower space arithmetic mangoldt
      p exponentIndex)

-- Instantiated through the original proof-bearing occurrence type.
occurrenceMangoldtPeriod :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (occur : PrimePower.PrimePowerOccurrence space arithmetic) →
  Bidi.mangoldtAtPeriod space arithmetic mangoldt
    (Period.encodeNatPeriod270
      (PrimePower.occurrenceValue space arithmetic occur))
  ≡ VM.AllPrimeArithmetic.logPrimeWeight arithmetic
      (PrimePower.occurrencePrime occur)
occurrenceMangoldtPeriod space arithmetic mangoldt
    (PrimePower.occurrence p exponentIndex) =
  mangoldtPrimePowerPeriod space arithmetic mangoldt p exponentIndex

actualPairAtPrimePower :
  (space : Weil.WeilTestSpace) →
  (arithmetic : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (p : VM.AllPrimeArithmetic.Prime arithmetic) →
  (exponentIndex : Nat) →
  Bidi.pairCorrelationAtPeriod
    (actualMangoldtPair space arithmetic mangoldt)
    (Period.encodeNatPeriod270
      (VM.primePowerNat space arithmetic p exponentIndex))
  ≡
  VM.AllPrimeArithmetic._*S_ arithmetic
    (VM.AllPrimeArithmetic.logPrimeWeight arithmetic p)
    (VM.VonMangoldtFunction.lambda mangoldt
      (VM.primePowerNat space arithmetic p exponentIndex + 2))
actualPairAtPrimePower space arithmetic mangoldt p exponentIndex =
  trans
    (actualPairPeriodBidi space arithmetic mangoldt
      (VM.primePowerNat space arithmetic p exponentIndex))
    (cong
      (λ weight →
        VM.AllPrimeArithmetic._*S_ arithmetic weight
          (VM.VonMangoldtFunction.lambda mangoldt
            (VM.primePowerNat space arithmetic p exponentIndex + 2)))
      (VM.lambdaAtPrimePower space arithmetic mangoldt
        p exponentIndex))

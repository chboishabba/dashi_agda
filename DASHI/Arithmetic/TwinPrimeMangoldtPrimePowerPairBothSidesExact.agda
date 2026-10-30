module DASHI.Arithmetic.TwinPrimeMangoldtPrimePowerPairBothSidesExact where

------------------------------------------------------------------------
-- M14: ACTUAL PRIME-POWER CONTRIBUCTIONS AT BOTH PAIR ENDPOINTS
--
-- ORIGINAL OWNERS (import; do not copy or redefine):
-- RiemannVonMangoldtSpecification.lambdaAtPrimePower;
-- RiemannPrimePowerCounting.PrimePowerOccurrence;
-- TwinPrimeMangoldtActualPrimePowerResidualExact.actualMangoldtPair.
--
-- Unlike the weighted-valuation energy, Lambda(p^k) = log(p),
-- including k > 1. Left, right and simultaneous occurrence are
-- treated separately: "prime power" does not mean "prime".
-- This is a proof of exact conditional weights, NOT of a finite
-- asymptotic prime-power error bound or prime-pair positivity.
-- Source-written; Agda kernel pending. 30 October 2026.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Analysis.RiemannPrimePowerCounting as PP
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period

-- A proper-power occurrence is explicitly exponent index (suc k),
-- corresponding to p^(k+2), not a certified prime.
record ProperPrimePowerOccurrence
    (space : Weil.WeilTestSpace)
    (arith : VM.AllPrimeArithmetic space) : Set where
  constructor proper-prime-power
  field
    prime : VM.AllPrimeArithmetic.Prime arith
    positiveIndex : Nat
open ProperPrimePowerOccurrence public

properPowerAsOccurrence :
  {space : Weil.WeilTestSpace} →
  {arith : VM.AllPrimeArithmetic space} →
  ProperPrimePowerOccurrence space arith →
  PP.PrimePowerOccurrence space arith
properPowerAsOccurrence (proper-prime-power p k) =
  PP.occurrence p (Agda.Builtin.Nat.suc k)

properPowerValue :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  ProperPrimePowerOccurrence space arith → Nat
properPowerValue space arith proper =
  PP.occurrenceValue space arith (properPowerAsOccurrence proper)

properPowerMangoldtPeriod :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (proper : ProperPrimePowerOccurrence space arith) →
  Bidi.mangoldtAtPeriod space arith mangoldt
    (Period.encodeNatPeriod270
      (properPowerValue space arith proper))
  ≡ VM.AllPrimeArithmetic.logPrimeWeight arith
      (prime proper)
properPowerMangoldtPeriod space arith mangoldt
    (proper-prime-power p k) =
  Actual.mangoldtPrimePowerPeriod space arith mangoldt
    p (Agda.Builtin.Nat.suc k)

-- General RIGHT ENDPOINT: a supplied genuine equality n+2=p^j
-- is essential; the weight is inherited from the original
-- relational Mangoldt specification.
rightPrimePowerWeight :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  (q : VM.AllPrimeArithmetic.Prime arith) →
  (j : Nat) →
  n + 2 ≡ VM.primePowerNat space arith q j →
  Bidi.pairCorrelationAtNat
    (Actual.actualMangoldtPair space arith mangoldt) n
  ≡
  VM.AllPrimeArithmetic._*S_ arith
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (VM.AllPrimeArithmetic.logPrimeWeight arith q)
rightPrimePowerWeight space arith mangoldt n q j eq =
  cong
    (VM.AllPrimeArithmetic._*S_ arith
      (VM.VonMangoldtFunction.lambda mangoldt n))
    (trans
      (cong (VM.VonMangoldtFunction.lambda mangoldt) eq)
      (VM.lambdaAtPrimePower space arith mangoldt q j))

-- Simultaneous prime-power endpoints: both original certificates,
-- not a synthetically promoted survivor of the 2/3/5 wheel.
bothPrimePowerWeights :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  (p q : VM.AllPrimeArithmetic.Prime arith) →
  (i j : Nat) →
  n ≡ VM.primePowerNat space arith p i →
  n + 2 ≡ VM.primePowerNat space arith q j →
  Bidi.pairCorrelationAtNat
    (Actual.actualMangoldtPair space arith mangoldt) n
  ≡
  VM.AllPrimeArithmetic._*S_ arith
    (VM.AllPrimeArithmetic.logPrimeWeight arith p)
    (VM.AllPrimeArithmetic.logPrimeWeight arith q)
bothPrimePowerWeights space arith mangoldt n p q i j eqL eqR =
  trans
    (cong
      (λ w →
        VM.AllPrimeArithmetic._*S_ arith w
          (VM.VonMangoldtFunction.lambda mangoldt (n + 2)))
      (trans
        (cong (VM.VonMangoldtFunction.lambda mangoldt) eqL)
        (VM.lambdaAtPrimePower space arith mangoldt p i)))
    (cong
      (VM.AllPrimeArithmetic._*S_ arith
        (VM.AllPrimeArithmetic.logPrimeWeight arith p))
      (trans
        (cong (VM.VonMangoldtFunction.lambda mangoldt) eqR)
        (VM.lambdaAtPrimePower space arith mangoldt q j)))

-- The SAME power-pair result after the genuine unbounded period
-- encoding, not a fabricated 27-cell finite-value classifier.
bothPrimePowerPeriodBidi :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  (p q : VM.AllPrimeArithmetic.Prime arith) →
  (i j : Nat) →
  n ≡ VM.primePowerNat space arith p i →
  n + 2 ≡ VM.primePowerNat space arith q j →
  Bidi.pairCorrelationAtPeriod
    (Actual.actualMangoldtPair space arith mangoldt)
    (Period.encodeNatPeriod270 n)
  ≡
  VM.AllPrimeArithmetic._*S_ arith
    (VM.AllPrimeArithmetic.logPrimeWeight arith p)
    (VM.AllPrimeArithmetic.logPrimeWeight arith q)
bothPrimePowerPeriodBidi space arith mangoldt n p q i j eqL eqR =
  trans
    (Actual.actualPairPeriodBidi space arith mangoldt n)
    (bothPrimePowerWeights space arith mangoldt n p q i j eqL eqR)

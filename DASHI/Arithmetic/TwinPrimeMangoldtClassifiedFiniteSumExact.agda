module DASHI.Arithmetic.TwinPrimeMangoldtClassifiedFiniteSumExact where

------------------------------------------------------------------------
-- M14 EXACT FINITE CORRELATION SUM FROM THE ORIGINAL 3x3 SUPPORT
--
-- Proof owners: RiemannVonMangoldtSpecification.VonMangoldtAt and
-- its single-valued scalar law; prior M14 classified endpoint
-- construction; TwinPrimeResidualMangoldtFiniteSumBidiExact
-- and TwinPrimeMangoldtActualPrimePowerResidualExact.
--
-- This file does NOT identify all prime-power terms as primes, does
-- NOT assert scalar positivity, and does NOT derive the analytic
-- gap-two correlation lower bound. It is an exact finite identity
-- without requiring monoid associativity/commutativity.
--
-- Johl Brown-directed DASHI bridge, source written 2026-10-30.
-- Kernel check remains pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeMangoldtExhaustiveSupportCaseExact as Cases
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Residual
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeResidualMangoldtFiniteSumBidiExact as Sum
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period
import DASHI.Arithmetic.TwinPrimeWeilActualCorrelationPartitionExact as WeilBridge

-- The weight of the ORIGINAL classified prime-power case.
-- At exponent one and exponent >=2 the scalar is the SAME log p;
-- outside the prime powers the scalar is zero.
supportWeight :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space) →
  {n : Nat} →
  Cases.MangoldtSupportCase space arithmetic n →
  Weil.WeilTestSpace.Scalar space
supportWeight space arithmetic (Cases.exponentOne p eq) =
  VM.AllPrimeArithmetic.logPrimeWeight arithmetic p
supportWeight space arithmetic (Cases.exponentAtLeastTwo p k eq) =
  VM.AllPrimeArithmetic.logPrimeWeight arithmetic p
supportWeight space arithmetic (Cases.noPrimePower outside) =
  Weil.WeilTestSpace.zeroS space

supportWeightCorrect :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  {n : Nat} →
  (case : Cases.MangoldtSupportCase space arithmetic n) →
  VM.VonMangoldtFunction.lambda mangoldt n
    ≡ supportWeight space arithmetic case
supportWeightCorrect space arithmetic mangoldt
    (Cases.exponentOne p eq) =
  Cases.mangoldtValueAtExponentOne
    space arithmetic mangoldt _ p eq
supportWeightCorrect space arithmetic mangoldt
    (Cases.exponentAtLeastTwo p k eq) =
  Cases.mangoldtValueAtProperPower
    space arithmetic mangoldt _ p k eq
supportWeightCorrect space arithmetic mangoldt
    (Cases.noPrimePower outside) =
  Cases.mangoldtValueOutside
    space arithmetic mangoldt _ outside

-- Exact pair weight from the original two endpoint certificates.
pairSupportWeight :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space) →
  {n : Nat} →
  Cases.BothEndpointsClassified space arithmetic n →
  Weil.WeilTestSpace.Scalar space
pairSupportWeight space arithmetic (left , right) =
  VM.AllPrimeArithmetic._*S_ arithmetic
    (supportWeight space arithmetic left)
    (supportWeight space arithmetic right)

-- Evaluate ALL Nats by reading the ORIGINAL lambdaSpecified proof.
classifiedPairWeight :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Weil.WeilTestSpace.Scalar space
classifiedPairWeight space arithmetic mangoldt n =
  pairSupportWeight space arithmetic
    (Cases.allPairSupportCases space arithmetic mangoldt n)

classifiedPairWeightExact :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  Residual.pairCorrelationAtNat
    (Actual.actualMangoldtPair space arithmetic mangoldt) n
  ≡ classifiedPairWeight space arithmetic mangoldt n
classifiedPairWeightExact space arithmetic mangoldt n =
  cong₂ (VM.AllPrimeArithmetic._*S_ arithmetic)
    (supportWeightCorrect space arithmetic mangoldt
      (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt n))
    (supportWeightCorrect space arithmetic mangoldt
      (Cases.supportCaseFromActualMangoldt space arithmetic mangoldt
        (n + 2)))

-- The SAME classified weight in the lossless unbounded period code.
classifiedPairPeriodExact :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  Residual.pairCorrelationAtPeriod
    (Actual.actualMangoldtPair space arithmetic mangoldt)
    (Period.encodeNatPeriod270 n)
  ≡ classifiedPairWeight space arithmetic mangoldt n
classifiedPairPeriodExact space arithmetic mangoldt n =
  trans
    (Actual.actualPairPeriodBidi space arithmetic mangoldt n)
    (classifiedPairWeightExact space arithmetic mangoldt n)

classifiedFiniteCorrelation :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Nat → Weil.WeilTestSpace.Scalar space
classifiedFiniteCorrelation space arithmetic mangoldt start count =
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (classifiedPairWeight space arithmetic mangoldt)
    start count

-- The key M14 paydown: for arbitrary finite intervals, the exact
-- classical von Mangoldt pair sum equals the completely classified
-- finite fold. Does NOT assume a symbolic/nonzero term is prime-prime.
finiteCorrelationClassifiedExact :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (start count : Nat) →
  Sum.sumInterval (WeilBridge.weilAdditive space)
    (Residual.pairCorrelationAtNat
      (Actual.actualMangoldtPair space arithmetic mangoldt))
    start count
  ≡ classifiedFiniteCorrelation space arithmetic mangoldt
      start count
finiteCorrelationClassifiedExact space arithmetic mangoldt start zero =
  refl
finiteCorrelationClassifiedExact space arithmetic mangoldt start
    (suc count) =
  cong₂ (Weil.WeilTestSpace._+S_ space)
    (classifiedPairWeightExact space arithmetic mangoldt start)
    (finiteCorrelationClassifiedExact space arithmetic mangoldt
      (suc start) count)

module DASHI.Arithmetic.TwinPrimeMangoldtExhaustiveSupportCaseExact where

------------------------------------------------------------------------
-- M14: EXHAUSTIVE PRIME / PROPER PRIME POWER / OUTSIDE CLASSIFICATION.
--
-- Do not reconstruct a new primality oracle: pattern-match ORIGINAL
-- RiemannVonMangoldtSpecification.VonMangoldtAt.lambdaSpecified.
-- Exponent index zero = p^1; index suc k = p^(k+2) proper
-- prime power, NOT a second kind of certified prime.
--
-- Every (n,n+2) gets two exhaustive support classifications.
-- Exact weights come from the ORIGINAL specificationSingleValued;
-- all-prime carrier identity remains owned by AllPrimeArithmetic.
-- No count, estimate, lower bound or prime-pair infinitude follows.
-- Source-written; Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM

data MangoldtSupportCase
  (space : Weil.WeilTestSpace)
  (arith : VM.AllPrimeArithmetic space)
  (n : Nat) : Set where
  exponentOne :
    (p : VM.AllPrimeArithmetic.Prime arith) →
    n ≡ VM.primePowerNat space arith p zero →
    MangoldtSupportCase space arith n
  exponentAtLeastTwo :
    (p : VM.AllPrimeArithmetic.Prime arith) →
    (k : Nat) →
    n ≡ VM.primePowerNat space arith p (suc k) →
    MangoldtSupportCase space arith n
  noPrimePower :
    ((p : VM.AllPrimeArithmetic.Prime arith) →
      (k : Nat) →
      VM._≢_ n (VM.primePowerNat space arith p k)) →
    MangoldtSupportCase space arith n

supportCaseFromActualMangoldt :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  MangoldtSupportCase space arith n
supportCaseFromActualMangoldt space arith mangoldt n
  with VM.VonMangoldtFunction.lambdaSpecified mangoldt n
... | VM.atPrimePower p zero eq = exponentOne p eq
... | VM.atPrimePower p (suc k) eq = exponentAtLeastTwo p k eq
... | VM.outsidePrimePowers outside = noPrimePower outside

mangoldtValueAtExponentOne :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  (p : VM.AllPrimeArithmetic.Prime arith) →
  (eq : n ≡ VM.primePowerNat space arith p zero) →
  VM.VonMangoldtFunction.lambda mangoldt n
  ≡ VM.AllPrimeArithmetic.logPrimeWeight arith p
mangoldtValueAtExponentOne space arith mangoldt n p eq =
  VM.VonMangoldtFunction.specificationSingleValued mangoldt n
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (VM.AllPrimeArithmetic.logPrimeWeight arith p)
    (VM.VonMangoldtFunction.lambdaSpecified mangoldt n)
    (VM.atPrimePower p zero eq)

mangoldtValueAtProperPower :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  (p : VM.AllPrimeArithmetic.Prime arith) →
  (k : Nat) →
  (eq : n ≡ VM.primePowerNat space arith p (suc k)) →
  VM.VonMangoldtFunction.lambda mangoldt n
  ≡ VM.AllPrimeArithmetic.logPrimeWeight arith p
mangoldtValueAtProperPower space arith mangoldt n p k eq =
  VM.VonMangoldtFunction.specificationSingleValued mangoldt n
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (VM.AllPrimeArithmetic.logPrimeWeight arith p)
    (VM.VonMangoldtFunction.lambdaSpecified mangoldt n)
    (VM.atPrimePower p (suc k) eq)

mangoldtValueOutside :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  ((p : VM.AllPrimeArithmetic.Prime arith) →
   (k : Nat) →
   VM._≢_ n (VM.primePowerNat space arith p k)) →
  VM.VonMangoldtFunction.lambda mangoldt n
  ≡ Weil.WeilTestSpace.zeroS space
mangoldtValueOutside space arith mangoldt n outside =
  VM.VonMangoldtFunction.specificationSingleValued mangoldt n
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (Weil.WeilTestSpace.zeroS space)
    (VM.VonMangoldtFunction.lambdaSpecified mangoldt n)
    (VM.outsidePrimePowers outside)

-- This Cartesian product is the FULL 3x3 support-case split;
-- its 9 cases are logical categories, not new 3x3x3 geometry
-- or a numerical Monster/RGS correspondence.
BothEndpointsClassified :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  Nat → Set
BothEndpointsClassified space arith n =
  MangoldtSupportCase space arith n
  × MangoldtSupportCase space arith (n + 2)

allPairSupportCases :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  BothEndpointsClassified space arith n
allPairSupportCases space arith mangoldt n =
  supportCaseFromActualMangoldt space arith mangoldt n ,
  supportCaseFromActualMangoldt space arith mangoldt (n + 2)

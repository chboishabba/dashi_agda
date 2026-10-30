module DASHI.Arithmetic.TwinPrimeMangoldtOutsidePrimePowersZeroExact where

------------------------------------------------------------------------
-- M14: OUTSIDE PRIME POWERS THE ACTUAL VON MANGOLDT WEIGHT IS ZERO.
--
-- Reuses the ORIGINAL relational VonMangoldtAt constructors and
-- specificationSingleValued; does not synthesize a decider for
-- all-prime support or invent an analytic lower bound.
-- Explicit zero-annihilation laws are required of multiplication:
-- they do NOT follow from an arbitrary WeilTestSpace record.
-- Source-written; Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeMangoldtActualPrimePowerResidualExact as Actual
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period

-- Exact original type-level negation of *every* positive prime power.
OutsideAllPrimePowers :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  Nat → Set
OutsideAllPrimePowers space arith n =
  (p : VM.AllPrimeArithmetic.Prime arith) →
  (index : Nat) →
  VM._≢_ n (VM.primePowerNat space arith p index)

mangoldtZeroOutside :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  (n : Nat) →
  OutsideAllPrimePowers space arith n →
  VM.VonMangoldtFunction.lambda mangoldt n
  ≡ Weil.WeilTestSpace.zeroS space
mangoldtZeroOutside space arith mangoldt n outside =
  VM.VonMangoldtFunction.specificationSingleValued mangoldt
    n
    (VM.VonMangoldtFunction.lambda mangoldt n)
    (Weil.WeilTestSpace.zeroS space)
    (VM.VonMangoldtFunction.lambdaSpecified mangoldt n)
    (VM.outsidePrimePowers outside)

record ProductZeroLaws
  (space : Weil.WeilTestSpace)
  (arith : VM.AllPrimeArithmetic space) : Set where
  field
    zeroLeft : (x : Weil.WeilTestSpace.Scalar space) →
      VM.AllPrimeArithmetic._*S_ arith
        (Weil.WeilTestSpace.zeroS space) x
      ≡ Weil.WeilTestSpace.zeroS space
    zeroRight : (x : Weil.WeilTestSpace.Scalar space) →
      VM.AllPrimeArithmetic._*S_ arith x
        (Weil.WeilTestSpace.zeroS space)
      ≡ Weil.WeilTestSpace.zeroS space
open ProductZeroLaws public

leftOutsidePairZero :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  ProductZeroLaws space arith →
  (n : Nat) → OutsideAllPrimePowers space arith n →
  Bidi.pairCorrelationAtNat
    (Actual.actualMangoldtPair space arith mangoldt) n
  ≡ Weil.WeilTestSpace.zeroS space
leftOutsidePairZero space arith mangoldt zeroLaws n outside =
  trans
    (cong
      (λ w → VM.AllPrimeArithmetic._*S_ arith w
        (VM.VonMangoldtFunction.lambda mangoldt (n + 2)))
      (mangoldtZeroOutside space arith mangoldt n outside))
    (zeroLeft zeroLaws
      (VM.VonMangoldtFunction.lambda mangoldt (n + 2)))

rightOutsidePairZero :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  ProductZeroLaws space arith →
  (n : Nat) → OutsideAllPrimePowers space arith (n + 2) →
  Bidi.pairCorrelationAtNat
    (Actual.actualMangoldtPair space arith mangoldt) n
  ≡ Weil.WeilTestSpace.zeroS space
rightOutsidePairZero space arith mangoldt zeroLaws n outside =
  trans
    (cong
      (VM.AllPrimeArithmetic._*S_ arith
        (VM.VonMangoldtFunction.lambda mangoldt n))
      (mangoldtZeroOutside space arith mangoldt (n + 2) outside))
    (zeroRight zeroLaws
      (VM.VonMangoldtFunction.lambda mangoldt n))

leftOutsidePairPeriodZero :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  ProductZeroLaws space arith →
  (n : Nat) → OutsideAllPrimePowers space arith n →
  Bidi.pairCorrelationAtPeriod
    (Actual.actualMangoldtPair space arith mangoldt)
    (Period.encodeNatPeriod270 n)
  ≡ Weil.WeilTestSpace.zeroS space
leftOutsidePairPeriodZero space arith mangoldt laws n outside =
  trans
    (Actual.actualPairPeriodBidi space arith mangoldt n)
    (leftOutsidePairZero space arith mangoldt laws n outside)

rightOutsidePairPeriodZero :
  (space : Weil.WeilTestSpace) →
  (arith : VM.AllPrimeArithmetic space) →
  (mangoldt : VM.VonMangoldtFunction space arith) →
  ProductZeroLaws space arith →
  (n : Nat) → OutsideAllPrimePowers space arith (n + 2) →
  Bidi.pairCorrelationAtPeriod
    (Actual.actualMangoldtPair space arith mangoldt)
    (Period.encodeNatPeriod270 n)
  ≡ Weil.WeilTestSpace.zeroS space
rightOutsidePairPeriodZero space arith mangoldt laws n outside =
  trans
    (Actual.actualPairPeriodBidi space arith mangoldt n)
    (rightOutsidePairZero space arith mangoldt laws n outside)

module DASHI.Arithmetic.TwinPrimeActualPairSectionGluingExact where

-- Concrete overlap gluing for the shifted arithmetic pair consumer.
-- Actual von Mangoldt values are supplied by the existing VM specification;
-- no new prime predicate, analytic bound, or independent gluing ontology.
-- Source written, kernel pending; no ESD edits.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact as Bidi
import DASHI.Arithmetic.TwinPrimeNat270PeriodResidualBidiExact as Period

-- A local chart carries two actual endpoint readings.
record PairSection (Scalar : Set) : Set₁ where
  field
    left : Nat → Scalar
    right : Nat → Scalar
open PairSection public

-- Overlap means the two charts agree on BOTH endpoint readings.
record PairOverlap {Scalar : Set}
    (a b : PairSection Scalar) (n : Nat) : Set where
  field
    leftAgreement : left a n ≡ left b n
    rightAgreement : right a n ≡ right b n
open PairOverlap public

pairValue : {Scalar : Set} →
  (Scalar → Scalar → Scalar) → PairSection Scalar → Nat → Scalar
pairValue mul s n = mul (left s n) (right s n)

pairGluingOnOverlap : {Scalar : Set} →
  (mul : Scalar → Scalar → Scalar) →
  (a b : PairSection Scalar) (n : Nat) →
  PairOverlap a b n →
  pairValue mul a n ≡ pairValue mul b n
pairGluingOnOverlap mul a b n overlap =
  cong₂ mul (leftAgreement overlap) (rightAgreement overlap)

-- One and the same genuine original Mangoldt producer at n and n+2.
actualMangoldtPair :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  PairSection (Weil.WeilTestSpace.Scalar space)
actualMangoldtPair space arithmetic mangoldt = record
  { left = VM.VonMangoldtFunction.lambda mangoldt
  ; right = λ n → VM.VonMangoldtFunction.lambda mangoldt (n + 2)
  }

actualPairConsumer :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Nat → Weil.WeilTestSpace.Scalar space
actualPairConsumer space arithmetic mangoldt =
  pairValue (VM.AllPrimeArithmetic._*S_ arithmetic)
    (actualMangoldtPair space arithmetic mangoldt)

actualPairRetained :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  Period.NatPeriod270 → Weil.WeilTestSpace.Scalar space
actualPairRetained space arithmetic mangoldt =
  Bidi.liftNatConsumer (actualPairConsumer space arithmetic mangoldt)

actualPairForward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  actualPairRetained space arithmetic mangoldt
    (Period.encodeNatPeriod270 n)
  ≡ actualPairConsumer space arithmetic mangoldt n
actualPairForward space arithmetic mangoldt =
  Bidi.liftConsumerSound (actualPairConsumer space arithmetic mangoldt)

actualPairBackward :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic) →
  (code : Period.NatPeriod270) →
  actualPairConsumer space arithmetic mangoldt
    (Period.decodeNatPeriod270 code)
  ≡ actualPairRetained space arithmetic mangoldt code
actualPairBackward space arithmetic mangoldt =
  Bidi.liftConsumerComplete (actualPairConsumer space arithmetic mangoldt)

-- Endpoint agreement is strictly stronger than equality of one-point
-- marginals or frequency energies; no cross-pair covariance estimated.

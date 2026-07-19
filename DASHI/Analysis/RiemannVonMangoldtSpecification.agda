module DASHI.Analysis.RiemannVonMangoldtSpecification where

-- Exact type-level specification of the von Mangoldt function.
--
-- Λ(n) = log p when n = p^k for a prime p and k ≥ 1, and Λ(n) = 0
-- otherwise.  The definition is relational so no unproved decision procedure
-- for primality or prime-power recognition is smuggled into the function.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannPrimePowerArithmetic using (natPow)

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record AllPrimeArithmetic (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    Prime : Set
    toNat : Prime → Nat
    toNatInjective :
      {p q : Prime} →
      toNat p ≡ toNat q →
      p ≡ q

    logPrimeWeight : Prime → Scalar
    _*S_ : Scalar → Scalar → Scalar
    sampleAtNat : Test → Nat → Scalar

primePowerNat :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  AllPrimeArithmetic.Prime arithmetic →
  Nat →
  Nat
primePowerNat space arithmetic p exponentIndex =
  natPow
    (AllPrimeArithmetic.toNat arithmetic p)
    (suc exponentIndex)

data VonMangoldtAt
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space)
  (n : Nat) :
  WeilTestSpace.Scalar space → Set where

  atPrimePower :
    (p : AllPrimeArithmetic.Prime arithmetic) →
    (exponentIndex : Nat) →
    n ≡ primePowerNat space arithmetic p exponentIndex →
    VonMangoldtAt space arithmetic n
      (AllPrimeArithmetic.logPrimeWeight arithmetic p)

  outsidePrimePowers :
    ((p : AllPrimeArithmetic.Prime arithmetic) →
      (exponentIndex : Nat) →
      n ≢ primePowerNat space arithmetic p exponentIndex) →
    VonMangoldtAt space arithmetic n
      (WeilTestSpace.zeroS space)

record VonMangoldtFunction
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space) : Set₁ where
  open WeilTestSpace space
  field
    lambda : Nat → Scalar

    lambdaSpecified :
      (n : Nat) →
      VonMangoldtAt space arithmetic n (lambda n)

    specificationSingleValued :
      (n : Nat) →
      (x y : Scalar) →
      VonMangoldtAt space arithmetic n x →
      VonMangoldtAt space arithmetic n y →
      x ≡ y

vonMangoldtSampleTerm :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  VonMangoldtFunction space arithmetic →
  WeilTestSpace.Test space →
  Nat →
  WeilTestSpace.Scalar space
vonMangoldtSampleTerm space arithmetic mangoldt f n =
  AllPrimeArithmetic._*S_ arithmetic
    (VonMangoldtFunction.lambda mangoldt n)
    (AllPrimeArithmetic.sampleAtNat arithmetic f n)

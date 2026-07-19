module DASHI.Analysis.ChebyshevPrimeCounting where

-- Exact finite Chebyshev counting functions.
--
-- θ(n) sums log p over primes p ≤ n.
-- ψ(n) sums Λ(m) over 1 ≤ m ≤ n.
--
-- The scalar carrier is inherited from the Weil / explicit-formula layer, so
-- these functions can be connected to the same logarithmic prime weights
-- without identifying Nat-valued valuation proxies with log p.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.PrimeCountingFunction
open import DASHI.Analysis.RiemannVonMangoldtSpecification

record PrimeLogWeightKernel
  (space : WeilTestSpace)
  (primes : PrimePredicate) : Set₁ where
  open WeilTestSpace space
  field
    logWeightAtNat : Nat → Scalar

chebyshevThetaLE :
  (space : WeilTestSpace) →
  (primes : PrimePredicate) →
  PrimeLogWeightKernel space primes →
  Nat →
  WeilTestSpace.Scalar space
chebyshevThetaLE space primes kernel zero =
  WeilTestSpace.zeroS space
chebyshevThetaLE space primes kernel (suc zero) =
  WeilTestSpace.zeroS space
chebyshevThetaLE space primes kernel (suc (suc n))
  with PrimePredicate.prime? primes (suc (suc n))
... | yes _ =
  WeilTestSpace._+S_ space
    (PrimeLogWeightKernel.logWeightAtNat kernel (suc (suc n)))
    (chebyshevThetaLE space primes kernel (suc n))
... | no _ =
  chebyshevThetaLE space primes kernel (suc n)

chebyshevPsiLE :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  VonMangoldtFunction space arithmetic →
  Nat →
  WeilTestSpace.Scalar space
chebyshevPsiLE space arithmetic mangoldt zero =
  WeilTestSpace.zeroS space
chebyshevPsiLE space arithmetic mangoldt (suc n) =
  WeilTestSpace._+S_ space
    (VonMangoldtFunction.lambda mangoldt (suc n))
    (chebyshevPsiLE space arithmetic mangoldt n)

chebyshevPsiStep :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (n : Nat) →
  chebyshevPsiLE space arithmetic mangoldt (suc n)
  ≡
  WeilTestSpace._+S_ space
    (VonMangoldtFunction.lambda mangoldt (suc n))
    (chebyshevPsiLE space arithmetic mangoldt n)
chebyshevPsiStep space arithmetic mangoldt n = refl

------------------------------------------------------------------------
-- Ownership of the prime-only and all-prime carriers
------------------------------------------------------------------------

record ChebyshevPrimeOwnership
  (space : WeilTestSpace)
  (primes : PrimePredicate)
  (thetaKernel : PrimeLogWeightKernel space primes)
  (arithmetic : AllPrimeArithmetic space) : Set₁ where
  field
    primeToCarrier :
      {n : Nat} →
      PrimePredicate.Prime primes n →
      Σ (AllPrimeArithmetic.Prime arithmetic)
        (λ p → AllPrimeArithmetic.toNat arithmetic p ≡ n)

    carrierIsPrime :
      (p : AllPrimeArithmetic.Prime arithmetic) →
      PrimePredicate.Prime primes
        (AllPrimeArithmetic.toNat arithmetic p)

    logWeightAgreement :
      (p : AllPrimeArithmetic.Prime arithmetic) →
      PrimeLogWeightKernel.logWeightAtNat thetaKernel
        (AllPrimeArithmetic.toNat arithmetic p)
      ≡
      AllPrimeArithmetic.logPrimeWeight arithmetic p

------------------------------------------------------------------------
-- Finite root-sum form ψ(x) = Σₖ θ(x^(1/k))
------------------------------------------------------------------------

record IntegerRootFloor : Set₁ where
  field
    rootFloor : Nat → Nat → Nat

    RootFloorCorrect : Nat → Nat → Set
    rootFloorCorrect :
      (x positiveExponent : Nat) →
      RootFloorCorrect x positiveExponent

thetaRootSum :
  (space : WeilTestSpace) →
  (primes : PrimePredicate) →
  (thetaKernel : PrimeLogWeightKernel space primes) →
  IntegerRootFloor →
  Nat →
  Nat →
  WeilTestSpace.Scalar space
thetaRootSum space primes thetaKernel roots zero x =
  WeilTestSpace.zeroS space
thetaRootSum space primes thetaKernel roots (suc exponentCutoff) x =
  WeilTestSpace._+S_ space
    (chebyshevThetaLE space primes thetaKernel
      (IntegerRootFloor.rootFloor roots x (suc exponentCutoff)))
    (thetaRootSum space primes thetaKernel roots exponentCutoff x)

record ChebyshevPrimePowerIdentity
  (space : WeilTestSpace)
  (primes : PrimePredicate)
  (thetaKernel : PrimeLogWeightKernel space primes)
  (arithmetic : AllPrimeArithmetic space)
  (mangoldt : VonMangoldtFunction space arithmetic)
  (roots : IntegerRootFloor) : Set₁ where
  field
    exponentCutoff : Nat → Nat

    cutoffCoversAllPrimePowers : Nat → Set
    cutoffCoverage :
      (x : Nat) →
      cutoffCoversAllPrimePowers x

    psiAsThetaRootSum :
      (x : Nat) →
      chebyshevPsiLE space arithmetic mangoldt x
      ≡
      thetaRootSum space primes thetaKernel roots
        (exponentCutoff x) x

record ChebyshevFiniteBoundary : Set where
  field
    thetaIsFinitePrimeLogSum : ⊤
    psiIsFiniteMangoldtSum : ⊤
    rootSumNeedsCoverageProof : ⊤
    noPartialSummationIntegralConstructedHere : ⊤
    noPrimeNumberTheoremPromotion : ⊤

chebyshevFiniteBoundary : ChebyshevFiniteBoundary
chebyshevFiniteBoundary = record
  { thetaIsFinitePrimeLogSum = tt
  ; psiIsFiniteMangoldtSum = tt
  ; rootSumNeedsCoverageProof = tt
  ; noPartialSummationIntegralConstructedHere = tt
  ; noPrimeNumberTheoremPromotion = tt
  }

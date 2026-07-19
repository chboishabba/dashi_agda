module DASHI.Analysis.PrimeCountingEstimateContracts where

-- Exact inverse ownership for the nth prime, explicit π / p_n estimate
-- contracts, and consequences that consume the Riemann hypothesis.
--
-- Numerical constants and thresholds are represented in the analytic real
-- carrier.  No estimate is asserted without a proof field.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_; _<_)
open import Data.Product using (Σ; _×_)
open import DASHI.Analysis.PrimeCountingFunction
open import DASHI.Analysis.PrimeCountingAnalyticBridge
open import DASHI.Analysis.RiemannAnalyticSubstrate

------------------------------------------------------------------------
-- Exact nth-prime inverse
------------------------------------------------------------------------

record NthPrimeFunction
  (primes : PrimePredicate) : Set₁ where
  field
    nthPrime : Nat → Nat

    nthPrimeIsPrime :
      (index : Nat) →
      PrimePredicate.Prime primes (nthPrime index)

    countAtNthPrime :
      (index : Nat) →
      primeCountLE primes (nthPrime index) ≡ suc index

    leastWithCount :
      (index candidate : Nat) →
      primeCountLE primes candidate ≡ suc index →
      nthPrime index ≤ candidate

------------------------------------------------------------------------
-- Explicit finite bounds for π(x)
------------------------------------------------------------------------

record ExplicitPrimeCountBounds
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    lowerApproximation : Nat → Real
    upperApproximation : Nat → Real

    lowerThreshold upperThreshold : Nat

    lowerBound :
      (x : Nat) →
      lowerThreshold ≤ x →
      lowerApproximation x ≤R piReal (natToReal x)

    upperBound :
      (x : Nat) →
      upperThreshold ≤ x →
      piReal (natToReal x) ≤R upperApproximation x

    LowerFormulaOwned : Set
    UpperFormulaOwned : Set
    lowerFormulaOwned : LowerFormulaOwned
    upperFormulaOwned : UpperFormulaOwned

------------------------------------------------------------------------
-- nth-prime asymptotic and explicit inequalities
------------------------------------------------------------------------

record NthPrimeEstimateBounds
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (nth : NthPrimeFunction primes) : Set₁ where
  open PrimeCountingRealOperations operations
  field
    lowerNthPrimeApproximation : Nat → Real
    upperNthPrimeApproximation : Nat → Real

    lowerThreshold upperThreshold : Nat

    lowerNthPrimeBound :
      (index : Nat) →
      lowerThreshold ≤ index →
      lowerNthPrimeApproximation index
      ≤R natToReal (NthPrimeFunction.nthPrime nth index)

    upperNthPrimeBound :
      (index : Nat) →
      upperThreshold ≤ index →
      natToReal (NthPrimeFunction.nthPrime nth index)
      ≤R upperNthPrimeApproximation index

    AsymptoticExpansionCorrect : Set
    asymptoticExpansionCorrect : AsymptoticExpansionCorrect

------------------------------------------------------------------------
-- RH-conditioned prime-counting regularity and nearby-prime consequence
------------------------------------------------------------------------

record RHPrimeIntervalConsequence
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate) : Set₁ where
  open PrimeCountingRealOperations operations
  field
    rh : RiemannHypothesisFor analytic
    fourOverPi : Real

    nearbyPrime :
      (x : Nat) →
      2 ≤ x →
      Σ Nat
        (λ p →
          PrimePredicate.Prime primes p
          ×
          (((natToReal x
             -R
             ((fourOverPi *R sqrtR (natToReal x))
              *R logR (natToReal x)))
            ≤R natToReal p)
           × p ≤ x))

------------------------------------------------------------------------
-- Normalized fluctuation around Riemann R
------------------------------------------------------------------------

record PrimeCountingFluctuationScale
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    riemannR : Real → Real
    normalizedFluctuation : Real → Real

    fluctuationDefinition :
      (x : Real) →
      normalizedFluctuation x
      ≡
      (((pi0Real x -R riemannR x) *R logR x)
       /R sqrtR x)

record PrimeCountingEstimateBoundary : Set where
  field
    nthPrimeNeedsLeastnessProof : ⊤
    explicitBoundsNeedThresholdProofs : ⊤
    asymptoticExpansionIsNotDefinitional : ⊤
    nearbyPrimeTheoremConsumesRH : ⊤
    normalizedFluctuationIsDiagnosticOnly : ⊤

primeCountingEstimateBoundary : PrimeCountingEstimateBoundary
primeCountingEstimateBoundary = record
  { nthPrimeNeedsLeastnessProof = tt
  ; explicitBoundsNeedThresholdProofs = tt
  ; asymptoticExpansionIsNotDefinitional = tt
  ; nearbyPrimeTheoremConsumesRH = tt
  ; normalizedFluctuationIsDiagnosticOnly = tt
  }

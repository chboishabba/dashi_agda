module DASHI.Analysis.PrimeCountingAnalyticBridge where

-- Analytic promotion surface for prime counting.
--
-- The exact Nat counter is connected to real-valued π and π₀ here.  The prime
-- number theorem, logarithmic integral comparison, Riemann R explicit formula,
-- Chebyshev explicit formula, and RH error estimate remain proof-bearing
-- analytic obligations owned by the same completed-zeta substrate.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_)
open import DASHI.Analysis.PrimeCountingFunction
open import DASHI.Analysis.RiemannAnalyticSubstrate

record PrimeCountingRealOperations
  (analytic : AnalyticSubstrate) : Set₁ where
  Real =
    ComplexAnalyticCarrier.Real
      (AnalyticSubstrate.carrier analytic)
  field
    zeroR oneR : Real
    _+R_ _-R_ _*R_ _/R_ : Real → Real → Real
    absR sqrtR logR expR liR : Real → Real
    natToReal : Nat → Real
    halfR : Real → Real
    _≤R_ : Real → Real → Set

record PrimeCountingRealisation
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate) : Set₁ where
  open PrimeCountingRealOperations operations
  field
    piReal : Real → Real
    pi0Real : Real → Real

    piAtNat :
      (n : Nat) →
      piReal (natToReal n)
      ≡ natToReal (primeCountLE primes n)

    pi0AtNat :
      (n : Nat) →
      pi0Real (natToReal n)
      ≡ halfR
          (natToReal (primeCountSymmetricTwice primes n))

record PrimeNumberTheorem
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    TendsToOne : (Nat → Real) → Set

    xOverLogX : Nat → Real
    piOverXOverLogX : Nat → Real
    piOverLi : Nat → Real

    xOverLogXDefinition :
      (x : Nat) →
      xOverLogX x
      ≡
      (natToReal x /R logR (natToReal x))

    piRatioDefinition :
      (x : Nat) →
      piOverXOverLogX x
      ≡
      (piReal (natToReal x) /R xOverLogX x)

    liRatioDefinition :
      (x : Nat) →
      piOverLi x
      ≡
      (piReal (natToReal x) /R liR (natToReal x))

    piAsymptoticXOverLogX :
      TendsToOne piOverXOverLogX

    piAsymptoticLi :
      TendsToOne piOverLi

    asymptoticFormsEquivalent : Set
    asymptoticEquivalence : asymptoticFormsEquivalent

------------------------------------------------------------------------
-- Riemann R / explicit prime-counting formula
------------------------------------------------------------------------

record RiemannPrimeCountingExplicitFormula
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    greaterThanOne : Real → Set

    riemannR : Real → Real
    nontrivialZeroContribution : Real → Real
    trivialZeroContribution : Real → Real

    MobiusSeriesConverges : Real → Set
    ZeroSeriesConvergesInHeightOrder : Real → Set
    ExponentialIntegralBranchConvention : Real → Set
    UsesOwnedCompletedZetaZeros : Set

    mobiusSeriesConverges :
      (x : Real) →
      greaterThanOne x →
      MobiusSeriesConverges x

    zeroSeriesConvergesInHeightOrder :
      (x : Real) →
      greaterThanOne x →
      ZeroSeriesConvergesInHeightOrder x

    exponentialIntegralBranchConvention :
      (x : Real) →
      greaterThanOne x →
      ExponentialIntegralBranchConvention x

    usesOwnedCompletedZetaZeros :
      UsesOwnedCompletedZetaZeros

    pi0ExplicitFormula :
      (x : Real) →
      greaterThanOne x →
      pi0Real x
      ≡
      ((riemannR x -R nontrivialZeroContribution x)
       -R trivialZeroContribution x)

------------------------------------------------------------------------
-- Chebyshev ψ₀ explicit formula
------------------------------------------------------------------------

record ChebyshevPsiExplicitFormula
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic) : Set₁ where
  open PrimeCountingRealOperations operations
  field
    greaterThanOne : Real → Set
    psi0Real : Real → Real
    zeroPowerContribution : Real → Real
    logTwoPi : Real
    trivialZeroLogCorrection : Real → Real

    ZeroPowerSeriesConvergesInHeightOrder : Real → Set
    UsesOwnedCompletedZetaZeros : Set

    zeroPowerSeriesConvergesInHeightOrder :
      (x : Real) →
      greaterThanOne x →
      ZeroPowerSeriesConvergesInHeightOrder x

    usesOwnedCompletedZetaZeros :
      UsesOwnedCompletedZetaZeros

    psi0ExplicitFormula :
      (x : Real) →
      greaterThanOne x →
      psi0Real x
      ≡
      (((x -R zeroPowerContribution x) -R logTwoPi)
       -R trivialZeroLogCorrection x)

------------------------------------------------------------------------
-- RH-strength prime-counting error bound
------------------------------------------------------------------------

record RHPrimeCountingErrorBound
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    rh : RiemannHypothesisFor analytic
    oneOverEightPi : Real

    schoenfeldBound :
      (x : Nat) →
      2657 ≤ x →
      absR
        (piReal (natToReal x) -R liR (natToReal x))
      ≤R
      ((oneOverEightPi *R sqrtR (natToReal x))
       *R logR (natToReal x))

record PrimeCountingAnalyticBoundary : Set where
  field
    finitePiDoesNotSupplyPNT : ⊤
    pntNeedsAsymptoticLimit : ⊤
    riemannRNeedsMobiusAndBranchControl : ⊤
    zeroSumNeedsHeightOrdering : ⊤
    rhErrorBoundConsumesRH : ⊤
    noAnalyticWitnessConstructedHere : ⊤

primeCountingAnalyticBoundary : PrimeCountingAnalyticBoundary
primeCountingAnalyticBoundary = record
  { finitePiDoesNotSupplyPNT = tt
  ; pntNeedsAsymptoticLimit = tt
  ; riemannRNeedsMobiusAndBranchControl = tt
  ; zeroSumNeedsHeightOrdering = tt
  ; rhErrorBoundConsumesRH = tt
  ; noAnalyticWitnessConstructedHere = tt
  }

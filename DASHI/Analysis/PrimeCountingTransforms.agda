module DASHI.Analysis.PrimeCountingTransforms where

-- Transform identities connecting exact counting functions to analytic number
-- theory: partial summation between π and θ, Perron/Mellin ownership of Π₀,
-- and the Möbius/Gram representations of Riemann's R-function.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (_≤_)
open import DASHI.Analysis.PrimeCountingFunction
open import DASHI.Analysis.ChebyshevPrimeCounting
open import DASHI.Analysis.PrimeCountingAnalyticBridge
open import DASHI.Analysis.RiemannAnalyticSubstrate
open import DASHI.Analysis.WeilTestSpace

------------------------------------------------------------------------
-- Abel / partial summation: π ↔ θ
------------------------------------------------------------------------

record PrimeThetaPartialSummation
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic)
  (primes : PrimePredicate)
  (realisation : PrimeCountingRealisation analytic operations primes)
  (space : WeilTestSpace)
  (thetaKernel : PrimeLogWeightKernel space primes) : Set₁ where
  open PrimeCountingRealOperations operations
  open PrimeCountingRealisation realisation
  field
    scalarToReal : WeilTestSpace.Scalar space → Real
    thetaReal : Real → Real

    integralPiOverT : Real → Real
    integralThetaOverTLogSquared : Real → Real

    thetaAtNat :
      (n : Nat) →
      thetaReal (natToReal n)
      ≡
      scalarToReal
        (chebyshevThetaLE space primes thetaKernel n)

    thetaFromPi :
      (n : Nat) →
      2 ≤ n →
      thetaReal (natToReal n)
      ≡
      ((piReal (natToReal n) *R logR (natToReal n))
       -R integralPiOverT (natToReal n))

    piFromTheta :
      (n : Nat) →
      2 ≤ n →
      piReal (natToReal n)
      ≡
      ((thetaReal (natToReal n) /R logR (natToReal n))
       +R integralThetaOverTLogSquared (natToReal n))

------------------------------------------------------------------------
-- log ζ(s) = s ∫ Π₀(x) x^(-s-1) dx
------------------------------------------------------------------------

record PrimePowerPerronMellinBridge
  (analytic : AnalyticSubstrate) : Set₁ where
  carrier = AnalyticSubstrate.carrier analytic
  halfPlane = AnalyticSubstrate.halfPlane analytic
  completed = AnalyticSubstrate.completed analytic
  open ComplexAnalyticCarrier carrier
  field
    logZeta : Function
    primePowerMellinIntegral : Complex → Complex

    LogZetaUsesOwnedZeta : Set
    PrimePowerCountLocallyIntegrable : Set
    MellinIntegralConverges : Complex → Set
    InterchangePrimePowerSumIntegral : Complex → Set

    logZetaUsesOwnedZeta : LogZetaUsesOwnedZeta
    primePowerCountLocallyIntegrable :
      PrimePowerCountLocallyIntegrable

    mellinIntegralConverges :
      (s : Complex) →
      ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
      MellinIntegralConverges s

    interchangePrimePowerSumIntegral :
      (s : Complex) →
      ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
      InterchangePrimePowerSumIntegral s

    perronMellinIdentity :
      (s : Complex) →
      ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane s →
      apply logZeta s ≡ primePowerMellinIntegral s

------------------------------------------------------------------------
-- Riemann R: Möbius-li series and Gram series
------------------------------------------------------------------------

record RiemannRSeriesBridge
  (analytic : AnalyticSubstrate)
  (operations : PrimeCountingRealOperations analytic) : Set₁ where
  open PrimeCountingRealOperations operations
  field
    greaterThanZero : Real → Set

    riemannR : Real → Real
    mobiusLiSeries : Real → Real
    gramSeries : Real → Real

    MobiusLiSeriesConverges : Real → Set
    GramSeriesConverges : Real → Set
    UsesOwnedPositiveIntegerZetaValues : Set
    LogarithmBranchCorrect : Real → Set

    mobiusLiSeriesConverges :
      (x : Real) →
      greaterThanZero x →
      MobiusLiSeriesConverges x

    gramSeriesConverges :
      (x : Real) →
      greaterThanZero x →
      GramSeriesConverges x

    usesOwnedPositiveIntegerZetaValues :
      UsesOwnedPositiveIntegerZetaValues

    logarithmBranchCorrect :
      (x : Real) →
      greaterThanZero x →
      LogarithmBranchCorrect x

    riemannRAsMobiusLi :
      (x : Real) →
      greaterThanZero x →
      riemannR x ≡ mobiusLiSeries x

    riemannRAsGramSeries :
      (x : Real) →
      greaterThanZero x →
      riemannR x ≡ gramSeries x

record PrimeCountingTransformBoundary : Set where
  field
    partialSummationNeedsIntegralTheory : ⊤
    perronNeedsHalfPlaneAndInterchange : ⊤
    logZetaNeedsBranchOwnership : ⊤
    riemannRNeedsMobiusConvergence : ⊤
    gramSeriesNeedsOwnedZetaValues : ⊤
    noTransformIdentityDischargedByFiniteCounts : ⊤

primeCountingTransformBoundary : PrimeCountingTransformBoundary
primeCountingTransformBoundary = record
  { partialSummationNeedsIntegralTheory = tt
  ; perronNeedsHalfPlaneAndInterchange = tt
  ; logZetaNeedsBranchOwnership = tt
  ; riemannRNeedsMobiusConvergence = tt
  ; gramSeriesNeedsOwnedZetaValues = tt
  ; noTransformIdentityDischargedByFiniteCounts = tt
  }

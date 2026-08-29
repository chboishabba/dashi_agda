module DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact where

------------------------------------------------------------------------
-- ROUND251 / STANDARD SPACETIME W1 PASSAGE + FINITE-DIMENSIONAL W3 FIRST HIT
--
-- R249 closes the pointwise scalar consequence of periodic Holder/Sobolev.
-- R243, however, consumes the time-integrated inequality.  This file records
-- the independently owned physical integration passage once, on the SAME
-- observables.
--
-- It also packages the standard finite-dimensional continuity + intermediate
-- value / least-hit theorem directly as the R242 FirstHitLaw required by W3.
-- No alternative trajectory or user-chosen notion of first hit is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242
import DASHI.Physics.Closure.NSTriadKNStandardPeriodicSobolevW1Round249Exact as R249

record StandardSpacetimeW1Authority
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    (pointwise : R249.StandardPeriodicW1Authority
      Time mixedMass criticalSize dissipationDensity)
    : Set₁ where
  field
    CriticalBarrierTo : Nat → Time → ℚ → Set

    integratedDissipation : Nat → Time → ℚ

    integratedDissipationMeaning :
      (N : Nat) (terminal : Time) →
      integratedDissipation N terminal
      ≡ integrateTo (dissipationDensity N) terminal

    pointwiseSobolevPassesToSpacetimeUnderBarrier :
      (N : Nat) (terminal : Time) (K : ℚ) →
      CriticalBarrierTo N terminal K →
      integrateTo (mixedMass N) terminal
      ≤ (R249.oneEmbeddingConstant pointwise
          * R249.halfEmbeddingConstant pointwise)
          * K * integratedDissipation N terminal

    scaledBarrierNonnegative :
      (N : Nat) (terminal : Time) (K : ℚ) →
      CriticalBarrierTo N terminal K →
      0ℚ ≤ (R249.oneEmbeddingConstant pointwise
          * R249.halfEmbeddingConstant pointwise) * K

open StandardSpacetimeW1Authority public

record FiniteDimensionalFirstHitAuthority
    (Time : Set)
    (Before : Time → Time → Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ) : Set₁ where
  field
    -- Source-level continuity theorem for the finite-dimensional Galerkin
    -- critical-size observable.  Its internal topology belongs to the analytic
    -- model; downstream code needs only the induced first-hit theorem.
    CriticalSizeContinuous : Nat → Set
    criticalSizeContinuous : (N : Nat) → CriticalSizeContinuous N

    firstHitLaw : R242.FirstHitLaw Time Before criticalSize threshold

open FiniteDimensionalFirstHitAuthority public

firstHitAuthorityBuildsCriticalSequence :
  ∀ {Time Before criticalSize threshold}
    (A : FiniteDimensionalFirstHitAuthority Time Before criticalSize threshold)
    (cutoffs : Nat → Nat)
    (crosses : (n : Nat) →
      R242.ThresholdCrossing Time criticalSize threshold (cutoffs n)) →
  R242.CriticalFirstHitSequence Time criticalSize threshold
firstHitAuthorityBuildsCriticalSequence A =
  R242.firstHitLawBuildsCriticalSequence (firstHitLaw A)

round251PointwiseW1ToSpacetimeAuthorityUnified : Bool
round251PointwiseW1ToSpacetimeAuthorityUnified = true

round251FiniteDimensionalContinuityAndFirstHitAuthorityUnified : Bool
round251FiniteDimensionalContinuityAndFirstHitAuthorityUnified = true

round251W3CompilerClosed : Bool
round251W3CompilerClosed = true

round251ContinuumIntegrationAndIVTKernelDerivedHere : Bool
round251ContinuumIntegrationAndIVTKernelDerivedHere = false

round251PackageAClosed : Bool
round251PackageAClosed = false

round251ClayPromotion : Bool
round251ClayPromotion = false

round251W3CompilerClosedIsTrue : round251W3CompilerClosed ≡ true
round251W3CompilerClosedIsTrue = refl

round251ContinuumIntegrationAndIVTKernelDerivedHereIsFalse :
  round251ContinuumIntegrationAndIVTKernelDerivedHere ≡ false
round251ContinuumIntegrationAndIVTKernelDerivedHereIsFalse = refl

round251ClayPromotionIsFalse : round251ClayPromotion ≡ false
round251ClayPromotionIsFalse = refl

module DASHI.Physics.Closure.NSTriadKNFirstHitBidiAnalyticClosureRound252Exact where

------------------------------------------------------------------------
-- ROUND252 / BIDI ANALYTIC CLOSURE COMPILER FOR W1 + W2 + W3
--
-- This is the capstone for the Round241--251 extraction tranche.
--
-- Source-bound standard analytic authorities:
--   R249: periodic Holder/Sobolev pointwise W1;
--   R251: pointwise-to-spacetime passage and finite-dimensional first hit;
--   R250: canonical G2 numeric dissipation projected onto the same physical
--         dissipation observable.
--
-- Downstream consumers:
--   R243 builds the same-trajectory W1/W2 and W3 objects;
--   R241 then pays the mixed-helicity defect under a critical barrier;
--   R242 then extracts the exact-threshold bounded critical sequence.
--
-- No additional mathematical leaf is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242
import DASHI.Physics.Closure.NSTriadKNFirstHitBidiPhysicalWeldRound243Exact as R243
import DASHI.Physics.Closure.NSTriadKNStandardPeriodicSobolevW1Round249Exact as R249
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251

F : C3.RealField _
F = Rational.rationalRealField

module AnalyticClosure
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Bidi = R243.PhysicalBidi Time initialTime integrateTo DerivativeOf
  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record CompletedW1W2
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
      (pointwise : R249.StandardPeriodicW1Authority
        Time mixedMass criticalSize dissipationDensity)
      (spacetime : R251.StandardSpacetimeW1Authority
        Time integrateTo mixedMass criticalSize dissipationDensity pointwise)
      : Set₁ where
    field
      dissipationBound : ℚ
      integratedDissipationBound :
        (N : Nat) (terminal : Time) →
        R251.integratedDissipation spacetime N terminal ≤ dissipationBound

  open CompletedW1W2 public

  completedW1W2BuildsRound243 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    {mixedMass criticalSize dissipationDensity : Nat → Time → ℚ} →
    (pointwise : R249.StandardPeriodicW1Authority
      Time mixedMass criticalSize dissipationDensity) →
    (spacetime : R251.StandardSpacetimeW1Authority
      Time integrateTo mixedMass criticalSize dissipationDensity pointwise) →
    (A : CompletedW1W2 T mixedMass criticalSize dissipationDensity pointwise spacetime) →
    Bidi.SameTrajectoryW1W2 T
  completedW1W2BuildsRound243 T pointwise spacetime A = record
    { Bidi.criticalSize = criticalSize
    ; Bidi.defectIntegral = λ N terminal → integrateTo (mixedMass N) terminal
    ; Bidi.dissipationIntegral = R251.integratedDissipation spacetime
    ; Bidi.interpolationConstant =
        R249.oneEmbeddingConstant pointwise * R249.halfEmbeddingConstant pointwise
    ; Bidi.dissipationBound = dissipationBound A
    ; Bidi.CriticalBarrierTo = R251.CriticalBarrierTo spacetime
    ; Bidi.mixedHelicityCriticalReduction =
        R251.pointwiseSobolevPassesToSpacetimeUnderBarrier spacetime
    ; Bidi.integratedDissipationBound = integratedDissipationBound A
    ; Bidi.scaledBarrierNonnegative = R251.scaledBarrierNonnegative spacetime
    }

  completedW3BuildsRound243 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    {mixedMass criticalSize dissipationDensity : Nat → Time → ℚ} →
    (pointwise : R249.StandardPeriodicW1Authority
      Time mixedMass criticalSize dissipationDensity) →
    (spacetime : R251.StandardSpacetimeW1Authority
      Time integrateTo mixedMass criticalSize dissipationDensity pointwise) →
    (A : CompletedW1W2 T mixedMass criticalSize dissipationDensity pointwise spacetime) →
    {Before : Time → Time → Set} →
    {threshold : ℚ} →
    (W3 : R251.FiniteDimensionalFirstHitAuthority
      Time Before criticalSize threshold) →
    Bidi.SameTrajectoryW3
      T (completedW1W2BuildsRound243 T pointwise spacetime A)
      Before threshold
  completedW3BuildsRound243 T pointwise spacetime A W3 = record
    { Bidi.firstHitLaw = R251.firstHitLaw W3 }

  completedAuthoritiesBuildCriticalSequence :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    {mixedMass criticalSize dissipationDensity : Nat → Time → ℚ} →
    (pointwise : R249.StandardPeriodicW1Authority
      Time mixedMass criticalSize dissipationDensity) →
    (spacetime : R251.StandardSpacetimeW1Authority
      Time integrateTo mixedMass criticalSize dissipationDensity pointwise) →
    (A : CompletedW1W2 T mixedMass criticalSize dissipationDensity pointwise spacetime) →
    {Before : Time → Time → Set} →
    {threshold : ℚ} →
    (W3 : R251.FiniteDimensionalFirstHitAuthority
      Time Before criticalSize threshold) →
    (cutoffs : Nat → Nat) →
    (crosses : (n : Nat) →
      R242.ThresholdCrossing Time criticalSize threshold (cutoffs n)) →
    R242.CriticalFirstHitSequence Time criticalSize threshold
  completedAuthoritiesBuildCriticalSequence
      T pointwise spacetime A W3 cutoffs crosses =
    Bidi.sameTrajectoryW3BuildsCriticalSequence
      T
      (completedW1W2BuildsRound243 T pointwise spacetime A)
      (completedW3BuildsRound243 T pointwise spacetime A W3)
      cutoffs crosses

round252W1W2W3BidiCompilerClosed : Bool
round252W1W2W3BidiCompilerClosed = true

round252NoAdditionalExtractionSocketAfterStandardAuthorities : Bool
round252NoAdditionalExtractionSocketAfterStandardAuthorities = true

round252StandardAnalyticAuthoritiesKernelDerivedInThisRepo : Bool
round252StandardAnalyticAuthoritiesKernelDerivedInThisRepo = false

round252PackageAClosed : Bool
round252PackageAClosed = false

round252ClayPromotion : Bool
round252ClayPromotion = false

round252W1W2W3BidiCompilerClosedIsTrue :
  round252W1W2W3BidiCompilerClosed ≡ true
round252W1W2W3BidiCompilerClosedIsTrue = refl

round252NoAdditionalExtractionSocketAfterStandardAuthoritiesIsTrue :
  round252NoAdditionalExtractionSocketAfterStandardAuthorities ≡ true
round252NoAdditionalExtractionSocketAfterStandardAuthoritiesIsTrue = refl

round252StandardAnalyticAuthoritiesKernelDerivedInThisRepoIsFalse :
  round252StandardAnalyticAuthoritiesKernelDerivedInThisRepo ≡ false
round252StandardAnalyticAuthoritiesKernelDerivedInThisRepoIsFalse = refl

round252ClayPromotionIsFalse : round252ClayPromotion ≡ false
round252ClayPromotionIsFalse = refl

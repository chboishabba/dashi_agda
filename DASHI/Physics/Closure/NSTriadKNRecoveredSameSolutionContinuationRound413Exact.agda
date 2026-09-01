module DASHI.Physics.Closure.NSTriadKNRecoveredSameSolutionContinuationRound413Exact where

------------------------------------------------------------------------
-- ROUND413 / BIDI RECOVERY: THE FINAL CONTINUATION COMPILER ALREADY EXISTS
--
-- R411 deliberately froze a generic Package-A -> critical-barrier target so we
-- would not reverse R241.  Repository archaeology gives a stronger existing
-- consumer: R369 -> R103 -> R90 already continues the EXACT limiting solution.
-- R371 further decomposes the only physical transport before that compiler into
--
--   A. physical signed-critical/barrier production;
--   B. the standard critical Sobolev--Simon upgrade.
--
-- Therefore a fresh post-barrier continuation theorem is not a research leaf.
-- Once the physical Round104 inputs are inhabited on the same R240 trajectory,
-- the existing theorem-bearing chain returns ExtendsPastMaximalTime.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSTriadKNUniformCriticalBarrierPassageToLimitRound103Exact as R103
import DASHI.Physics.Closure.NSTriadKNPackageAToSameSolutionSerrinRound369Exact as R369
import DASHI.Physics.Closure.NSTriadKNPackageAToRound104CriticalFrontierRound371Exact as R371
import DASHI.Physics.Closure.NSTriadKNCriticalSimonUpgradeFollowsBarrierRound148Exact as R148

F : C3.RealField _
F = Rational.rationalRealField

module Recovered
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Same = R369.PackageAToSameSolutionSerrin
    Time initialTime integrateTo DerivativeOf

  recoveredCriticalLimitData :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (continuation : Critical.PeriodicSerrinContinuationTarget) →
    (I : Same.PackageASameSolutionSerrinInputs T continuation) →
    R103.UniformCriticalGalerkinLimitData continuation
  recoveredCriticalLimitData T continuation I =
    Same.sameSolutionCriticalLimitDataFromR293 T continuation I

  recoveredSameSolutionContinuation :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (continuation : Critical.PeriodicSerrinContinuationTarget) →
    (I : Same.PackageASameSolutionSerrinInputs T continuation) →
    Critical.ExtendsPastMaximalTime continuation
      (R103.limitingSolution (recoveredCriticalLimitData T continuation I))
  recoveredSameSolutionContinuation T continuation I =
    Same.r293PackageAContinuesExactLimitingSolution T continuation I

round413FreshContinuationTheoremNeeded : Bool
round413FreshContinuationTheoremNeeded =
  R371.round371FreshContinuationTheoremNeededAfterRound104Inputs

round413SameSolutionLimitCompilerAlreadyClosed : Bool
round413SameSolutionLimitCompilerAlreadyClosed =
  R371.round371SameSolutionLimitCompilerAlreadyClosed

round413PostBarrierNonlinearDiscoveryNeeded : Bool
round413PostBarrierNonlinearDiscoveryNeeded = false

round413StandardSimonUpgradeAlreadyReducedToThreeFacts : Bool
round413StandardSimonUpgradeAlreadyReducedToThreeFacts =
  R148.round148PackageBReducedToStandardPublishedAnalysis

round413FreshContinuationTheoremNeededIsFalse :
  round413FreshContinuationTheoremNeeded ≡ false
round413FreshContinuationTheoremNeededIsFalse = refl

round413SameSolutionLimitCompilerAlreadyClosedIsTrue :
  round413SameSolutionLimitCompilerAlreadyClosed ≡ true
round413SameSolutionLimitCompilerAlreadyClosedIsTrue = refl

round413PostBarrierNonlinearDiscoveryNeededIsFalse :
  round413PostBarrierNonlinearDiscoveryNeeded ≡ false
round413PostBarrierNonlinearDiscoveryNeededIsFalse = refl

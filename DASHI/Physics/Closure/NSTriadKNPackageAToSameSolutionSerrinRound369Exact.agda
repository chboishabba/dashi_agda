module DASHI.Physics.Closure.NSTriadKNPackageAToSameSolutionSerrinRound369Exact where

------------------------------------------------------------------------
-- ROUND369 / BIDI: PACKAGE A -> EXISTING SAME-SOLUTION SERRIN CONSUMER
--
-- Round365 routed Package A through the older scalar nested-limit/restart
-- interface.  Repository archaeology shows a stronger existing downstream
-- consumer: Round103 owns the one-shot same-solution Galerkin-limit compiler
-- into the Round90 critical barrier and periodic Serrin continuation.
--
-- Therefore the shortest continuation-facing seam is not a detached scalar
-- threshold.  It is an explicit physical transport from the SAME R240 Package-A
-- budget into Round103 `UniformCriticalGalerkinLimitData`, whose limiting
-- element is already welded to the exact solution consumed by Serrin.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSTriadKNUniformCriticalBarrierPassageToLimitRound103Exact as R103

F : C3.RealField _
F = Rational.rationalRealField

module PackageAToSameSolutionSerrin
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record PackageASameSolutionSerrinInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (continuation : Critical.PeriodicSerrinContinuationTarget) : Set₁ where
    field
      r354Inputs : Weld.R293PhysicalPackageAInputs T

      -- Same-object physical transport only.  Round103 already owns the
      -- compactness, lower-semicontinuity, exact-limit-element weld, critical
      -- budget -> L4_t L6_x step, and Serrin continuation compiler.
      packageAToUniformCriticalLimitData :
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget T →
        R103.UniformCriticalGalerkinLimitData continuation

  open PackageASameSolutionSerrinInputs public

  sameSolutionCriticalLimitDataFromR293 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (continuation : Critical.PeriodicSerrinContinuationTarget) →
    PackageASameSolutionSerrinInputs T continuation →
    R103.UniformCriticalGalerkinLimitData continuation
  sameSolutionCriticalLimitDataFromR293 T continuation I =
    packageAToUniformCriticalLimitData I
      (Weld.r293BuildsPhysicalPackageA T (r354Inputs I))

  r293PackageAContinuesExactLimitingSolution :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (continuation : Critical.PeriodicSerrinContinuationTarget) →
    (I : PackageASameSolutionSerrinInputs T continuation) →
    Critical.ExtendsPastMaximalTime continuation
      (R103.limitingSolution
        (sameSolutionCriticalLimitDataFromR293 T continuation I))
  r293PackageAContinuesExactLimitingSolution T continuation I =
    R103.uniformCriticalPassageContinuesSameLimitingSolution
      (sameSolutionCriticalLimitDataFromR293 T continuation I)

round369Round103SameSolutionCompilerReused : Bool
round369Round103SameSolutionCompilerReused = true

round369Round90CriticalBarrierCompilerReusedTransitively : Bool
round369Round90CriticalBarrierCompilerReusedTransitively = true

round369DetachedScalarThresholdRequiredForSerrinRoute : Bool
round369DetachedScalarThresholdRequiredForSerrinRoute = false

round369PackageAToUniformCriticalLimitTransportStillPhysical : Bool
round369PackageAToUniformCriticalLimitTransportStillPhysical = true

round369SameSolutionContinuationCompilerClosedConditionally : Bool
round369SameSolutionContinuationCompilerClosedConditionally = true

round369SameSolutionContinuationCompilerClosedConditionallyIsTrue :
  round369SameSolutionContinuationCompilerClosedConditionally ≡ true
round369SameSolutionContinuationCompilerClosedConditionallyIsTrue = refl

round369DetachedScalarThresholdRequiredForSerrinRouteIsFalse :
  round369DetachedScalarThresholdRequiredForSerrinRoute ≡ false
round369DetachedScalarThresholdRequiredForSerrinRouteIsFalse = refl

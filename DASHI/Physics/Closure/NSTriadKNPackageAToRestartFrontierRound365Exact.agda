module DASHI.Physics.Closure.NSTriadKNPackageAToRestartFrontierRound365Exact where

------------------------------------------------------------------------
-- ROUND365 / BIDI: DECOMPOSE THE R363 GLOBALIZATION AUTHORITY
--
-- The old Round22 lane already proves two downstream logical compilers:
--
--   finite two-cutoff estimate + analytic convergence receipts
--     -> physical critical norm below continuation threshold;
--
--   physical critical bound + restart/maximality receipts
--     -> contradiction of a finite maximal time.
--
-- Hence R363's Package-A -> GlobalPhysicalSolutionPrimitiveInputs authority is
-- still too coarse.  This round factors out the already-owned limit/restart
-- mathematics and leaves only the analytic transports that connect the new
-- R240 Package-A budget to those old interfaces.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNR293ToPhysicalPackageARound354Exact as R354
import DASHI.Physics.Closure.NSTriadKNLuoNestedGalerkinShellLimitExact as Limit
import DASHI.Physics.Closure.NSTriadKNLuoCriticalRestartContradictionExact as Restart

F : C3.RealField _
F = Rational.rationalRealField

module PackageAToRestartFrontier
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Weld = R354.PhysicalPackageAWeld Time initialTime integrateTo DerivativeOf

  record PackageACriticalLimitInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      r354Inputs : Weld.R293PhysicalPackageAInputs T

      -- Analytic same-object transport from the R240 budget to the old nested
      -- shell/Galerkin critical-limit interface.  The old selection arithmetic
      -- itself is not reproved here.
      packageABudgetToNestedLimitData :
        Dyn.PhysicalNSMixedHelicitySpacetimeBudget T →
        Limit.NestedGalerkinShellLimitData

  open PackageACriticalLimitInputs public

  physicalCriticalBelowContinuationThreshold :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : PackageACriticalLimitInputs T) →
    Limit.physicalCritical (packageABudgetToNestedLimitData I
      (Weld.r293BuildsPhysicalPackageA T (r354Inputs I)))
    ≤ Limit.continuationThreshold (packageABudgetToNestedLimitData I
      (Weld.r293BuildsPhysicalPackageA T (r354Inputs I)))
  physicalCriticalBelowContinuationThreshold T I =
    Limit.nestedGalerkinShellLimitBelowThreshold
      (packageABudgetToNestedLimitData I
        (Weld.r293BuildsPhysicalPackageA T (r354Inputs I)))

  record RestartFromPackageAInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      criticalLimitInputs : PackageACriticalLimitInputs T

      -- Given the actual threshold theorem returned by the reused Round22
      -- nested-limit compiler, supply only the physical restart/maximality data
      -- that instantiate the old contradiction theorem.
      thresholdToFiniteMaximalContradictionData :
        let L = packageABudgetToNestedLimitData criticalLimitInputs
                  (Weld.r293BuildsPhysicalPackageA T
                    (r354Inputs criticalLimitInputs))
        in
        Limit.physicalCritical L ≤ Limit.continuationThreshold L →
        Restart.FiniteMaximalRestartContradictionData

  open RestartFromPackageAInputs public

  finiteMaximalTimeContradictedFromPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    RestartFromPackageAInputs T →
    ⊥
  finiteMaximalTimeContradictedFromPackageA T I =
    Restart.criticalRestartContradictsFiniteMaximality
      (thresholdToFiniteMaximalContradictionData I
        (physicalCriticalBelowContinuationThreshold T
          (criticalLimitInputs I)))

round365OldNestedLimitCompilerReused : Bool
round365OldNestedLimitCompilerReused = true

round365OldCriticalRestartContradictionReused : Bool
round365OldCriticalRestartContradictionReused = true

round365PackageAToGlobalPrimitiveStillAtomic : Bool
round365PackageAToGlobalPrimitiveStillAtomic = false

round365PackageAToCriticalLimitTransportStillAnalytic : Bool
round365PackageAToCriticalLimitTransportStillAnalytic = true

round365RestartInstantiationStillPhysical : Bool
round365RestartInstantiationStillPhysical = true

round365FiniteMaximalTimeContradictionCompilerClosedConditionally : Bool
round365FiniteMaximalTimeContradictionCompilerClosedConditionally = true

round365FiniteMaximalTimeContradictionCompilerClosedConditionallyIsTrue :
  round365FiniteMaximalTimeContradictionCompilerClosedConditionally ≡ true
round365FiniteMaximalTimeContradictionCompilerClosedConditionallyIsTrue = refl

round365PackageAToGlobalPrimitiveStillAtomicIsFalse :
  round365PackageAToGlobalPrimitiveStillAtomic ≡ false
round365PackageAToGlobalPrimitiveStillAtomicIsFalse = refl

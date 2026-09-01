module DASHI.Physics.Closure.NSTriadKNPackageAToGlobalPrimitiveRound367Exact where

------------------------------------------------------------------------
-- ROUND367 / BIDI: R354 PACKAGE A -> R365 RESTART -> R366 GLOBAL PRIMITIVE
--
-- R365 closes the finite-maximal-time contradiction once the Package-A to
-- critical-limit transport and physical restart instantiation are supplied.
-- R366 then turns any finite-maximal-time contradiction into the exact old
-- `GlobalPhysicalSolutionPrimitiveInputs` using the existing maximal-time
-- dichotomy and standard post-infinite-time continuation infrastructure.
--
-- Thus R363's monolithic Package-A globalization authority is no longer needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact as Legacy
import DASHI.Physics.Closure.NSTriadKNLuoGlobalPhysicalSolutionReductionExact as Global
import DASHI.Physics.Closure.NSTriadKNPackageAToRestartFrontierRound365Exact as R365
import DASHI.Physics.Closure.NSTriadKNStandardGlobalContinuationCompilerRound366Exact as R366

F : C3.RealField _
F = Rational.rationalRealField

module PackageAToGlobalPrimitive
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (legacy : Legacy.PeriodicNavierStokesSubmissionCarrier) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module RestartLane =
    R365.PackageAToRestartFrontier Time initialTime integrateTo DerivativeOf

  record DatumGlobalPrimitiveInputs
      (initial : Legacy.SmoothPeriodicDatum legacy) : Set₁ where
    field
      trajectory : Dyn.PhysicalNSGalerkinTrajectory

      standardContinuation :
        R366.StandardGlobalContinuationInfrastructure legacy initial

      -- The finite maximal-time witness determines the concrete physical
      -- restart instance used to contradict that finite case.
      restartInputsForFiniteCase :
        R366.FiniteMaximalTime standardContinuation →
        RestartLane.RestartFromPackageAInputs trajectory

  open DatumGlobalPrimitiveInputs public

  finiteCaseImpossible :
    ∀ {initial}
      (I : DatumGlobalPrimitiveInputs initial) →
    R366.FiniteMaximalTime (standardContinuation I) → ⊥
  finiteCaseImpossible I finite =
    RestartLane.finiteMaximalTimeContradictedFromPackageA
      (trajectory I)
      (restartInputsForFiniteCase I finite)

  packageARestartBuildsGlobalPrimitive :
    ∀ {initial} →
    DatumGlobalPrimitiveInputs initial →
    Global.GlobalPhysicalSolutionPrimitiveInputs legacy initial
  packageARestartBuildsGlobalPrimitive I =
    R366.primitivePhysicalSolutionFromFiniteContradiction
      (standardContinuation I)
      (finiteCaseImpossible I)

  record UniformDatumGlobalPrimitiveInputs : Set₁ where
    field
      forEveryAdmissibleLegacyDatum :
        (initial : Legacy.SmoothPeriodicDatum legacy) →
        Legacy.DivergenceFreeDatum legacy initial →
        Legacy.MeanZeroDatum legacy initial →
        DatumGlobalPrimitiveInputs initial

  open UniformDatumGlobalPrimitiveInputs public

  packageARestartBuildsOldUniformGlobalPhysicalInputs :
    UniformDatumGlobalPrimitiveInputs →
    Global.UniformGlobalPhysicalSolutionInputs legacy
  packageARestartBuildsOldUniformGlobalPhysicalInputs I = record
    { Global.primitiveInputsForDatum =
        λ initial divergenceFree meanZero →
          packageARestartBuildsGlobalPrimitive
            (forEveryAdmissibleLegacyDatum I initial divergenceFree meanZero)
    }

round367R363MonolithicGlobalizationAuthorityNeeded : Bool
round367R363MonolithicGlobalizationAuthorityNeeded = false

round367R365FiniteMaximalContradictionReused : Bool
round367R365FiniteMaximalContradictionReused = true

round367R366GlobalPrimitiveCompilerReused : Bool
round367R366GlobalPrimitiveCompilerReused = true

round367UniformGlobalPhysicalInputsClosedConditionally : Bool
round367UniformGlobalPhysicalInputsClosedConditionally = true

round367UniformGlobalPhysicalInputsClosedConditionallyIsTrue :
  round367UniformGlobalPhysicalInputsClosedConditionally ≡ true
round367UniformGlobalPhysicalInputsClosedConditionallyIsTrue = refl

round367R363MonolithicGlobalizationAuthorityNeededIsFalse :
  round367R363MonolithicGlobalizationAuthorityNeeded ≡ false
round367R363MonolithicGlobalizationAuthorityNeededIsFalse = refl

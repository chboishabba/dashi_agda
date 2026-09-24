{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCriticalSliceRound639Exact where

------------------------------------------------------------------------
-- ROUND637 / CANONICAL PHYSICAL R414 CRITICAL SLICE
--
-- The literal finite critical observables and their exact energy identity are
-- already owned by:
--
--   LiteralFiniteCriticalObservableFoldExact
--   LiteralCriticalEnergyCalculusExact
--
-- This owner removes the remaining alias freedom in R414.  Given the standard
-- scalar-calculus authorities required by the existing energy-identity
-- compiler, and the genuinely analytic phase-sensitive production estimate,
-- it constructs the R414 slice with
--
--   initialCritical             = literal X_N(0)
--   terminalCritical            = literal X_N(T)
--   criticalDissipation         = literal D_N(T)
--   integratedSignedProduction  = literal P_N(T)
--   viscousCoefficient          = 2 * physicalViscosity
--
-- definitionally.
--
-- The absorbed coefficient is still analytic data.  Strictly positive retained
-- viscosity is kept as its own typed receipt:
--
--   0 < 2*nu - absorbedCoefficient.
--
-- No nonlinear estimate is proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNRetainedViscosityPositivityNoGoRound514Exact as R514

F : C3.RealField _
F = Rational.rationalRealField

module PhysicalSlice
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo DerivativeOf
  module Calc = Energy.LiteralCriticalEnergyCalculus
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record PhysicalCriticalSliceData
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      absorbedCoefficient : ℚ

      phaseSensitiveProductionEstimate :
        Obs.integratedCriticalProduction
            (Live.literalPhysicalTrajectory D) cutoff terminal
        ≤ absorbedCoefficient
            * Obs.integratedCriticalDissipation
                (Live.literalPhysicalTrajectory D) cutoff terminal
          + Unified.literalRemainderIntegral
              (Live.literalPhysicalTrajectory D) R cutoff terminal

  open PhysicalCriticalSliceData public

  canonicalPhysicalCriticalSlice :
    ∀ {D C R cutoff terminal} →
    (P : PhysicalCriticalSliceData D C R cutoff terminal) →
    Unified.CriticalSliceOnLiteralR406
      (Live.literalPhysicalTrajectory D) R terminal cutoff
  canonicalPhysicalCriticalSlice {D} {C} {R} {cutoff} {terminal} P =
    record
      { Unified.initialCritical =
          Obs.criticalEnergyAt
            (Live.literalPhysicalTrajectory D) cutoff initialTime
      ; Unified.terminalCritical =
          Obs.criticalEnergyAt
            (Live.literalPhysicalTrajectory D) cutoff terminal
      ; Unified.criticalDissipation =
          Obs.integratedCriticalDissipation
            (Live.literalPhysicalTrajectory D) cutoff terminal
      ; Unified.integratedSignedProduction =
          Obs.integratedCriticalProduction
            (Live.literalPhysicalTrajectory D) cutoff terminal
      ; Unified.viscousCoefficient =
          Fold.two * Live.physicalViscosity (Live.support D)
      ; Unified.absorbedCoefficient = absorbedCoefficient P
      ; Unified.criticalEnergyInequality =
          subst
            (λ rhs →
              Obs.criticalEnergyAt
                  (Live.literalPhysicalTrajectory D) cutoff terminal
                + (Fold.two * Live.physicalViscosity (Live.support D))
                    * Obs.integratedCriticalDissipation
                        (Live.literalPhysicalTrajectory D) cutoff terminal
              ≤ rhs)
            (Calc.integratedLiteralCriticalEnergyIdentity
              D C cutoff terminal)
            ℚP.≤-refl
      ; Unified.signedProductionEstimateByLiteralRemainder =
          phaseSensitiveProductionEstimate P
      }

  record PositiveRetainedViscosityReceipt
      {D : Live.LiteralRHSTrajectoryData}
      {C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D)}
      {R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D)}
      {cutoff : Nat}
      {terminal : Time}
      (P : PhysicalCriticalSliceData D C R cutoff terminal) : Set where
    field
      retainedViscosityPositive :
        0ℚ <
          (Fold.two * Live.physicalViscosity (Live.support D))
            - absorbedCoefficient P

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round639LiteralCriticalCoordinatesInstalledOnR414 : Bool
round639LiteralCriticalCoordinatesInstalledOnR414 = true

round639ViscousCoefficientFixedToTwoPhysicalViscosity : Bool
round639ViscousCoefficientFixedToTwoPhysicalViscosity = true

round639CriticalEnergyInequalityCompiledFromExactIdentity : Bool
round639CriticalEnergyInequalityCompiledFromExactIdentity = true

round639CallerCanAliasCriticalCoordinatesArbitrarily : Bool
round639CallerCanAliasCriticalCoordinatesArbitrarily = false

round639PhaseSensitiveProductionEstimateStillProofBearing : Bool
round639PhaseSensitiveProductionEstimateStillProofBearing = true

round639PositiveRetainedViscosityTyped : Bool
round639PositiveRetainedViscosityTyped = true

round639PositiveRetainedViscosityProved : Bool
round639PositiveRetainedViscosityProved = false

round639RequiresConcreteScalarFTC : Bool
round639RequiresConcreteScalarFTC = true

round639IntroducesNewNSEstimate : Bool
round639IntroducesNewNSEstimate = false

round639ClayPromotion : Bool
round639ClayPromotion = false

round639LiteralCriticalCoordinatesInstalledOnR414IsTrue :
  round639LiteralCriticalCoordinatesInstalledOnR414 ≡ true
round639LiteralCriticalCoordinatesInstalledOnR414IsTrue = refl

round639ViscousCoefficientFixedToTwoPhysicalViscosityIsTrue :
  round639ViscousCoefficientFixedToTwoPhysicalViscosity ≡ true
round639ViscousCoefficientFixedToTwoPhysicalViscosityIsTrue = refl

round639CriticalEnergyInequalityCompiledFromExactIdentityIsTrue :
  round639CriticalEnergyInequalityCompiledFromExactIdentity ≡ true
round639CriticalEnergyInequalityCompiledFromExactIdentityIsTrue = refl

round639CallerCanAliasCriticalCoordinatesArbitrarilyIsFalse :
  round639CallerCanAliasCriticalCoordinatesArbitrarily ≡ false
round639CallerCanAliasCriticalCoordinatesArbitrarilyIsFalse = refl

round639PhaseSensitiveProductionEstimateStillProofBearingIsTrue :
  round639PhaseSensitiveProductionEstimateStillProofBearing ≡ true
round639PhaseSensitiveProductionEstimateStillProofBearingIsTrue = refl

round639PositiveRetainedViscosityTypedIsTrue :
  round639PositiveRetainedViscosityTyped ≡ true
round639PositiveRetainedViscosityTypedIsTrue = refl

round639PositiveRetainedViscosityProvedIsFalse :
  round639PositiveRetainedViscosityProved ≡ false
round639PositiveRetainedViscosityProvedIsFalse = refl

round639RequiresConcreteScalarFTCIsTrue :
  round639RequiresConcreteScalarFTC ≡ true
round639RequiresConcreteScalarFTCIsTrue = refl

round639IntroducesNewNSEstimateIsFalse :
  round639IntroducesNewNSEstimate ≡ false
round639IntroducesNewNSEstimateIsFalse = refl

round639ClayPromotionIsFalse :
  round639ClayPromotion ≡ false
round639ClayPromotionIsFalse = refl

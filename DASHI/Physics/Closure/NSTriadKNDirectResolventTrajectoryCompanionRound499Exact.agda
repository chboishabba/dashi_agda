module DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact where

------------------------------------------------------------------------
-- ROUND499 / LIVE-TRAJECTORY SPECIALIZATION OF THE DIRECT RESOLVENT COMPANION
--
-- R498 is generic in one physical finite system.  R406 already constructs the
-- exact physical system, canonical time-independent output list, and local pair
-- positivity at every cutoff/time slice of the live Galerkin trajectory.
--
-- This file specializes R498 to that exact R406 slice.  Therefore the literal
-- instantaneous R406 weighted remainder is four times a canonical direct
-- nonseparable resolvent companion scalar at every (N,t).
--
-- No temporal integration law and no estimate is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498

F : C3.RealField _
F = Rational.rationalRealField

module DirectTrajectory
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf

  instantaneousDirectCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  instantaneousDirectCompanion T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = R498.DirectGlobal
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.globalDirectCompanion
      cutoff At.outputs At.canonicalOutputPositivity

  literalInstantaneousRemainderIsFourDirectCompanion :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Flux.At.weightedRemainder T R cutoff time
    ≡ R299.four * instantaneousDirectCompanion T R cutoff time
  literalInstantaneousRemainderIsFourDirectCompanion
      T R cutoff time =
    let
      module At = Flux.At T R cutoff time
      module G = R498.DirectGlobal
        At.PS
        (Dyn.Base.S (Dyn.forgetDynamics T))
        (Dyn.Base.L (Dyn.forgetDynamics T))
        (Dyn.Base.H (Dyn.forgetDynamics T))
        At.P
    in
    G.globalRemainderIsFourDirectCompanion
      cutoff At.outputs At.canonicalOutputPositivity

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round499LiteralR406SliceSpecializationClosed : Bool
round499LiteralR406SliceSpecializationClosed = true

round499InstantaneousRemainderIsFourDirectCompanionClosed : Bool
round499InstantaneousRemainderIsFourDirectCompanionClosed = true

round499IntegrationAuthorityUsed : Bool
round499IntegrationAuthorityUsed = false

round499IntegratedCompanionWeldClosed : Bool
round499IntegratedCompanionWeldClosed = false

round499SignedSpacetimeEstimateClosed : Bool
round499SignedSpacetimeEstimateClosed = false

round499ClayPromotion : Bool
round499ClayPromotion = false

round499InstantaneousRemainderIsFourDirectCompanionClosedIsTrue :
  round499InstantaneousRemainderIsFourDirectCompanionClosed ≡ true
round499InstantaneousRemainderIsFourDirectCompanionClosedIsTrue = refl

round499IntegrationAuthorityUsedIsFalse :
  round499IntegrationAuthorityUsed ≡ false
round499IntegrationAuthorityUsedIsFalse = refl

round499ClayPromotionIsFalse : round499ClayPromotion ≡ false
round499ClayPromotionIsFalse = refl

module DASHI.Physics.Closure.NSTriadKNR571SecondMomentToR568BridgeExact where

------------------------------------------------------------------------
-- PERIODIC B / SECOND-MOMENT -> LIVE R568 BRIDGE SURFACE
--
-- R571 now produces a finite physical weighted second moment on the same
-- periodic trajectory.  R568 consumes the time-integrated global forcing /
-- commutator full square.  The remaining representation theorem is therefore
-- not another estimate: it is the same-object inequality identifying the live
-- forcing square with the already-paid physical M2 density.
--
-- This owner separates exactly those two jobs:
--
--   1. fixed-time/cutoff same-object domination by the R571 physical M2;
--   2. time integration + cutoff-uniform dissipation bound.
--
-- Once supplied, the existing R568 record is constructed directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567

F : C3.RealField _
F = Rational.rationalRealField

module Bridge
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Comm = R568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integration

  record R571PhysicalM2Realization
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      physicalM2Density : Nat → Time → ℚ
      dissipationBound : Time → ℚ

      forcingFullBelowPhysicalM2 :
        (cutoff : Nat) (time : Time) →
        Comm.globalForcingFull T R cutoff time
        ≤ physicalM2Density cutoff time

      integratedPhysicalM2Bound :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 * integrateTo (physicalM2Density cutoff) terminal
        ≤ dissipationBound terminal

      integrationMonotone :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (Comm.globalForcingFull T R cutoff) terminal
        ≤ integrateTo (physicalM2Density cutoff) terminal

  open R571PhysicalM2Realization public

  physicalM2BuildsR568 :
    ∀ {T R} →
    R571PhysicalM2Realization T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  physicalM2BuildsR568 P =
    record
      { Comm.cutoffIndependentCommutatorBound568 =
          dissipationBound P
      ; Comm.liveCommutatorOnlyBudget568 = λ cutoff terminal →
          let
            first =
              integrationMonotone P cutoff terminal
            scaled :
              R567.four567 *
                Comm.integratedGlobalForcingFull _ _ cutoff terminal
              ≤
              R567.four567 *
                integrateTo (physicalM2Density P cutoff) terminal
            scaled =
              let
                open import Data.Rational.Base using (0ℚ; nonNegative)
                import Data.Rational.Properties as ℚP
                fourNN : 0ℚ ≤ R567.four567
                fourNN = ℚP.<⇒≤ (ℚP.positive⁻¹ R567.four567)
                instance fourNNI = nonNegative fourNN
              in
              ℚP.*-monoˡ-≤-nonNeg R567.four567 first
          in
          let import Data.Rational.Properties as ℚP
          in ℚP.≤-trans scaled
            (integratedPhysicalM2Bound P cutoff terminal)
      }

r571ToR568RepresentationCutIsolated : Bool
r571ToR568RepresentationCutIsolated = true

r571PhysicalM2ToR568CompilerClosed : Bool
r571PhysicalM2ToR568CompilerClosed = true

forcingSquareBelowLiteralR571M2ProvedHere : Bool
forcingSquareBelowLiteralR571M2ProvedHere = false

cutoffUniformIntegratedM2DissipationProvedHere : Bool
cutoffUniformIntegratedM2DissipationProvedHere = false

clayPromotion : Bool
clayPromotion = false

r571PhysicalM2ToR568CompilerClosedIsTrue :
  r571PhysicalM2ToR568CompilerClosed ≡ true
r571PhysicalM2ToR568CompilerClosedIsTrue = refl

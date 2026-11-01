module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionAnalyticAssemblyExact where

------------------------------------------------------------------------
-- S2b2d1b2 / B1-B4 -> LIVE PHYSICAL CRITICAL-REGION PAYMENT
--
-- This is the literal fixed-output B5 constructor.  It consumes the four new
-- leaf owners and constructs PhysicalCriticalRegionPayment without restating
-- any analytic inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowLiteralInfinityShellPaymentExact as FF
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepFarLowDeepHHFractionalShellPaymentExact as FH
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepHHFractionalShellPaymentExact as HH
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as Core

F : C3.RealField _
F = Rational.rationalRealField

module Assemble
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output
  module FFP = FF.LiteralDeepFarLowPayment physicalSystem S output
  module FHP = FH.DeepCrossPayment physicalSystem S output
  module HHP = HH.DeepHHPayment physicalSystem S output
  module CP = Core.CriticalTouching physicalSystem S output

  record FixedOutputAnalyticLeaves : Set₁ where
    constructor fixed-output-analytic-leaves
    field
      farLow : FFP.PhysicalDeepFarLowLiteralShellData
      farLowHighHigh : FHP.PhysicalDeepFarLowDeepHHFractionalShellData
      highHigh : HHP.PhysicalDeepHHFractionalShellData
      critical : CP.SignedBlockOperatorCertificate

      viscosityNN : 0ℚ ≤ Field30.viscosity physicalSystem

  open FixedOutputAnalyticLeaves public

  physicalCriticalRegionPaymentAt :
    FixedOutputAnalyticLeaves →
    P.PhysicalCriticalRegionPayment
  physicalCriticalRegionPaymentAt leaves =
    let
      ff = farLow leaves
      fh = farLowHighHigh leaves
      hh = highHigh leaves
      cc = critical leaves
    in record
      { P.deepFarLowFarLowBudget =
          FFP.coefficient ff * FFP.localED ff
      ; P.deepFarLowDeepHighHighBudget =
          FHP.coefficient fh * FHP.localED fh
      ; P.deepHighHighHighHighBudget =
          HHP.coefficient hh * HHP.localED hh
      ; P.coreCompanionMass = CP.coreCompanionMass cc
      ; P.coreEDBudget = CP.coreEDBudget cc
      ; P.theta = CP.theta cc
      ; P.viscosityNN = viscosityNN leaves
      ; P.thetaNN = CP.thetaNN cc
      ; P.thetaStrictlyBelowOne = CP.thetaStrictlyBelowOne cc
      ; P.deepFarLowFarLowPaid =
          FFP.deepFarLowFarLowLiteralShellPayment ff
      ; P.deepFarLowDeepHighHighPaid =
          FHP.deepFarLowDeepHHFractionalShellPayment fh
      ; P.deepHighHighHighHighPaid =
          HHP.deepHHFractionalShellPayment hh
      ; P.criticalTouchingRelativeCovariance =
          CP.criticalTouchingRelativeCovariance cc
      }

fixedOutputB1B4ToPhysicalPaymentCompilerClosed : Bool
fixedOutputB1B4ToPhysicalPaymentCompilerClosed = true

fixedOutputB1B4ToPhysicalPaymentIntroducesPostulate : Bool
fixedOutputB1B4ToPhysicalPaymentIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

fixedOutputB1B4ToPhysicalPaymentCompilerClosedIsTrue :
  fixedOutputB1B4ToPhysicalPaymentCompilerClosed ≡ true
fixedOutputB1B4ToPhysicalPaymentCompilerClosedIsTrue = refl

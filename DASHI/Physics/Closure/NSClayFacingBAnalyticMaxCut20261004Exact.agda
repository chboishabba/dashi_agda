module DASHI.Physics.Closure.NSClayFacingBAnalyticMaxCut20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / DIRECT ANALYTIC MAX-CUT
--
-- The representation/provenance programme has already reduced the physical
-- critical-region problem to the literal six-block R236 carrier.  The legacy
-- B1/B2/B3/B4 producer records are useful proof routes, but they are not the
-- theorem frontier consumed downstream.
--
-- This owner removes that final packaging layer.  A positive-B producer need
-- supply exactly four literal inequalities:
--
--   B1  DFL-DFL <= C1 * ED1
--   B2  DFL-DHH <= C2 * ED2
--   B3  DHH-DHH <= C3 * ED3
--   B4  criticalTouching <= theta * Mcore + EDcore, 0 <= theta < 1
--
-- These compile directly to the existing PhysicalCriticalRegionPayment and
-- hence to the live fixed-output coherent-covariance bound.  No shell receipt,
-- alias scalar, or same-object equality is reintroduced here.
--
-- B7 remains a producer disjunction: the preferred quartic Gram+endpoint route
-- or the direct signed quintic route.  B-continuation remains an inhabitation
-- problem for the already-machine-checked continuum/BKM compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _+_; _≤_; _<_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Exact as Positive
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact as B7
import DASHI.Physics.Closure.NSPeriodicCutoffUniformContinuumBKMCompletion as Continuum

F : C3.RealField _
F = Rational.rationalRealField

module DirectAnalytic
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  record DirectPhysicalCriticalRegionAnalyticLeaves : Set where
    constructor direct-physical-critical-region-analytic-leaves
    field
      b1Budget b2Budget b3Budget : ℚ
      coreCompanionMass coreEDBudget theta : ℚ

      viscosityNN : 0ℚ ≤ Field30.viscosity physicalSystem
      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ

      b1LiteralPayment :
        P.deepFarLowFarLowSigned ≤ b1Budget

      b2LiteralPayment :
        P.deepFarLowDeepHighHighSigned ≤ b2Budget

      b3LiteralPayment :
        P.deepHighHighHighHighSigned ≤ b3Budget

      b4LiteralStrictPayment :
        P.criticalTouchingSigned
        ≤ theta * coreCompanionMass + coreEDBudget

  open DirectPhysicalCriticalRegionAnalyticLeaves public

  directLeavesBuildPhysicalCriticalRegionPayment :
    DirectPhysicalCriticalRegionAnalyticLeaves →
    P.PhysicalCriticalRegionPayment
  directLeavesBuildPhysicalCriticalRegionPayment D = record
    { P.deepFarLowFarLowBudget = b1Budget D
    ; P.deepFarLowDeepHighHighBudget = b2Budget D
    ; P.deepHighHighHighHighBudget = b3Budget D
    ; P.coreCompanionMass = coreCompanionMass D
    ; P.coreEDBudget = coreEDBudget D
    ; P.theta = theta D
    ; P.viscosityNN = viscosityNN D
    ; P.thetaNN = thetaNN D
    ; P.thetaStrictlyBelowOne = thetaStrictlyBelowOne D
    ; P.deepFarLowFarLowPaid = b1LiteralPayment D
    ; P.deepFarLowDeepHighHighPaid = b2LiteralPayment D
    ; P.deepHighHighHighHighPaid = b3LiteralPayment D
    ; P.criticalTouchingRelativeCovariance = b4LiteralStrictPayment D
    }

  directLeavesCloseFixedOutput :
    (D : DirectPhysicalCriticalRegionAnalyticLeaves) →
    P.Live.coherentCovarianceNumerator output
    ≤ P.fixedOutputBudget (directLeavesBuildPhysicalCriticalRegionPayment D)
  directLeavesCloseFixedOutput D =
    P.physicalCriticalRegionPaymentClosesFixedOutput
      (directLeavesBuildPhysicalCriticalRegionPayment D)

------------------------------------------------------------------------
-- Exact roadmap state.
------------------------------------------------------------------------

bRepresentationProgrammeClosed : Bool
bRepresentationProgrammeClosed = true

b1AnalyticClosed : Bool
b1AnalyticClosed = Positive.b1LiteralShellPhysicalPaymentClosed

b2AnalyticClosed : Bool
b2AnalyticClosed = Positive.b2SignedShellEstimateClosed

b3AnalyticClosed : Bool
b3AnalyticClosed = Positive.b3SignedIntraShellL2Closed

b4AnalyticClosed : Bool
b4AnalyticClosed = Positive.b4StrictMarginClosed

b4HighestInformationAnalyticWall : Bool
b4HighestInformationAnalyticWall = true

b7QuarticEndpointPreferred : Bool
b7QuarticEndpointPreferred = true

b7DirectQuinticFallback : Bool
b7DirectQuinticFallback = true

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false b = b

b7OneProducerClosed : Bool
b7OneProducerClosed =
  boolOr B7.b7QuarticGramEndpointRouteClosed B7.b7DirectSignedQuinticRouteClosed

bContinuationInputsClosed : Bool
bContinuationInputsClosed = Continuum.periodicContinuumBKMCompletionInputsInhabited

bAnalyticRepresentationWrapperStillRequired : Bool
bAnalyticRepresentationWrapperStillRequired = false

r823ShouldReopen : Bool
r823ShouldReopen = false

oldB7UniversalCovarianceEqualityShouldReopen : Bool
oldB7UniversalCovarianceEqualityShouldReopen = false

clayPromotion : Bool
clayPromotion = false

bRepresentationProgrammeClosedIsTrue : bRepresentationProgrammeClosed ≡ true
bRepresentationProgrammeClosedIsTrue = refl

b4HighestInformationAnalyticWallIsTrue :
  b4HighestInformationAnalyticWall ≡ true
b4HighestInformationAnalyticWallIsTrue = refl

b7QuarticEndpointPreferredIsTrue : b7QuarticEndpointPreferred ≡ true
b7QuarticEndpointPreferredIsTrue = refl

bAnalyticRepresentationWrapperStillRequiredIsFalse :
  bAnalyticRepresentationWrapperStillRequired ≡ false
bAnalyticRepresentationWrapperStillRequiredIsFalse = refl

r823ShouldReopenIsFalse : r823ShouldReopen ≡ false
r823ShouldReopenIsFalse = refl

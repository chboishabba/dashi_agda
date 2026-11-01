module DASHI.Physics.Closure.NSClayFacingBAnalyticMaxCut20261004Exact where

------------------------------------------------------------------------
-- CLAY-FACING B / DIRECT ANALYTIC MAX-CUT
--
-- The representation/provenance programme has already reduced the physical
-- critical-region problem to the literal six-block R236 carrier.  The legacy
-- B1/B2/B3/B4 producer records are useful proof routes, but they are not the
-- theorem frontier consumed downstream.
--
-- This owner removes that final packaging layer.  At one output a positive-B
-- producer supplies exactly four literal inequalities:
--
--   B1  DFL-DFL <= B1
--   B2  DFL-DHH <= B2
--   B3  DHH-DHH <= B3
--   B4  criticalTouching <= theta * Mcore + EDcore, 0 <= theta < 1.
--
-- For the cutoff-uniform family there is one additional honest analytic
-- allocation:
--
--   B1 + B2 + B3 + EDcore <= C * ED_local(output),
--
-- with common theta and C.  These data compile directly to the existing
-- PhysicalCriticalRegionPayment and UniformPhysicalCriticalRegionFamily.
-- No shell receipt, alias scalar, or same-object equality is reintroduced.
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
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyProducerExact as UniformProducer
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
  module Live = LiveOwner.Live physicalSystem S

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
    Live.coherentCovarianceNumerator output
    ≤ P.fixedOutputBudget (directLeavesBuildPhysicalCriticalRegionPayment D)
  directLeavesCloseFixedOutput D =
    P.physicalCriticalRegionPaymentClosesFixedOutput
      (directLeavesBuildPhysicalCriticalRegionPayment D)

------------------------------------------------------------------------
-- Uniform family: the final analytic interface before the existing B6/R406
-- assembly.  The only additional content beyond the four pointwise payments is
-- common theta/C plus one summed local-ED allocation per output.
------------------------------------------------------------------------

module DirectUniformAnalytic
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (theta coefficient : ℚ)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) where

  module U = UniformProducer.Producer physicalSystem S theta coefficient select

  record DirectUniformAnalyticLeaves : Set₁ where
    constructor direct-uniform-analytic-leaves
    field
      b1Budget b2Budget b3Budget : Z3.FourierMode → ℚ
      coreCompanionMass coreEDBudget : Z3.FourierMode → ℚ

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ
      coefficientNN : 0ℚ ≤ coefficient
      viscosityNN : 0ℚ ≤ Field30.viscosity physicalSystem

      b1LiteralPayment :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowFarLowSigned ≤ b1Budget output

      b2LiteralPayment :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowDeepHighHighSigned ≤ b2Budget output

      b3LiteralPayment :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepHighHighHighHighSigned ≤ b3Budget output

      b4LiteralStrictPayment :
        (output : Z3.FourierMode) →
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.criticalTouchingSigned
          ≤ theta * coreCompanionMass output + coreEDBudget output

      aggregateLocalEDAllocation :
        (output : Z3.FourierMode) →
        ((b1Budget output + b2Budget output) + b3Budget output)
          + coreEDBudget output
        ≤ coefficient * U.localED output

  open DirectUniformAnalyticLeaves public

  perOutputReceipts :
    (D : DirectUniformAnalyticLeaves) →
    (output : Z3.FourierMode) → U.PerOutputAnalyticReceipts output
  perOutputReceipts D output = record
    { U.deepFarLowFarLowBudget = b1Budget D output
    ; U.deepFarLowDeepHighHighBudget = b2Budget D output
    ; U.deepHighHighHighHighBudget = b3Budget D output
    ; U.coreCompanionMass = coreCompanionMass D output
    ; U.coreEDBudget = coreEDBudget D output
    ; U.viscosityNN = viscosityNN D
    ; U.thetaNN = thetaNN D
    ; U.thetaStrictlyBelowOne = thetaStrictlyBelowOne D
    ; U.deepFarLowFarLowPaid = b1LiteralPayment D output
    ; U.deepFarLowDeepHighHighPaid = b2LiteralPayment D output
    ; U.deepHighHighHighHighPaid = b3LiteralPayment D output
    ; U.criticalTouchingRelativeCovariance = b4LiteralStrictPayment D output
    }

  directUniformLeavesBuildExistingReceipts :
    DirectUniformAnalyticLeaves → U.UniformAnalyticReceipts
  directUniformLeavesBuildExistingReceipts D = record
    { U.receiptsAt = perOutputReceipts D
    ; U.coefficientNN = coefficientNN D
    ; U.viscosityNN = viscosityNN D
    ; U.localEDBudgetPaid = aggregateLocalEDAllocation D
    }

  directUniformLeavesBuildPhysicalFamily :
    DirectUniformAnalyticLeaves → U.U.UniformPhysicalCriticalRegionFamily
  directUniformLeavesBuildPhysicalFamily D =
    U.physicalCriticalRegionUniformFamily
      (directUniformLeavesBuildExistingReceipts D)

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

bUniformLocalEDAllocationClosed : Bool
bUniformLocalEDAllocationClosed = false

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

bContinuationCompilerMachineChecked : Bool
bContinuationCompilerMachineChecked = true

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

bContinuationCompilerMachineCheckedIsTrue :
  bContinuationCompilerMachineChecked ≡ true
bContinuationCompilerMachineCheckedIsTrue = refl

bAnalyticRepresentationWrapperStillRequiredIsFalse :
  bAnalyticRepresentationWrapperStillRequired ≡ false
bAnalyticRepresentationWrapperStillRequiredIsFalse = refl

r823ShouldReopenIsFalse : r823ShouldReopen ≡ false
r823ShouldReopenIsFalse = refl

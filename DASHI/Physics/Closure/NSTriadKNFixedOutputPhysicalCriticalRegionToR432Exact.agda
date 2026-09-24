module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionToR432Exact where

------------------------------------------------------------------------
-- S2b2d1b2 / LIVE R236 PAYMENT -> R432 FIXED-OUTPUT PAYMENT RECORD
--
-- R432.FixedOutputSignedCrossPayment is only a scalar inequality package.
-- Therefore the new literal d1b2 critical-region payment can inhabit it
-- directly:
--
--   signedCross = live coherent covariance numerator,
--   fibreBudget = literal R236 fixed-output budget.
--
-- IMPORTANT FIREWALL
-- ------------------
-- This does NOT assert that the resulting list is already the exact R398/R406
-- fixed-output decomposition.  That global same-object equality remains a
-- separate producer required by R432.FixedOutputRemainderDecomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as RegionPay
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432

F : C3.RealField _
F = Rational.rationalRealField

module ToR432
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Pay = RegionPay.LiveRegionPayment physicalSystem S output

  criticalRegionPaymentToR432 :
    Pay.PhysicalCriticalRegionPayment →
    R432.FixedOutputSignedCrossPayment
  criticalRegionPaymentToR432 P = record
    { R432.signedCross = Live.coherentCovarianceNumerator output
    ; R432.fibreBudget = Pay.fixedOutputBudget P
    ; R432.signedCrossBound =
        Pay.physicalCriticalRegionPaymentClosesFixedOutput P
    }

liveCriticalRegionToR432FixedOutputCompilerClosed : Bool
liveCriticalRegionToR432FixedOutputCompilerClosed = true

liveCriticalRegionToR432GlobalR406SameObjectWeldClosedHere : Bool
liveCriticalRegionToR432GlobalR406SameObjectWeldClosedHere = false

liveCriticalRegionToR432IntroducesCrossOutputCoherence : Bool
liveCriticalRegionToR432IntroducesCrossOutputCoherence = false

clayPromotion : Bool
clayPromotion = false

liveCriticalRegionToR432FixedOutputCompilerClosedIsTrue :
  liveCriticalRegionToR432FixedOutputCompilerClosed ≡ true
liveCriticalRegionToR432FixedOutputCompilerClosedIsTrue = refl

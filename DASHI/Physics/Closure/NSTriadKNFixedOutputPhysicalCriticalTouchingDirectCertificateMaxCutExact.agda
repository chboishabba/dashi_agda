module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingDirectCertificateMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / DIRECT STRICT CRITICAL-TOUCHING CERTIFICATE
--
-- The existing B4 certificate allows a producer to choose an arbitrary scalar
-- `signedOperatorValue` and then separately prove that it is the literal live
-- critical-touching signed block.  That equality is representation plumbing,
-- not part of the strict operator estimate.
--
-- This max-cut removes the alias entirely.  A producer now supplies only:
--
--   0 <= theta < 1,
--   criticalTouchingSigned <= theta * coreCompanionMass + coreEDBudget.
--
-- From this direct certificate we compile the legacy certificate consumed by
-- the existing B4/B5 machinery.  No estimate is introduced here; the strict
-- inequality remains the genuine mathematical leaf.
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
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact as Legacy

F : C3.RealField _
F = Rational.rationalRealField

module DirectCriticalTouching
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output
  module B4 = Legacy.CriticalTouching physicalSystem S output

  record DirectStrictCriticalTouchingCertificate : Set where
    constructor direct-strict-critical-touching-certificate
    field
      theta coreCompanionMass coreEDBudget : ℚ
      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ
      directOperatorBound :
        P.criticalTouchingSigned
        ≤ theta * coreCompanionMass + coreEDBudget

  open DirectStrictCriticalTouchingCertificate public

  directCertificateBuildsLegacy :
    DirectStrictCriticalTouchingCertificate →
    B4.SignedBlockOperatorCertificate
  directCertificateBuildsLegacy D = record
    { B4.theta = theta D
    ; B4.coreCompanionMass = coreCompanionMass D
    ; B4.coreEDBudget = coreEDBudget D
    ; B4.thetaNN = thetaNN D
    ; B4.thetaStrictlyBelowOne = thetaStrictlyBelowOne D
    ; B4.signedOperatorValue = P.criticalTouchingSigned
    ; B4.signedOperatorIsLiteralCriticalTouching = refl
    ; B4.operatorBound = directOperatorBound D
    }

  directCriticalTouchingRelativeCovariance :
    (D : DirectStrictCriticalTouchingCertificate) →
    P.criticalTouchingSigned
    ≤ theta D * coreCompanionMass D + coreEDBudget D
  directCriticalTouchingRelativeCovariance D = directOperatorBound D

------------------------------------------------------------------------
-- Status / exact frontier.
------------------------------------------------------------------------

b4ArbitrarySignedOperatorAliasEliminated : Bool
b4ArbitrarySignedOperatorAliasEliminated = true

b4LegacyCompilerReusableFromDirectCertificate : Bool
b4LegacyCompilerReusableFromDirectCertificate = true

b4DirectStrictEstimateClosedHere : Bool
b4DirectStrictEstimateClosedHere = false

b4RequiresStrictThetaBelowOne : Bool
b4RequiresStrictThetaBelowOne = true

b4IntroducesEstimate : Bool
b4IntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b4ArbitrarySignedOperatorAliasEliminatedIsTrue :
  b4ArbitrarySignedOperatorAliasEliminated ≡ true
b4ArbitrarySignedOperatorAliasEliminatedIsTrue = refl

b4DirectStrictEstimateClosedHereIsFalse :
  b4DirectStrictEstimateClosedHere ≡ false
b4DirectStrictEstimateClosedHereIsFalse = refl

b4RequiresStrictThetaBelowOneIsTrue :
  b4RequiresStrictThetaBelowOne ≡ true
b4RequiresStrictThetaBelowOneIsTrue = refl

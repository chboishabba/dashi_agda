module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRelativeCovarianceExact where

------------------------------------------------------------------------
-- S2b2d1b2 / B4: LITERAL CRITICAL-TOUCHING RELATIVE COVARIANCE
--
-- Work on the modern six-block carrier:
--
--   DFL-Core + DHH-Core + Core-Core.
--
-- The analytic producer is represented as a signed block-operator certificate,
-- not as an absolute Schur majorant.  The certificate retains one common
-- theta < 1 and an ED remainder.  Its conclusion is definitionally the exact
-- field required by PhysicalCriticalRegionPayment.
--
-- This owner deliberately does NOT manufacture the strict margin.  A proof of
-- the operator bound is the remaining genuine critical-cone theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _+_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

module CriticalTouching
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module P = Pay.LiveRegionPayment physicalSystem S output

  record SignedBlockOperatorCertificate : Set where
    constructor signed-block-operator-certificate
    field
      theta coreCompanionMass coreEDBudget : ℚ

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1

      signedOperatorValue : ℚ

      signedOperatorIsLiteralCriticalTouching :
        signedOperatorValue ≡ P.criticalTouchingSigned

      operatorBound :
        signedOperatorValue
        ≤ theta * coreCompanionMass + coreEDBudget

  open SignedBlockOperatorCertificate public

  criticalTouchingRelativeCovariance :
    (certificate : SignedBlockOperatorCertificate) →
    P.criticalTouchingSigned
    ≤ theta certificate * coreCompanionMass certificate
      + coreEDBudget certificate
  criticalTouchingRelativeCovariance certificate =
    subst
      (_≤ theta certificate * coreCompanionMass certificate
        + coreEDBudget certificate)
      (sym (signedOperatorIsLiteralCriticalTouching certificate))
      (operatorBound certificate)

criticalTouchingSignedBlockOperatorCompilerClosed : Bool
criticalTouchingSignedBlockOperatorCompilerClosed = true

criticalTouchingAbsoluteSchurRequired : Bool
criticalTouchingAbsoluteSchurRequired = false

criticalTouchingStrictOperatorCertificateInhabitedHere : Bool
criticalTouchingStrictOperatorCertificateInhabitedHere = false

criticalTouchingCompilerIntroducesPostulate : Bool
criticalTouchingCompilerIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false

criticalTouchingSignedBlockOperatorCompilerClosedIsTrue :
  criticalTouchingSignedBlockOperatorCompilerClosed ≡ true
criticalTouchingSignedBlockOperatorCompilerClosedIsTrue = refl

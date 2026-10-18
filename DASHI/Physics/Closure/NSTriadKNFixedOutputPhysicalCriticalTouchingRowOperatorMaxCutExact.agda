module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingRowOperatorMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B4 / LITERAL ROW-OPERATOR STRICT-MARGIN INTERFACE
--
-- B4's exact source carrier is now the literal critical-touching row fold from
-- NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact.  A producer therefore
-- proves the strict estimate on that finite signed row operator directly:
--
--   rowSum <= theta * M_core + ED_core,    0 <= theta < 1.
--
-- The exact same-object theorem then compiles this to the existing direct B4
-- certificate and hence to PhysicalCriticalRegionPayment.  There is no scalar
-- alias and no additional representation hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _+_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingLiteralRowsMaxCutExact as Rows
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalTouchingDirectCertificateMaxCutExact as Direct

F : C3.RealField _
F = Rational.rationalRealField

module LiteralRowOperator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module R = Rows.LiveCriticalRows physicalSystem S output
  module B4 = Direct.DirectCriticalTouching physicalSystem S output

  record LiteralRowStrictCriticalTouchingCertificate : Set where
    constructor literal-row-strict-critical-touching-certificate
    field
      theta coreCompanionMass coreEDBudget : ℚ
      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1ℚ

      literalRowOperatorBound :
        R.rowSum ≤ theta * coreCompanionMass + coreEDBudget

  open LiteralRowStrictCriticalTouchingCertificate public

  rowBoundToLiveCriticalTouching :
    (D : LiteralRowStrictCriticalTouchingCertificate) →
    R.P.criticalTouchingSigned
      ≤ theta D * coreCompanionMass D + coreEDBudget D
  rowBoundToLiveCriticalTouching D =
    subst
      (λ lower →
        lower ≤ theta D * coreCompanionMass D + coreEDBudget D)
      (sym R.liveCriticalTouchingIsLiteralRows)
      (literalRowOperatorBound D)

  literalRowCertificateBuildsDirectB4 :
    LiteralRowStrictCriticalTouchingCertificate →
    B4.DirectStrictCriticalTouchingCertificate
  literalRowCertificateBuildsDirectB4 D = record
    { B4.theta = theta D
    ; B4.coreCompanionMass = coreCompanionMass D
    ; B4.coreEDBudget = coreEDBudget D
    ; B4.thetaNN = thetaNN D
    ; B4.thetaStrictlyBelowOne = thetaStrictlyBelowOne D
    ; B4.directOperatorBound = rowBoundToLiveCriticalTouching D
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

b4LiteralRowOperatorCompilerClosed : Bool
b4LiteralRowOperatorCompilerClosed = true

b4RowOperatorSameObjectLeafRemaining : Bool
b4RowOperatorSameObjectLeafRemaining = false

b4LiteralRowStrictEstimateClosedHere : Bool
b4LiteralRowStrictEstimateClosedHere = false

b4LiteralRowOperatorIntroducesNorm : Bool
b4LiteralRowOperatorIntroducesNorm = false

clayPromotion : Bool
clayPromotion = false

b4LiteralRowOperatorCompilerClosedIsTrue :
  b4LiteralRowOperatorCompilerClosed ≡ true
b4LiteralRowOperatorCompilerClosedIsTrue = refl

b4RowOperatorSameObjectLeafRemainingIsFalse :
  b4RowOperatorSameObjectLeafRemaining ≡ false
b4RowOperatorSameObjectLeafRemainingIsFalse = refl

b4LiteralRowStrictEstimateClosedHereIsFalse :
  b4LiteralRowStrictEstimateClosedHere ≡ false
b4LiteralRowStrictEstimateClosedHereIsFalse = refl

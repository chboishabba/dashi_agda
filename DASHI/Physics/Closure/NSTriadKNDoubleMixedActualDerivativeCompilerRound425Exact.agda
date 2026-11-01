module DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact where

------------------------------------------------------------------------
-- ROUND425 / ACTUAL DOUBLE-MIXED CELL DERIVATIVE FROM TWO PLUS-MINUS CELLS
--
-- R387 proves pointwise
--
--   D_tau = 2 A_tau + 2 A_swap(tau).
--
-- R388 defines the corresponding tangent by exactly the same finite linear
-- combination of the already-owned plus-minus tangents.  Therefore, for any
-- honest vector derivative semantics closed under addition and transport, the
-- actual derivative of D_tau reduces to the two actual derivatives of A_tau
-- and A_swap(tau).  This removes another purely formal layer from the R422
-- temporal seam without introducing a second projector tangent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387

F : C3.RealField _
F = Rational.rationalRealField

record VectorDerivativeAlgebra
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) : Set₁ where
  field
    addDerivative :
      ∀ {f g df dg} →
      VectorDerivativeOf f df →
      VectorDerivativeOf g dg →
      VectorDerivativeOf
        (λ time → C3.complex3Add (f time) (g time))
        (λ time → C3.complex3Add (df time) (dg time))

    transportDerivative :
      ∀ {f g df dg} →
      ((time : Time) → f time ≡ g time) →
      ((time : Time) → df time ≡ dg time) →
      VectorDerivativeOf f df →
      VectorDerivativeOf g dg

open VectorDerivativeAlgebra public

module DoubleMixedDerivative
    (Time : Set)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (A : VectorDerivativeAlgebra Time VectorDerivativeOf)
    (S : Helical.HelicalModeScalars F)
    (velocity : Time → Z3.FourierMode → C3.Complex3 F) where

  plusMinusCurve :
    Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  plusMinusCurve tau time =
    R224.mixedPlusMinus S (velocity time) tau

  doubleMixedCurve :
    Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  doubleMixedCurve tau time =
    R225.doubleMixedCell S (velocity time) tau

  doubledCurve :
    (Time → C3.Complex3 F) → Time → C3.Complex3 F
  doubledCurve f time = C3.complex3Add (f time) (f time)

  swapPairedCurve :
    Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  swapPairedCurve tau time =
    C3.complex3Add
      (doubledCurve (plusMinusCurve tau) time)
      (doubledCurve (plusMinusCurve (Symmetry.swapTriad tau)) time)

  doubleMixedIsSwapPairedPointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    (time : Time) →
    doubleMixedCurve tau time ≡ swapPairedCurve tau time
  doubleMixedIsSwapPairedPointwise tau time =
    R387.doubleMixedIsSwapPairedPlusMinus S (velocity time) tau

  doubledDerivative :
    ∀ {f df} →
    VectorDerivativeOf f df →
    VectorDerivativeOf (doubledCurve f) (doubledCurve df)
  doubledDerivative d = addDerivative A d d

  swapPairedDerivative :
    (tau : Physical.PhysicalTriadIncidence) →
    (tangent tangentSwap : Time → C3.Complex3 F) →
    VectorDerivativeOf (plusMinusCurve tau) tangent →
    VectorDerivativeOf
      (plusMinusCurve (Symmetry.swapTriad tau)) tangentSwap →
    VectorDerivativeOf
      (swapPairedCurve tau)
      (λ time →
        C3.complex3Add
          (C3.complex3Add (tangent time) (tangent time))
          (C3.complex3Add (tangentSwap time) (tangentSwap time)))
  swapPairedDerivative tau tangent tangentSwap d dSwap =
    addDerivative A (doubledDerivative d) (doubledDerivative dSwap)

  plusMinusDerivativesBuildDoubleMixedDerivative :
    (tau : Physical.PhysicalTriadIncidence) →
    (tangent tangentSwap doubleTangent : Time → C3.Complex3 F) →
    VectorDerivativeOf (plusMinusCurve tau) tangent →
    VectorDerivativeOf
      (plusMinusCurve (Symmetry.swapTriad tau)) tangentSwap →
    ((time : Time) →
      C3.complex3Add
        (C3.complex3Add (tangent time) (tangent time))
        (C3.complex3Add (tangentSwap time) (tangentSwap time))
      ≡ doubleTangent time) →
    VectorDerivativeOf (doubleMixedCurve tau) doubleTangent
  plusMinusDerivativesBuildDoubleMixedDerivative
      tau tangent tangentSwap doubleTangent d dSwap tangentMeaning =
    transportDerivative A
      (λ time →
        symEq (doubleMixedIsSwapPairedPointwise tau time))
      tangentMeaning
      (swapPairedDerivative tau tangent tangentSwap d dSwap)
    where
    symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    symEq refl = refl

round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivatives : Bool
round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivatives = true

round425SecondIndependentProjectorDerivativeNeeded : Bool
round425SecondIndependentProjectorDerivativeNeeded = false

round425OnlyRemainingCellDerivativeLeafIsLiteralPlusMinusDerivative : Bool
round425OnlyRemainingCellDerivativeLeafIsLiteralPlusMinusDerivative = true

round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivativesIsTrue :
  round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivatives ≡ true
round425DoubleMixedActualDerivativeReducedToTwoPlusMinusDerivativesIsTrue = refl

module DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact where

------------------------------------------------------------------------
-- ROUND426 / ACTUAL DERIVATIVE OF THE LITERAL PLUS-MINUS MIXED CELL
--
-- R292 has already computed the exact algebraic tangent of
--
--   A_tau(t) = P_+ u_p(t) x P_- u_q(t).
--
-- The remaining temporal seam is not Navier--Stokes algebra.  It is ordinary
-- vector calculus: project the two known velocity derivatives and apply the
-- bilinear cross-product product rule.  This file isolates exactly that rule.
--
-- Thus a caller supplies no arbitrary mixed-cell tangent: the target is
-- definitionally R292.cellTangent on the same literal R224 mixedPlusMinus cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityCellDampedTangentRound292Exact as R292

F : C3.RealField _
F = Rational.rationalRealField

record ProjectedCrossDerivativeCalculus
    (Time : Set)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) : Set₁ where
  field
    projectedCrossProductRule :
      {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
      (S : Helical.HelicalModeScalars F) →
      (p q : Z3.FourierMode) →
      (up dup uq duq : Time → C3.Complex3 F) →
      DerivativeOf up dup →
      DerivativeOf uq duq →
      DerivativeOf
        (λ time →
          Cross.complex3Cross
            (Helical.helicalProjectorPlus E I S p (up time))
            (Helical.helicalProjectorMinus E I S q (uq time)))
        (λ time →
          C3.complex3Add
            (Cross.complex3Cross
              (Helical.helicalProjectorPlus E I S p (dup time))
              (Helical.helicalProjectorMinus E I S q (uq time)))
            (Cross.complex3Cross
              (Helical.helicalProjectorPlus E I S p (up time))
              (Helical.helicalProjectorMinus E I S q (duq time))))

open ProjectedCrossDerivativeCalculus public

module ActualMixedCell
    (Time : Set)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (C : ProjectedCrossDerivativeCalculus Time DerivativeOf) where

  literalMixedCellCurve :
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
    (S : Helical.HelicalModeScalars F) →
    (velocity : Time → Z3.FourierMode → C3.Complex3 F) →
    Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  literalMixedCellCurve {E} {I} S velocity tau time =
    R224.mixedPlusMinus {E = E} {I = I} S (velocity time) tau

  literalMixedCellTangentCurve :
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
    (S : Helical.HelicalModeScalars F) →
    (velocity tangent : Time → Z3.FourierMode → C3.Complex3 F) →
    Physical.PhysicalTriadIncidence → Time → C3.Complex3 F
  literalMixedCellTangentCurve {E} {I} S velocity tangent tau time =
    R292.cellTangent {E = E} {I = I} S (velocity time) (tangent time) tau

  modalDerivativesBuildLiteralMixedCellDerivative :
    {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
    (S : Helical.HelicalModeScalars F) →
    (velocity tangent : Time → Z3.FourierMode → C3.Complex3 F) →
    (tau : Physical.PhysicalTriadIncidence) →
    DerivativeOf
      (λ time → velocity time (Physical.p tau))
      (λ time → tangent time (Physical.p tau)) →
    DerivativeOf
      (λ time → velocity time (Physical.q tau))
      (λ time → tangent time (Physical.q tau)) →
    DerivativeOf
      (literalMixedCellCurve S velocity tau)
      (literalMixedCellTangentCurve S velocity tangent tau)
  modalDerivativesBuildLiteralMixedCellDerivative S velocity tangent tau dp dq =
    projectedCrossProductRule C S
      (Physical.p tau) (Physical.q tau)
      (λ time → velocity time (Physical.p tau))
      (λ time → tangent time (Physical.p tau))
      (λ time → velocity time (Physical.q tau))
      (λ time → tangent time (Physical.q tau))
      dp dq

round426CallerSelectedMixedCellTangentEliminated : Bool
round426CallerSelectedMixedCellTangentEliminated = true

round426TargetIsLiteralR224MixedPlusMinus : Bool
round426TargetIsLiteralR224MixedPlusMinus = true

round426TargetTangentIsLiteralR292CellTangent : Bool
round426TargetTangentIsLiteralR292CellTangent = true

round426RemainingAnalyticLawIsProjectedCrossProductRule : Bool
round426RemainingAnalyticLawIsProjectedCrossProductRule = true

round426IntroducesNoNavierStokesEstimate : Bool
round426IntroducesNoNavierStokesEstimate = true

round426TargetIsLiteralR224MixedPlusMinusIsTrue :
  round426TargetIsLiteralR224MixedPlusMinus ≡ true
round426TargetIsLiteralR224MixedPlusMinusIsTrue = refl

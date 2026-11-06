{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalLogAtanUniformDerivativeRemainderExact where

------------------------------------------------------------------------
-- ORIGINAL LOG + MACHIN ATAN: EFFECTIVE UNIFORM DERIVATIVE RESIDUAL.
--
-- Source F1/F2 from BishopLogAtanFiniteDerivativeGeometricExact.
-- No derivative exchange assumption: this is an ALL-N exact
-- Bishop-order certificate on the LITERAL source factor derivatives:
--
--  |x| <= r<1   => |x^N| <= r^N.
--  |t| <= 1/2   => |(-t*t)^N| <= (1/4)^N.
--
-- The RHS depends ONLY on N and the selected radius, not on the
-- source point, and tends constructively to zero via the original
-- pinned vendor/bishop Sequence.∣r∣<1⇒rⁿ→0.
--
-- This pays the UNIFORM GEOMETRIC RESIDUAL bound, not uniform
-- factor quotient convergence of the infinite source function.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP
import Sequence as S

import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as Half
import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan

originalNegativeLogUniformDerivativeResidual :
  (radius : R.ℝ) →
  R.NonNegative radius →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) radius →
  (degree : Nat) →
  R._≤_
    (R.∣ R.pow point degree ∣)
    (R.pow radius degree)
originalNegativeLogUniformDerivativeResidual
    radius radiusNonnegative point inside degree =
  RP.≤-respˡ-≃
    (RP.≃-symm (S.∣xⁿ∣≃∣x∣ⁿ point degree))
    (S.x≤y∧nonNegx⇒xⁿ≤yⁿ
      degree inside (RP.nonNeg∣x∣ point))

nativeNegativeSquareAbsoluteIsSquare :
  (point : R.ℝ) →
  R._≃_
    (R.∣ R.-_ (R._*_ point point) ∣)
    (R._*_ point point)
nativeNegativeSquareAbsoluteIsSquare point =
  RP.≃-trans
    (RP.∣-x∣≃∣x∣ {x = R._*_ point point})
    (RP.nonNegx⇒∣x∣≃x
      (Square.bishopSquareNonnegative point))

nativeNegativeSquareBoundQuarter :
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  R._≤_
    (R.∣ R.-_ (R._*_ point point) ∣)
    Half.bishopQuarter
nativeNegativeSquareBoundQuarter point insideHalf =
  RP.≤-respˡ-≃
    (RP.≃-symm (nativeNegativeSquareAbsoluteIsSquare point))
    (RP.≤-respˡ-≃
      (Norm.absoluteSquare point)
      (Half.bishopHalfBallMagnitudeSquareBelowQuarter point insideHalf))

originalMachinAtanUniformDerivativeResidual :
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  (degree : Nat) →
  R._≤_
    (R.∣ R.pow (R.-_ (R._*_ point point)) degree ∣)
    (R.pow Half.bishopQuarter degree)
originalMachinAtanUniformDerivativeResidual point inside degree =
  let
    q = R.-_ (R._*_ point point)
  in
  RP.≤-respˡ-≃
    (RP.≃-symm (S.∣xⁿ∣≃∣x∣ⁿ q degree))
    (S.x≤y∧nonNegx⇒xⁿ≤yⁿ
      degree
      (nativeNegativeSquareBoundQuarter point inside)
      (RP.nonNeg∣x∣ q))

quarterAbsoluteBelowOne : R._<_ (R.∣ Half.bishopQuarter ∣) R.1ℝ
quarterAbsoluteBelowOne =
  RP.<-respˡ-≃
    (RP.≃-symm
      (RP.nonNegx⇒∣x∣≃x
        (RP.pos⇒nonNeg Atan.quarterPositive)))
    Atan.quarterBelowOne

quarterPowersConvergeToZero :
  S._ConvergesTo_
    (λ degree → R.pow Half.bishopQuarter degree)
    R.0ℝ
quarterPowersConvergeToZero =
  S.∣r∣<1⇒rⁿ→0 quarterAbsoluteBelowOne

-- This is a common, explicit point-independent modulus of every
-- original Machin derivative residual on the ENTIRE half-ball.
originalMachinUniformResidualCertificate :
  (degree : Nat) →
  (point : R.ℝ) →
  R._≤_ (R.∣ point ∣) Half.bishopHalf →
  R._≤_
    (R.∣ R.pow (R.-_ (R._*_ point point)) degree ∣)
    (R.pow Half.bishopQuarter degree)
originalMachinUniformResidualCertificate degree point inside =
  originalMachinAtanUniformDerivativeResidual point inside degree

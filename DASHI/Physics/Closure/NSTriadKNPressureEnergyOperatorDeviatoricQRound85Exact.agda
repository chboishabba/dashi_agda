module DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
--
-- Authors: Jinhee Jeong; Fazle Hussain.
-- Title: "On the identification of a vortex".
-- DOI: 10.1017/S0022112095000462.
--
-- ROUND85 / PRINCIPAL PRESSURE ENERGY OPERATOR
--
-- For a same-field energy pairing the pressure Hessian and pressure-transport
-- integration-by-parts source occur in the combination
--
--   H - (1/2) tr(H) I.
--
-- Write
--
--   H = H^D + (1/3) tr(H) I,
--   Q = (1/2) tr(H)            [because Delta p = 2Q].
--
-- Then exactly
--
--   H - (1/2) tr(H) I
--     = H^D - (1/6) tr(H) I
--     = H^D - (1/3) Q I.
--
-- This is the right principal pressure operator for the C4 energy pairing.
-- The selected hard-shell theorem still has a commutator/tail remainder because
-- the two mixed velocity legs are not globally identical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A

half third sixth : ℚ
half = Int.+ 1 / 2
third = Int.+ 1 / 3
sixth = Int.+ 1 / 6

matrixTrace : M.Matrix3 → ℚ
matrixTrace H = M.m11 H + M.m22 H + M.m33 H

qFromTrace : M.Matrix3 → ℚ
qFromTrace H = half * matrixTrace H

deviatoric : M.Matrix3 → M.Matrix3
deviatoric H =
  let t3 = third * matrixTrace H in
  M.matrix3
    (M.m11 H - t3) (M.m12 H)      (M.m13 H)
    (M.m21 H)      (M.m22 H - t3) (M.m23 H)
    (M.m31 H)      (M.m32 H)      (M.m33 H - t3)

pressureEnergyOperator : M.Matrix3 → M.Matrix3
pressureEnergyOperator H =
  let t2 = half * matrixTrace H in
  M.matrix3
    (M.m11 H - t2) (M.m12 H)      (M.m13 H)
    (M.m21 H)      (M.m22 H - t2) (M.m23 H)
    (M.m31 H)      (M.m32 H)      (M.m33 H - t2)

deviatoricMinusTraceSixth : M.Matrix3 → M.Matrix3
deviatoricMinusTraceSixth H =
  let t6 = sixth * matrixTrace H
      D = deviatoric H
  in
  M.matrix3
    (M.m11 D - t6) (M.m12 D)      (M.m13 D)
    (M.m21 D)      (M.m22 D - t6) (M.m23 D)
    (M.m31 D)      (M.m32 D)      (M.m33 D - t6)

deviatoricMinusQThird : M.Matrix3 → M.Matrix3
deviatoricMinusQThird H =
  let q3 = third * qFromTrace H
      D = deviatoric H
  in
  M.matrix3
    (M.m11 D - q3) (M.m12 D)      (M.m13 D)
    (M.m21 D)      (M.m22 D - q3) (M.m23 D)
    (M.m31 D)      (M.m32 D)      (M.m33 D - q3)

matrixExt : ∀ {left right : M.Matrix3} →
  M.m11 left ≡ M.m11 right → M.m12 left ≡ M.m12 right →
  M.m13 left ≡ M.m13 right → M.m21 left ≡ M.m21 right →
  M.m22 left ≡ M.m22 right → M.m23 left ≡ M.m23 right →
  M.m31 left ≡ M.m31 right → M.m32 left ≡ M.m32 right →
  M.m33 left ≡ M.m33 right → left ≡ right
matrixExt {M.matrix3 a11 a12 a13 a21 a22 a23 a31 a32 a33}
          {M.matrix3 .a11 .a12 .a13 .a21 .a22 .a23 .a31 .a32 .a33}
          refl refl refl refl refl refl refl refl refl = refl

pressureEnergyOperatorEqualsDeviatoricMinusTraceSixth : ∀ H →
  pressureEnergyOperator H ≡ deviatoricMinusTraceSixth H
pressureEnergyOperatorEqualsDeviatoricMinusTraceSixth
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33) =
  matrixExt
    (solve (h11 ∷ h22 ∷ h33 ∷ [])) refl refl refl
    (solve (h11 ∷ h22 ∷ h33 ∷ [])) refl refl refl
    (solve (h11 ∷ h22 ∷ h33 ∷ []))

pressureEnergyOperatorEqualsDeviatoricMinusQThird : ∀ H →
  pressureEnergyOperator H ≡ deviatoricMinusQThird H
pressureEnergyOperatorEqualsDeviatoricMinusQThird
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33) =
  matrixExt
    (solve (h11 ∷ h22 ∷ h33 ∷ [])) refl refl refl
    (solve (h11 ∷ h22 ∷ h33 ∷ [])) refl refl refl
    (solve (h11 ∷ h22 ∷ h33 ∷ []))

pressureEnergyBilinear : M.Matrix3 → V.Vector3 → ℚ
pressureEnergyBilinear H value = V.dot value (A.apply (pressureEnergyOperator H) value)

deviatoricQBilinear : M.Matrix3 → V.Vector3 → ℚ
deviatoricQBilinear H value =
  V.dot value (A.apply (deviatoricMinusQThird H) value)

pressureEnergyBilinearEqualsDeviatoricQ : ∀ H value →
  pressureEnergyBilinear H value ≡ deviatoricQBilinear H value
pressureEnergyBilinearEqualsDeviatoricQ H value
  rewrite pressureEnergyOperatorEqualsDeviatoricMinusQThird H = refl

round85PressureEnergyOperatorDeviatoricQCompressionExact : Bool
round85PressureEnergyOperatorDeviatoricQCompressionExact = true

round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ : Bool
round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ = true

round85PrincipalPressureEnergyUsesDeviatoricHessianAndQIsTrue :
  round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ ≡ true
round85PrincipalPressureEnergyUsesDeviatoricHessianAndQIsTrue = refl

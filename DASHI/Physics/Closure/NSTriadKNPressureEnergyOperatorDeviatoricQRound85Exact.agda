module DASHI.Physics.Closure.NSTriadKNPressureEnergyOperatorDeviatoricQRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Koji Ohkitani; Shigeo Kishiba.
-- Title: "Nonlocal nature of vortex stretching in an inviscid fluid".
-- Physics of Fluids 7 (1995), 411--421.
-- DOI: 10.1063/1.868633.
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
-- Ohkitani--Kishiba use the standard pressure-Hessian trace/deviatoric split:
-- the trace is the local pressure-Poisson invariant, while the trace-free part
-- is the genuinely anisotropic/nonlocal pressure contribution.  On the DASHI
-- normalization Delta p = 2Q, the same-field pressure-energy operator is
--
--   H - (1/2) tr(H) I
--     = H^D - (1/6) tr(H) I
--     = H^D - (1/3) Q I.
--
-- This file now pushes that matrix identity through the literal velocity
-- pairing as well:
--
--   <v,(H - (1/2)tr(H)I)v>
--     = <v,H^D v> - (1/3) Q |v|^2.
--
-- Thus C4a has an exact local/nonlocal scalar split on the principal packet.
-- What remains analytic is to control the anisotropic H^D work in the selected
-- dangerous-event currency; Q alone cannot recover that term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

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

------------------------------------------------------------------------
-- Scalar local/nonlocal split used directly by C4a.
------------------------------------------------------------------------

deviatoricBilinear : M.Matrix3 → V.Vector3 → ℚ
deviatoricBilinear H value =
  V.dot value (A.apply (deviatoric H) value)

localQEnergyCorrection : M.Matrix3 → V.Vector3 → ℚ
localQEnergyCorrection H value =
  third * qFromTrace H * V.normSquared value

deviatoricQBilinearSplitsAnisotropicMinusLocalQ : ∀ H value →
  deviatoricQBilinear H value
  ≡ deviatoricBilinear H value - localQEnergyCorrection H value
deviatoricQBilinearSplitsAnisotropicMinusLocalQ
    (M.matrix3 h11 h12 h13 h21 h22 h23 h31 h32 h33)
    (V.v3 vx vy vz) =
  solve
    (h11 ∷ h12 ∷ h13 ∷ h21 ∷ h22 ∷ h23 ∷ h31 ∷ h32 ∷ h33
      ∷ vx ∷ vy ∷ vz ∷ [])

pressureEnergyBilinearSplitsAnisotropicMinusLocalQ : ∀ H value →
  pressureEnergyBilinear H value
  ≡ deviatoricBilinear H value - localQEnergyCorrection H value
pressureEnergyBilinearSplitsAnisotropicMinusLocalQ H value =
  trans
    (pressureEnergyBilinearEqualsDeviatoricQ H value)
    (deviatoricQBilinearSplitsAnisotropicMinusLocalQ H value)

round85PressureEnergyOperatorDeviatoricQCompressionExact : Bool
round85PressureEnergyOperatorDeviatoricQCompressionExact = true

round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ : Bool
round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ = true

round85PrincipalPressurePairingSplitsAnisotropicAndLocalQ : Bool
round85PrincipalPressurePairingSplitsAnisotropicAndLocalQ = true

round85PrincipalPressureEnergyUsesDeviatoricHessianAndQIsTrue :
  round85PrincipalPressureEnergyUsesDeviatoricHessianAndQ ≡ true
round85PrincipalPressureEnergyUsesDeviatoricHessianAndQIsTrue = refl

round85PrincipalPressurePairingSplitsAnisotropicAndLocalQIsTrue :
  round85PrincipalPressurePairingSplitsAnisotropicAndLocalQ ≡ true
round85PrincipalPressurePairingSplitsAnisotropicAndLocalQIsTrue = refl

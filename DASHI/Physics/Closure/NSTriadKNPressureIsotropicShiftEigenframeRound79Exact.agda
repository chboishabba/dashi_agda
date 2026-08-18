module DASHI.Physics.Closure.NSTriadKNPressureIsotropicShiftEigenframeRound79Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in the dynamics of intense velocity gradients in
-- turbulent flows".
-- Journal of Fluid Mechanics 973 (2023), A23.
-- DOI: 10.1017/jfm.2023.786.
-- arXiv: 2308.03902.
--
-- Authors: Wm. T. Ashurst; A. R. Kerstein; R. M. Kerr; C. H. Gibson.
-- Title: "Alignment of vorticity and scalar gradient with strain rate in
-- simulated Navier-Stokes turbulence".
-- Physics of Fluids 30 (1987), 2343--2353.
-- DOI: 10.1063/1.866513.
--
-- ROUND79 / PRESSURE-EIGENFRAME PRECISION CORRECTION
--
-- Ashurst et al. concern alignment with the STRAIN eigenframe. Buaria--Pumir
-- separately report near-alignment with the smallest eigenvector of the FULL
-- pressure Hessian H. Round78 used the DEVIATORIC pressure Hessian H^D.
--
-- This is not a carrier mismatch: H = H^D + c I, where c = tr(H)/3. Adding
-- an isotropic scalar multiple of the identity preserves every eigenvector and
-- shifts only the eigenvalue. The theorem below proves that fact on the exact
-- rational three-vector/matrix carrier already used by the Fourier-strain lane.
-- Therefore full-H and H^D have the same eigenspaces (including degenerate
-- eigenspaces); strain S remains a distinct operator/eigenframe.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A

identityMatrix : M.Matrix3
identityMatrix = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 1ℚ

addMatrix : M.Matrix3 → M.Matrix3 → M.Matrix3
addMatrix left right = M.matrix3
  (M.m11 left + M.m11 right)
  (M.m12 left + M.m12 right)
  (M.m13 left + M.m13 right)
  (M.m21 left + M.m21 right)
  (M.m22 left + M.m22 right)
  (M.m23 left + M.m23 right)
  (M.m31 left + M.m31 right)
  (M.m32 left + M.m32 right)
  (M.m33 left + M.m33 right)

scaleMatrix : ℚ → M.Matrix3 → M.Matrix3
scaleMatrix scalar matrix = M.matrix3
  (scalar * M.m11 matrix)
  (scalar * M.m12 matrix)
  (scalar * M.m13 matrix)
  (scalar * M.m21 matrix)
  (scalar * M.m22 matrix)
  (scalar * M.m23 matrix)
  (scalar * M.m31 matrix)
  (scalar * M.m32 matrix)
  (scalar * M.m33 matrix)

isotropicShift : ℚ → M.Matrix3 → M.Matrix3
isotropicShift scalar deviatoric =
  addMatrix deviatoric (scaleMatrix scalar identityMatrix)

applyAddMatrix : ∀ left right value →
  A.apply (addMatrix left right) value
  ≡ V.add (A.apply left value) (A.apply right value)
applyAddMatrix
  (M.matrix3 a11 a12 a13 a21 a22 a23 a31 a32 a33)
  (M.matrix3 b11 b12 b13 b21 b22 b23 b31 b32 b33)
  (V.v3 x y z) =
  V.vectorExt
    (solve (a11 ∷ a12 ∷ a13 ∷ b11 ∷ b12 ∷ b13 ∷ x ∷ y ∷ z ∷ []))
    (solve (a21 ∷ a22 ∷ a23 ∷ b21 ∷ b22 ∷ b23 ∷ x ∷ y ∷ z ∷ []))
    (solve (a31 ∷ a32 ∷ a33 ∷ b31 ∷ b32 ∷ b33 ∷ x ∷ y ∷ z ∷ []))

applyScaledIdentity : ∀ scalar value →
  A.apply (scaleMatrix scalar identityMatrix) value ≡ V.scale scalar value
applyScaledIdentity scalar (V.v3 x y z) =
  V.vectorExt
    (solve (scalar ∷ x ∷ []))
    (solve (scalar ∷ y ∷ []))
    (solve (scalar ∷ z ∷ []))

addScaledSameVector : ∀ a b value →
  V.add (V.scale a value) (V.scale b value)
  ≡ V.scale (a + b) value
addScaledSameVector a b (V.v3 x y z) =
  V.vectorExt
    (solve (a ∷ b ∷ x ∷ []))
    (solve (a ∷ b ∷ y ∷ []))
    (solve (a ∷ b ∷ z ∷ []))

isotropicShiftRoundtrip : ∀ scalar matrix →
  isotropicShift (- scalar) (isotropicShift scalar matrix) ≡ matrix
isotropicShiftRoundtrip scalar
    (M.matrix3 a11 a12 a13 a21 a22 a23 a31 a32 a33) =
  M.matrixExt
    (solve (scalar ∷ a11 ∷ []))
    (solve (scalar ∷ a12 ∷ []))
    (solve (scalar ∷ a13 ∷ []))
    (solve (scalar ∷ a21 ∷ []))
    (solve (scalar ∷ a22 ∷ []))
    (solve (scalar ∷ a23 ∷ []))
    (solve (scalar ∷ a31 ∷ []))
    (solve (scalar ∷ a32 ∷ []))
    (solve (scalar ∷ a33 ∷ []))

record Eigenpair (matrix : M.Matrix3) : Set where
  constructor eigenpair
  field
    eigenvector : V.Vector3
    eigenvalue : ℚ
    eigenEquation : A.apply matrix eigenvector ≡ V.scale eigenvalue eigenvector

open Eigenpair public

isotropicShiftPreservesEigenpair :
  ∀ scalar deviatoric →
  Eigenpair deviatoric →
  Eigenpair (isotropicShift scalar deviatoric)
isotropicShiftPreservesEigenpair scalar deviatoric pair =
  eigenpair
    (eigenvector pair)
    (eigenvalue pair + scalar)
    (trans
      (applyAddMatrix deviatoric (scaleMatrix scalar identityMatrix) (eigenvector pair))
      (trans
        (cong
          (V.add (A.apply deviatoric (eigenvector pair)))
          (applyScaledIdentity scalar (eigenvector pair)))
        (trans
          (cong
            (λ left → V.add left (V.scale scalar (eigenvector pair)))
            (eigenEquation pair))
          (addScaledSameVector
            (eigenvalue pair) scalar (eigenvector pair)))))

isotropicShiftEigenpairReflects :
  ∀ scalar deviatoric →
  Eigenpair (isotropicShift scalar deviatoric) →
  Eigenpair deviatoric
isotropicShiftEigenpairReflects scalar deviatoric pair =
  subst
    Eigenpair
    (isotropicShiftRoundtrip scalar deviatoric)
    (isotropicShiftPreservesEigenpair
      (- scalar)
      (isotropicShift scalar deviatoric)
      pair)

round79FullPressureAndDeviatoricPressureShareEigenframe : Bool
round79FullPressureAndDeviatoricPressureShareEigenframe = true

round79StrainAndPressureEigenframesIdentified : Bool
round79StrainAndPressureEigenframesIdentified = false

round79FullPressureAndDeviatoricPressureShareEigenframeIsTrue :
  round79FullPressureAndDeviatoricPressureShareEigenframe ≡ true
round79FullPressureAndDeviatoricPressureShareEigenframeIsTrue = refl

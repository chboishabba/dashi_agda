module DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Derive the literal nonzero Fourier strain multiplier from the repository's
-- exact Biot--Savart velocity, rather than treating the angular strain symbol
-- as an independent object.
--
-- With
--
--   u_k = |k|^-2 (k cross omega_k)
--
-- after absorbing the common Fourier phase sign, define
--
--   S_k(omega) = -1/2 [ k tensor u_k + u_k tensor k ].
--
-- This module proves exactly
--
--   S_k(omega)
--     = |k|^-2 S^ang_k(omega),
--
-- where `S^ang` is the corrected Round-37 symbol, and therefore
--
--   v . S_k(omega) v
--     = - |k|^-2 (k.v) k.(omega cross v).
--
-- This closes the nonzero modewise multiplier identification needed before
-- the periodic torus/PV kernel realization.  The zero Fourier mode is not a
-- `ProjectionMode` (it has no inverse norm); the physical periodic multiplier
-- must assign that mode zero separately, which is exactly the hypothesis used
-- by the Round-38 zero-mode-to-zero-mass theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNVortexStretchingGeometricFactorRound37Exact as Stretch

half : ℚ
half = Int.+ 1 / 2

minusHalf : ℚ
minusHalf = - half

scaleMatrix : ℚ → Matrix.Matrix3 → Matrix.Matrix3
scaleMatrix scalar matrix =
  Matrix.matrix3
    (scalar * Matrix.m11 matrix)
    (scalar * Matrix.m12 matrix)
    (scalar * Matrix.m13 matrix)
    (scalar * Matrix.m21 matrix)
    (scalar * Matrix.m22 matrix)
    (scalar * Matrix.m23 matrix)
    (scalar * Matrix.m31 matrix)
    (scalar * Matrix.m32 matrix)
    (scalar * Matrix.m33 matrix)

fourierStrainMultiplier :
  V.ProjectionMode → V.Vector3 → Matrix.Matrix3
fourierStrainMultiplier modeData omega =
  let
    k = V.mode modeData
    u = BS.biotSavart modeData omega
  in
  Matrix.matrix3
    (minusHalf * (V.x k * V.x u + V.x u * V.x k))
    (minusHalf * (V.x k * V.y u + V.x u * V.y k))
    (minusHalf * (V.x k * V.z u + V.x u * V.z k))
    (minusHalf * (V.y k * V.x u + V.y u * V.x k))
    (minusHalf * (V.y k * V.y u + V.y u * V.y k))
    (minusHalf * (V.y k * V.z u + V.y u * V.z k))
    (minusHalf * (V.z k * V.x u + V.z u * V.x k))
    (minusHalf * (V.z k * V.y u + V.z u * V.y k))
    (minusHalf * (V.z k * V.z u + V.z u * V.z k))

fourierStrainMultiplierExact :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  fourierStrainMultiplier modeData omega
  ≡ scaleMatrix
      (V.inverseNormSquared modeData)
      (Angular.angularStrain (V.mode modeData) omega)
fourierStrainMultiplierExact
    (V.projection-mode (V.v3 kx ky kz) inv inverseLaw)
    (V.v3 wx wy wz) =
  Matrix.matrixExt
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))
    (solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ inv ∷ minusHalf ∷ []))

applyScaledMatrix : ∀ scalar matrix value →
  Angular.apply (scaleMatrix scalar matrix) value
  ≡ V.scale scalar (Angular.apply matrix value)
applyScaledMatrix scalar
    (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33)
    (V.v3 vx vy vz) =
  V.vectorExt
    (solve (scalar ∷ m11 ∷ m12 ∷ m13 ∷ vx ∷ vy ∷ vz ∷ []))
    (solve (scalar ∷ m21 ∷ m22 ∷ m23 ∷ vx ∷ vy ∷ vz ∷ []))
    (solve (scalar ∷ m31 ∷ m32 ∷ m33 ∷ vx ∷ vy ∷ vz ∷ []))

fourierStrainActionExact :
  (modeData : V.ProjectionMode) →
  (omega value : V.Vector3) →
  Angular.apply (fourierStrainMultiplier modeData omega) value
  ≡
  V.scale (V.inverseNormSquared modeData)
    (Angular.apply (Angular.angularStrain (V.mode modeData) omega) value)
fourierStrainActionExact modeData omega value =
  trans
    (cong
      (λ matrix → Angular.apply matrix value)
      (fourierStrainMultiplierExact modeData omega))
    (applyScaledMatrix
      (V.inverseNormSquared modeData)
      (Angular.angularStrain (V.mode modeData) omega)
      value)

fourierStretchingScalar :
  V.ProjectionMode → V.Vector3 → V.Vector3 → ℚ
fourierStretchingScalar modeData source target =
  V.dot target
    (Angular.apply (fourierStrainMultiplier modeData source) target)

fourierStretchingScalarExact :
  (modeData : V.ProjectionMode) →
  (source target : V.Vector3) →
  fourierStretchingScalar modeData source target
  ≡
  V.inverseNormSquared modeData
    * Stretch.stretchingScalar (V.mode modeData) source target
fourierStretchingScalarExact modeData source target =
  trans
    (cong
      (V.dot target)
      (fourierStrainActionExact modeData source target))
    (V.dotScaleRight
      target
      (Angular.apply (Angular.angularStrain (V.mode modeData) source) target)
      (V.inverseNormSquared modeData))

fourierStretchingMisalignmentExact :
  (modeData : V.ProjectionMode) →
  (source target : V.Vector3) →
  fourierStretchingScalar modeData source target
  ≡
  (- V.inverseNormSquared modeData)
    * V.dot (V.mode modeData) target
    * V.dot (V.mode modeData) (BS.cross source target)
fourierStretchingMisalignmentExact modeData source target =
  trans
    (fourierStretchingScalarExact modeData source target)
    (trans
      (cong
        (V.inverseNormSquared modeData *_)
        (Stretch.stretchingScalarMisalignmentFactor
          (V.mode modeData) source target))
      (solve
        ( V.inverseNormSquared modeData
        ∷ V.dot (V.mode modeData) target
        ∷ V.dot (V.mode modeData) (BS.cross source target)
        ∷ [])))

fourierStrainMultiplierModewiseClosed : Bool
fourierStrainMultiplierModewiseClosed = true

literalPeriodicStrainKernelRealizationConstructed : Bool
literalPeriodicStrainKernelRealizationConstructed = false

fourierStrainMultiplierModewiseClosedIsTrue :
  fourierStrainMultiplierModewiseClosed ≡ true
fourierStrainMultiplierModewiseClosedIsTrue = refl

module DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- Communications in Partial Differential Equations 21 (1996), 559--571.
-- DOI: 10.1080/03605309608821197.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01240221.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Construct the literal nonzero Fourier strain multiplier without introducing
-- a normalized direction or a square root.  For a nonzero Fourier mode k,
-- inverse-square datum |k|^-2, and vorticity coefficient omega, set
--
--   a = k cross omega,
--   S_k(omega)
--     = - 1/(2 |k|^2) (k tensor a + a tensor k).
--
-- This is the exact symmetric-gradient symbol obtained by composing the
-- Fourier Biot--Savart inverse with the gradient.  We prove:
--
--   * exact symmetry and trace zero;
--   * the action formula on an arbitrary vector v;
--   * v . S_k(omega) v
--       = - |k|^-2 (k.v) ((k cross omega).v);
--   * the self-mode quadratic stretching is exactly zero;
--   * if k.omega = 0, then S_k(omega) omega = 0;
--   * the exact Frobenius identity
--
--       ||S_k(omega)||_F^2 = (1/2) |omega|^2
--
--     for transverse omega.
--
-- The last identity is a sharp frequency-uniform L2 multiplier statement at
-- one Fourier mode.  It is not the still-open periodic principal-value kernel,
-- Calderon--Zygmund increment estimate, or the cross-mode HH-good owner bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix

half two : ℚ
half = Int.+ 1 / 2
two = Int.+ 2 / 1

minusHalf : ℚ
minusHalf = - half

strainCoefficient : V.ProjectionMode → ℚ
strainCoefficient modeData =
  minusHalf * V.inverseNormSquared modeData

fourierStrain : V.ProjectionMode → V.Vector3 → Matrix.Matrix3
fourierStrain modeData omega =
  let
    k = V.mode modeData
    a = BS.cross k omega
    c = strainCoefficient modeData
  in
  Matrix.matrix3
    (c * (V.x k * V.x a + V.x a * V.x k))
    (c * (V.x k * V.y a + V.x a * V.y k))
    (c * (V.x k * V.z a + V.x a * V.z k))
    (c * (V.y k * V.x a + V.y a * V.x k))
    (c * (V.y k * V.y a + V.y a * V.y k))
    (c * (V.y k * V.z a + V.y a * V.z k))
    (c * (V.z k * V.x a + V.z a * V.x k))
    (c * (V.z k * V.y a + V.z a * V.y k))
    (c * (V.z k * V.z a + V.z a * V.z k))

fourierStrainSymmetric12 :
  ∀ modeData omega →
  Matrix.m12 (fourierStrain modeData omega)
  ≡ Matrix.m21 (fourierStrain modeData omega)
fourierStrainSymmetric12 modeData omega
  with V.mode modeData | BS.cross (V.mode modeData) omega
... | V.v3 kx ky kz | V.v3 ax ay az =
  solve (kx ∷ ky ∷ ax ∷ ay ∷ strainCoefficient modeData ∷ [])

fourierStrainSymmetric13 :
  ∀ modeData omega →
  Matrix.m13 (fourierStrain modeData omega)
  ≡ Matrix.m31 (fourierStrain modeData omega)
fourierStrainSymmetric13 modeData omega
  with V.mode modeData | BS.cross (V.mode modeData) omega
... | V.v3 kx ky kz | V.v3 ax ay az =
  solve (kx ∷ kz ∷ ax ∷ az ∷ strainCoefficient modeData ∷ [])

fourierStrainSymmetric23 :
  ∀ modeData omega →
  Matrix.m23 (fourierStrain modeData omega)
  ≡ Matrix.m32 (fourierStrain modeData omega)
fourierStrainSymmetric23 modeData omega
  with V.mode modeData | BS.cross (V.mode modeData) omega
... | V.v3 kx ky kz | V.v3 ax ay az =
  solve (ky ∷ kz ∷ ay ∷ az ∷ strainCoefficient modeData ∷ [])

trace : Matrix.Matrix3 → ℚ
trace matrix =
  Matrix.m11 matrix + Matrix.m22 matrix + Matrix.m33 matrix

fourierStrainTraceMeaning :
  ∀ modeData omega →
  trace (fourierStrain modeData omega)
  ≡ two * strainCoefficient modeData
      * V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega)
fourierStrainTraceMeaning modeData omega
  with V.mode modeData | BS.cross (V.mode modeData) omega
... | V.v3 kx ky kz | V.v3 ax ay az =
  solve
    ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
    ∷ strainCoefficient modeData ∷ [])

fourierStrainTraceFree :
  ∀ modeData omega → trace (fourierStrain modeData omega) ≡ 0ℚ
fourierStrainTraceFree modeData omega =
  begin
    trace (fourierStrain modeData omega)
  ≡⟨ fourierStrainTraceMeaning modeData omega ⟩
    two * strainCoefficient modeData
      * V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega)
  ≡⟨ cong
       (λ pairing → two * strainCoefficient modeData * pairing)
       (BS.crossOrthogonalLeft
         (V.mode modeData) omega) ⟩
    two * strainCoefficient modeData * 0ℚ
  ≡⟨ solve (strainCoefficient modeData ∷ []) ⟩
    0ℚ
  ∎

apply : Matrix.Matrix3 → V.Vector3 → V.Vector3
apply matrix (V.v3 vx vy vz) =
  V.v3
    (Matrix.m11 matrix * vx + Matrix.m12 matrix * vy
      + Matrix.m13 matrix * vz)
    (Matrix.m21 matrix * vx + Matrix.m22 matrix * vy
      + Matrix.m23 matrix * vz)
    (Matrix.m31 matrix * vx + Matrix.m32 matrix * vy
      + Matrix.m33 matrix * vz)

fourierStrainActionFormula :
  ∀ modeData omega value →
  apply (fourierStrain modeData omega) value
  ≡ V.scale (strainCoefficient modeData)
      (V.add
        (V.scale
          (V.dot (BS.cross (V.mode modeData) omega) value)
          (V.mode modeData))
        (V.scale
          (V.dot (V.mode modeData) value)
          (BS.cross (V.mode modeData) omega)))
fourierStrainActionFormula modeData omega value
  with V.mode modeData
     | BS.cross (V.mode modeData) omega
     | value
... | V.v3 kx ky kz | V.v3 ax ay az | V.v3 vx vy vz =
  V.vectorExt
    (solve
      ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
      ∷ vx ∷ vy ∷ vz ∷ strainCoefficient modeData ∷ []))
    (solve
      ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
      ∷ vx ∷ vy ∷ vz ∷ strainCoefficient modeData ∷ []))
    (solve
      ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
      ∷ vx ∷ vy ∷ vz ∷ strainCoefficient modeData ∷ []))

stretchingQuadraticFactorization :
  ∀ modeData omega value →
  V.dot value (apply (fourierStrain modeData omega) value)
  ≡ (- V.inverseNormSquared modeData)
      * (V.dot (V.mode modeData) value
        * V.dot (BS.cross (V.mode modeData) omega) value)
stretchingQuadraticFactorization modeData omega value
  with V.mode modeData
     | BS.cross (V.mode modeData) omega
     | value
... | V.v3 kx ky kz | V.v3 ax ay az | V.v3 vx vy vz =
  solve
    ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
    ∷ vx ∷ vy ∷ vz
    ∷ V.inverseNormSquared modeData ∷ [])

fourierStrainSelfQuadraticVanishes :
  ∀ modeData omega →
  V.dot omega (apply (fourierStrain modeData omega) omega) ≡ 0ℚ
fourierStrainSelfQuadraticVanishes modeData omega =
  begin
    V.dot omega (apply (fourierStrain modeData omega) omega)
  ≡⟨ stretchingQuadraticFactorization modeData omega omega ⟩
    (- V.inverseNormSquared modeData)
      * (V.dot (V.mode modeData) omega
        * V.dot (BS.cross (V.mode modeData) omega) omega)
  ≡⟨ cong
       (λ pairing →
         (- V.inverseNormSquared modeData)
           * (V.dot (V.mode modeData) omega * pairing))
       (BS.crossOrthogonalRight (V.mode modeData) omega) ⟩
    (- V.inverseNormSquared modeData)
      * (V.dot (V.mode modeData) omega * 0ℚ)
  ≡⟨ solve
       (V.inverseNormSquared modeData
       ∷ V.dot (V.mode modeData) omega ∷ []) ⟩
    0ℚ
  ∎

fourierStrainOwnModeActionVanishes :
  ∀ modeData omega →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  apply (fourierStrain modeData omega) omega
  ≡ V.v3 0ℚ 0ℚ 0ℚ
fourierStrainOwnModeActionVanishes modeData omega transverse =
  begin
    apply (fourierStrain modeData omega) omega
  ≡⟨ fourierStrainActionFormula modeData omega omega ⟩
    V.scale (strainCoefficient modeData)
      (V.add
        (V.scale
          (V.dot (BS.cross (V.mode modeData) omega) omega)
          (V.mode modeData))
        (V.scale
          (V.dot (V.mode modeData) omega)
          (BS.cross (V.mode modeData) omega)))
  ≡⟨ cong
       (λ pairing →
         V.scale (strainCoefficient modeData)
           (V.add
             (V.scale pairing (V.mode modeData))
             (V.scale
               (V.dot (V.mode modeData) omega)
               (BS.cross (V.mode modeData) omega))))
       (BS.crossOrthogonalRight (V.mode modeData) omega) ⟩
    V.scale (strainCoefficient modeData)
      (V.add
        (V.scale 0ℚ (V.mode modeData))
        (V.scale
          (V.dot (V.mode modeData) omega)
          (BS.cross (V.mode modeData) omega)))
  ≡⟨ cong
       (λ pairing →
         V.scale (strainCoefficient modeData)
           (V.add
             (V.scale 0ℚ (V.mode modeData))
             (V.scale pairing
               (BS.cross (V.mode modeData) omega))))
       transverse ⟩
    V.scale (strainCoefficient modeData)
      (V.add
        (V.scale 0ℚ (V.mode modeData))
        (V.scale 0ℚ (BS.cross (V.mode modeData) omega)))
  ≡⟨ zeroAction modeData omega ⟩
    V.v3 0ℚ 0ℚ 0ℚ
  ∎
  where
  zeroAction :
    ∀ modeData omega →
    V.scale (strainCoefficient modeData)
      (V.add
        (V.scale 0ℚ (V.mode modeData))
        (V.scale 0ℚ (BS.cross (V.mode modeData) omega)))
    ≡ V.v3 0ℚ 0ℚ 0ℚ
  zeroAction selectedMode selectedOmega
    with V.mode selectedMode
       | BS.cross (V.mode selectedMode) selectedOmega
  ... | V.v3 kx ky kz | V.v3 ax ay az =
    V.vectorExt
      (solve (kx ∷ ax ∷ strainCoefficient selectedMode ∷ []))
      (solve (ky ∷ ay ∷ strainCoefficient selectedMode ∷ []))
      (solve (kz ∷ az ∷ strainCoefficient selectedMode ∷ []))

frobeniusSquared : Matrix.Matrix3 → ℚ
frobeniusSquared matrix =
  Matrix.m11 matrix * Matrix.m11 matrix
  + Matrix.m12 matrix * Matrix.m12 matrix
  + Matrix.m13 matrix * Matrix.m13 matrix
  + Matrix.m21 matrix * Matrix.m21 matrix
  + Matrix.m22 matrix * Matrix.m22 matrix
  + Matrix.m23 matrix * Matrix.m23 matrix
  + Matrix.m31 matrix * Matrix.m31 matrix
  + Matrix.m32 matrix * Matrix.m32 matrix
  + Matrix.m33 matrix * Matrix.m33 matrix

fourierStrainFrobeniusExpansion :
  ∀ modeData omega →
  frobeniusSquared (fourierStrain modeData omega)
  ≡ two * strainCoefficient modeData * strainCoefficient modeData
      * (V.normSquared (V.mode modeData)
          * V.normSquared (BS.cross (V.mode modeData) omega)
        + V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega)
          * V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega))
fourierStrainFrobeniusExpansion modeData omega
  with V.mode modeData | BS.cross (V.mode modeData) omega
... | V.v3 kx ky kz | V.v3 ax ay az =
  solve
    ( kx ∷ ky ∷ kz ∷ ax ∷ ay ∷ az
    ∷ strainCoefficient modeData ∷ [])

fourierStrainFrobeniusCrossExact :
  ∀ modeData omega →
  frobeniusSquared (fourierStrain modeData omega)
  ≡ half * V.inverseNormSquared modeData
      * V.normSquared (BS.cross (V.mode modeData) omega)
fourierStrainFrobeniusCrossExact modeData omega =
  let
    inv = V.inverseNormSquared modeData
    k2 = V.normSquared (V.mode modeData)
    a2 = V.normSquared (BS.cross (V.mode modeData) omega)
  in
  begin
    frobeniusSquared (fourierStrain modeData omega)
  ≡⟨ fourierStrainFrobeniusExpansion modeData omega ⟩
    two * strainCoefficient modeData * strainCoefficient modeData
      * (k2 * a2
        + V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega)
          * V.dot (V.mode modeData) (BS.cross (V.mode modeData) omega))
  ≡⟨ cong
       (λ pairing →
         two * strainCoefficient modeData * strainCoefficient modeData
           * (k2 * a2 + pairing * pairing))
       (BS.crossOrthogonalLeft (V.mode modeData) omega) ⟩
    two * strainCoefficient modeData * strainCoefficient modeData
      * (k2 * a2 + 0ℚ * 0ℚ)
  ≡⟨ solve (inv ∷ k2 ∷ a2 ∷ []) ⟩
    (half * inv * a2) * (inv * k2)
  ≡⟨ cong ((half * inv * a2) *_)
       (V.inverseLaw modeData) ⟩
    (half * inv * a2) * 1ℚ
  ≡⟨ solve (inv ∷ a2 ∷ []) ⟩
    half * inv * a2
  ∎

fourierStrainFrobeniusTransverseExact :
  ∀ modeData omega →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  frobeniusSquared (fourierStrain modeData omega)
  ≡ half * V.normSquared omega
fourierStrainFrobeniusTransverseExact modeData omega transverse =
  let
    inv = V.inverseNormSquared modeData
    k2 = V.normSquared (V.mode modeData)
    w2 = V.normSquared omega
    a2 = V.normSquared (BS.cross (V.mode modeData) omega)

    crossNorm : a2 ≡ k2 * w2
    crossNorm =
      trans
        (BS.crossNormLagrange (V.mode modeData) omega)
        (trans
          (cong
            (λ pairing → k2 * w2 - pairing * pairing)
            transverse)
          (solve (k2 ∷ w2 ∷ [])))
  in
  begin
    frobeniusSquared (fourierStrain modeData omega)
  ≡⟨ fourierStrainFrobeniusCrossExact modeData omega ⟩
    half * inv * a2
  ≡⟨ cong (half * inv *_) crossNorm ⟩
    half * inv * (k2 * w2)
  ≡⟨ solve (inv ∷ k2 ∷ w2 ∷ []) ⟩
    half * (inv * k2) * w2
  ≡⟨ cong (λ product → half * product * w2)
       (V.inverseLaw modeData) ⟩
    half * 1ℚ * w2
  ≡⟨ solve (w2 ∷ []) ⟩
    half * w2
  ∎

periodicFourierStrainMultiplierExactClosed : Bool
periodicFourierStrainMultiplierExactClosed = true

physicalPeriodicPrincipalValueKernelConstructed : Bool
physicalPeriodicPrincipalValueKernelConstructed = false

periodicFourierStrainMultiplierExactClosedIsTrue :
  periodicFourierStrainMultiplierExactClosed ≡ true
periodicFourierStrainMultiplierExactClosedIsTrue = refl

physicalPeriodicPrincipalValueKernelConstructedIsFalse :
  physicalPeriodicPrincipalValueKernelConstructed ≡ false
physicalPeriodicPrincipalValueKernelConstructedIsFalse = refl

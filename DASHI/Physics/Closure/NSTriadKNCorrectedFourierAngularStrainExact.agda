module DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact where

------------------------------------------------------------------------
-- PROVENANCE
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
-- PURPOSE
-- Replace the defective displayed expression epsilon_ikl theta_k theta_l by
-- the actual Fourier strain symbol obtained from Biot--Savart inversion.
-- With the Fourier phase convention absorbed into the sign, set
--
--   a = theta cross omega,
--   S_theta(omega) = -1/2 (theta tensor a + a tensor theta).
--
-- This symbol is symmetric and trace free.  It is genuinely nonzero as an
-- operator, while its contraction against the same transverse single-mode
-- vorticity vanishes exactly.  The latter is a real diagonal/self-mode
-- depletion identity; it does not cancel cross-mode stretching and therefore
-- does not by itself prove regularity or a non-orientable eigenbundle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _+_; _*_; -_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≢_; cong; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Audit

half : ℚ
half = Int.+ 1 / 2

minusHalf : ℚ
minusHalf = - half

angularStrain : V.Vector3 → V.Vector3 → Audit.Matrix3
angularStrain theta omega =
  let
    tangent = BS.cross theta omega
  in
  Audit.matrix3
    (minusHalf * (V.x theta * V.x tangent + V.x tangent * V.x theta))
    (minusHalf * (V.x theta * V.y tangent + V.x tangent * V.y theta))
    (minusHalf * (V.x theta * V.z tangent + V.x tangent * V.z theta))
    (minusHalf * (V.y theta * V.x tangent + V.y tangent * V.x theta))
    (minusHalf * (V.y theta * V.y tangent + V.y tangent * V.y theta))
    (minusHalf * (V.y theta * V.z tangent + V.y tangent * V.z theta))
    (minusHalf * (V.z theta * V.x tangent + V.z tangent * V.x theta))
    (minusHalf * (V.z theta * V.y tangent + V.z tangent * V.y theta))
    (minusHalf * (V.z theta * V.z tangent + V.z tangent * V.z theta))

angularStrainSymmetric12 :
  (theta omega : V.Vector3) →
  Audit.m12 (angularStrain theta omega)
  ≡ Audit.m21 (angularStrain theta omega)
angularStrainSymmetric12
  (V.v3 tx ty tz) (V.v3 wx wy wz) =
  solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ [])

angularStrainSymmetric13 :
  (theta omega : V.Vector3) →
  Audit.m13 (angularStrain theta omega)
  ≡ Audit.m31 (angularStrain theta omega)
angularStrainSymmetric13
  (V.v3 tx ty tz) (V.v3 wx wy wz) =
  solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ [])

angularStrainSymmetric23 :
  (theta omega : V.Vector3) →
  Audit.m23 (angularStrain theta omega)
  ≡ Audit.m32 (angularStrain theta omega)
angularStrainSymmetric23
  (V.v3 tx ty tz) (V.v3 wx wy wz) =
  solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ [])

trace : Audit.Matrix3 → ℚ
trace matrix =
  Audit.m11 matrix + Audit.m22 matrix + Audit.m33 matrix

angularStrainTraceFree :
  (theta omega : V.Vector3) →
  trace (angularStrain theta omega) ≡ 0ℚ
angularStrainTraceFree theta omega =
  begin
    trace (angularStrain theta omega)
  ≡⟨ traceMeaning theta omega ⟩
    (- 1ℚ) * V.dot theta (BS.cross theta omega)
  ≡⟨ cong ((- 1ℚ) *_)
       (BS.crossOrthogonalLeft theta omega) ⟩
    (- 1ℚ) * 0ℚ
  ≡⟨ solve [] ⟩
    0ℚ
  ∎
  where
  traceMeaning :
    (theta omega : V.Vector3) →
    trace (angularStrain theta omega)
    ≡ (- 1ℚ) * V.dot theta (BS.cross theta omega)
  traceMeaning
    (V.v3 tx ty tz) (V.v3 wx wy wz) =
    solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ [])

apply : Audit.Matrix3 → V.Vector3 → V.Vector3
apply matrix (V.v3 vx vy vz) =
  V.v3
    (Audit.m11 matrix * vx + Audit.m12 matrix * vy + Audit.m13 matrix * vz)
    (Audit.m21 matrix * vx + Audit.m22 matrix * vy + Audit.m23 matrix * vz)
    (Audit.m31 matrix * vx + Audit.m32 matrix * vy + Audit.m33 matrix * vz)

angularStrainActionFormula :
  (theta omega value : V.Vector3) →
  apply (angularStrain theta omega) value
  ≡ V.scale minusHalf
      (V.add
        (V.scale (V.dot (BS.cross theta omega) value) theta)
        (V.scale (V.dot theta value) (BS.cross theta omega)))
angularStrainActionFormula
  (V.v3 tx ty tz)
  (V.v3 wx wy wz)
  (V.v3 vx vy vz) =
  V.vectorExt
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ vx ∷ vy ∷ vz ∷ minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ vx ∷ vy ∷ vz ∷ minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ vx ∷ vy ∷ vz ∷ minusHalf ∷ []))

singleModeStretchingVanishes :
  (theta omega : V.Vector3) →
  V.dot theta omega ≡ 0ℚ →
  apply (angularStrain theta omega) omega
  ≡ V.v3 0ℚ 0ℚ 0ℚ
singleModeStretchingVanishes theta omega transverse =
  begin
    apply (angularStrain theta omega) omega
  ≡⟨ angularStrainActionFormula theta omega omega ⟩
    V.scale minusHalf
      (V.add
        (V.scale (V.dot (BS.cross theta omega) omega) theta)
        (V.scale (V.dot theta omega) (BS.cross theta omega)))
  ≡⟨ cong
       (λ rightPairing →
         V.scale minusHalf
           (V.add
             (V.scale rightPairing theta)
             (V.scale (V.dot theta omega) (BS.cross theta omega))))
       (BS.crossOrthogonalRight theta omega) ⟩
    V.scale minusHalf
      (V.add
        (V.scale 0ℚ theta)
        (V.scale (V.dot theta omega) (BS.cross theta omega)))
  ≡⟨ cong
       (λ leftPairing →
         V.scale minusHalf
           (V.add
             (V.scale 0ℚ theta)
             (V.scale leftPairing (BS.cross theta omega))))
       transverse ⟩
    V.scale minusHalf
      (V.add
        (V.scale 0ℚ theta)
        (V.scale 0ℚ (BS.cross theta omega)))
  ≡⟨ zeroCoordinates theta omega ⟩
    V.v3 0ℚ 0ℚ 0ℚ
  ∎
  where
  zeroCoordinates :
    (theta omega : V.Vector3) →
    V.scale minusHalf
      (V.add
        (V.scale 0ℚ theta)
        (V.scale 0ℚ (BS.cross theta omega)))
    ≡ V.v3 0ℚ 0ℚ 0ℚ
  zeroCoordinates
    (V.v3 tx ty tz) (V.v3 wx wy wz) =
    V.vectorExt
      (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ []))
      (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ []))
      (solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ minusHalf ∷ []))

basisTheta basisOmega : V.Vector3
basisTheta = V.v3 1ℚ 0ℚ 0ℚ
basisOmega = V.v3 0ℚ 1ℚ 0ℚ

basisSymbol : Audit.Matrix3
basisSymbol =
  Audit.matrix3
    0ℚ 0ℚ minusHalf
    0ℚ 0ℚ 0ℚ
    minusHalf 0ℚ 0ℚ

basisSymbolMeaning :
  angularStrain basisTheta basisOmega ≡ basisSymbol
basisSymbolMeaning =
  Audit.matrixExt
    (solve []) (solve []) (solve [])
    (solve []) (solve []) (solve [])
    (solve []) (solve []) (solve [])

minusHalfNotZero : minusHalf ≢ 0ℚ
minusHalfNotZero ()

basisSymbolNonzero :
  angularStrain basisTheta basisOmega ≢ Audit.zeroMatrix
basisSymbolNonzero equality =
  minusHalfNotZero
    (trans
      (cong Audit.m13 equality)
      refl)

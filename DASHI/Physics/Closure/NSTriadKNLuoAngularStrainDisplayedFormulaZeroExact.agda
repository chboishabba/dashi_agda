module DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Torah Sanni.
-- Title: "A Topological Obstruction to Persistent Vorticity Alignment via
-- the Angular Strain Symbol".
-- protocols.io preprint/protocol, version 1, 2025.
-- DOI: 10.17504/protocols.io.j8nlk15m5g5r/v1.
--
-- PURPOSE
-- Audit Definition 2.1 exactly as displayed before importing its topological
-- conclusion.  Its repeated-index core is
--
--   c_i(theta) = epsilon_{ikl} theta_k theta_l.
--
-- This is theta cross theta and therefore vanishes identically.  Consequently
-- both the matrix printed in the protocol,
--
--   M_ij(theta) = 1/2 (c_i(theta)+c_j(theta)) theta_i,
--
-- and the natural symmetric repair
--
--   1/2 (c_i(theta) theta_j + theta_i c_j(theta))
--
-- are the zero matrix for every direction.  The displayed definition has no
-- distinguished maximal eigenline and cannot instantiate the claimed
-- non-orientable maximal-eigenline bundle without a nontrivial corrected
-- symbol.
--
-- This theorem concerns the cited displayed formula.  It does not assert that
-- every possible angular strain symbol is zero; a corrected formula containing
-- the intended additional vector/index would need a fresh derivation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
import Data.Integer.Base as Int

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

record Matrix3 : Set where
  constructor matrix3
  field
    m11 m12 m13 : ℚ
    m21 m22 m23 : ℚ
    m31 m32 m33 : ℚ

open Matrix3 public

matrixExt :
  ∀ {a b : Matrix3} →
  m11 a ≡ m11 b → m12 a ≡ m12 b → m13 a ≡ m13 b →
  m21 a ≡ m21 b → m22 a ≡ m22 b → m23 a ≡ m23 b →
  m31 a ≡ m31 b → m32 a ≡ m32 b → m33 a ≡ m33 b →
  a ≡ b
matrixExt {matrix3 a11 a12 a13 a21 a22 a23 a31 a32 a33}
          {matrix3 .a11 .a12 .a13 .a21 .a22 .a23 .a31 .a32 .a33}
          refl refl refl refl refl refl refl refl refl = refl

zeroMatrix : Matrix3
zeroMatrix = matrix3 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

leviCivitaSelfContraction : V.Vector3 → V.Vector3
leviCivitaSelfContraction (V.v3 tx ty tz) =
  V.v3
    (ty * tz - tz * ty)
    (tz * tx - tx * tz)
    (tx * ty - ty * tx)

leviCivitaSelfContractionZero :
  (theta : V.Vector3) →
  leviCivitaSelfContraction theta ≡ V.v3 0ℚ 0ℚ 0ℚ
leviCivitaSelfContractionZero (V.v3 tx ty tz) =
  V.vectorExt
    (solve (ty ∷ tz ∷ []))
    (solve (tz ∷ tx ∷ []))
    (solve (tx ∷ ty ∷ []))

half : ℚ
half = Int.+ 1 / 2

-- Literal transcription of the displayed Definition 2.1:
-- M_ij = 1/2 (c_i+c_j) theta_i.
displayedFormulaSymbol : V.Vector3 → Matrix3
displayedFormulaSymbol theta =
  let
    core = leviCivitaSelfContraction theta
  in
  matrix3
    (half * (V.x core + V.x core) * V.x theta)
    (half * (V.x core + V.y core) * V.x theta)
    (half * (V.x core + V.z core) * V.x theta)
    (half * (V.y core + V.x core) * V.y theta)
    (half * (V.y core + V.y core) * V.y theta)
    (half * (V.y core + V.z core) * V.y theta)
    (half * (V.z core + V.x core) * V.z theta)
    (half * (V.z core + V.y core) * V.z theta)
    (half * (V.z core + V.z core) * V.z theta)

displayedFormulaSymbolZero :
  (theta : V.Vector3) →
  displayedFormulaSymbol theta ≡ zeroMatrix
displayedFormulaSymbolZero (V.v3 tx ty tz) =
  matrixExt
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))

-- The most obvious symmetric repair still uses the same zero core.
naturalSymmetrizedSymbol : V.Vector3 → Matrix3
naturalSymmetrizedSymbol theta =
  let
    core = leviCivitaSelfContraction theta
  in
  matrix3
    (half * (V.x core * V.x theta + V.x theta * V.x core))
    (half * (V.x core * V.y theta + V.x theta * V.y core))
    (half * (V.x core * V.z theta + V.x theta * V.z core))
    (half * (V.y core * V.x theta + V.y theta * V.x core))
    (half * (V.y core * V.y theta + V.y theta * V.y core))
    (half * (V.y core * V.z theta + V.y theta * V.z core))
    (half * (V.z core * V.x theta + V.z theta * V.x core))
    (half * (V.z core * V.y theta + V.z theta * V.y core))
    (half * (V.z core * V.z theta + V.z theta * V.z core))

naturalSymmetrizedSymbolZero :
  (theta : V.Vector3) →
  naturalSymmetrizedSymbol theta ≡ zeroMatrix
naturalSymmetrizedSymbolZero (V.v3 tx ty tz) =
  matrixExt
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ []))

module DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixSymbolRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 68 / ACTUAL COMPACT ANNULAR MATRIX SYMBOL
--
-- Compose the explicit compact scalar cutoff from the previous Round68 file
-- with the already-derived physical Fourier strain multiplier on the same
-- rational ProjectionMode carrier:
--
--   M(k,omega) = phi(|k|^2) Strain(k,omega).
--
-- Unlike the old Round48 scale-invariant "annular cutoff" interface, phi is
-- genuinely non-homogeneous and compact in the squared-radius variable.  The
-- homogeneous degree-zero property remains where it belongs: in Strain.
--
-- Exact support and plateau consequences:
--
--   |k|^2 <= 1  -> M=0,
--   |k|^2 >= 4  -> M=0,
--   2 <= |k|^2 <= 3 -> M=Strain(k,omega).
--
-- Thus E1 now has a concrete same-carrier compact annular matrix object.  What
-- remains analytically is the continuum C4 chain rule/derivative mass and the
-- fourfold inverse-Fourier integration by parts, not construction of a symbol.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (0ℚ; 1ℚ; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularScalarCutoffRound68Exact as Cutoff

compactAnnularMatrixSymbol :
  V.ProjectionMode → V.Vector3 → Matrix.Matrix3
compactAnnularMatrixSymbol modeData omega =
  Strain.scaleMatrix
    (Cutoff.compactAnnularScalarCutoff (V.normSquared (V.mode modeData)))
    (Strain.fourierStrainMultiplier modeData omega)

scaleZeroMatrix : ∀ matrix →
  Strain.scaleMatrix 0ℚ matrix ≡ Matrix.zeroMatrix
scaleZeroMatrix
    (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33) =
  Matrix.matrixExt
    (solve (m11 ∷ [])) (solve (m12 ∷ [])) (solve (m13 ∷ []))
    (solve (m21 ∷ [])) (solve (m22 ∷ [])) (solve (m23 ∷ []))
    (solve (m31 ∷ [])) (solve (m32 ∷ [])) (solve (m33 ∷ []))

scaleIdentityMatrix : ∀ matrix →
  Strain.scaleMatrix 1ℚ matrix ≡ matrix
scaleIdentityMatrix
    (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33) =
  Matrix.matrixExt
    (solve (m11 ∷ [])) (solve (m12 ∷ [])) (solve (m13 ∷ []))
    (solve (m21 ∷ [])) (solve (m22 ∷ [])) (solve (m23 ∷ []))
    (solve (m31 ∷ [])) (solve (m32 ∷ [])) (solve (m33 ∷ []))

compactAnnularMatrixBelowInnerSupport :
  ∀ modeData omega →
  V.normSquared (V.mode modeData) ≤ 1ℚ →
  compactAnnularMatrixSymbol modeData omega ≡ Matrix.zeroMatrix
compactAnnularMatrixBelowInnerSupport modeData omega norm≤1 =
  trans
    (cong
      (λ weight → Strain.scaleMatrix weight
        (Strain.fourierStrainMultiplier modeData omega))
      (Cutoff.compactAnnularCutoffBelowInnerSupport norm≤1))
    (scaleZeroMatrix (Strain.fourierStrainMultiplier modeData omega))

compactAnnularMatrixAboveOuterSupport :
  ∀ modeData omega →
  Cutoff.four ≤ V.normSquared (V.mode modeData) →
  compactAnnularMatrixSymbol modeData omega ≡ Matrix.zeroMatrix
compactAnnularMatrixAboveOuterSupport modeData omega four≤norm =
  trans
    (cong
      (λ weight → Strain.scaleMatrix weight
        (Strain.fourierStrainMultiplier modeData omega))
      (Cutoff.compactAnnularCutoffAboveOuterSupport four≤norm))
    (scaleZeroMatrix (Strain.fourierStrainMultiplier modeData omega))

compactAnnularMatrixOnPlateau :
  ∀ modeData omega →
  Cutoff.two ≤ V.normSquared (V.mode modeData) →
  V.normSquared (V.mode modeData) ≤ Cutoff.three →
  compactAnnularMatrixSymbol modeData omega
  ≡ Strain.fourierStrainMultiplier modeData omega
compactAnnularMatrixOnPlateau modeData omega two≤norm norm≤three =
  trans
    (cong
      (λ weight → Strain.scaleMatrix weight
        (Strain.fourierStrainMultiplier modeData omega))
      (Cutoff.compactAnnularCutoffPlateau two≤norm norm≤three))
    (scaleIdentityMatrix (Strain.fourierStrainMultiplier modeData omega))

round68ConcreteCompactAnnularMatrixSymbolConstructed : Bool
round68ConcreteCompactAnnularMatrixSymbolConstructed = true

round68ConcreteCompactAnnularMatrixSymbolConstructedIsTrue :
  round68ConcreteCompactAnnularMatrixSymbolConstructed ≡ true
round68ConcreteCompactAnnularMatrixSymbolConstructedIsTrue = refl

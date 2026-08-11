module DASHI.Physics.Closure.NSTriadKNFourierStrainScaleInvariantRound40Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 38 derived the exact nonzero strain multiplier
--
--   S_k = |k|^{-2} S_ang(k).
--
-- The shell-localized kernel argument in Round 40 needs the standard fact that
-- this is an order-zero angular multiplier.  Here that homogeneity is proved
-- exactly on the repository's rational projection-mode carrier.
--
-- A positive rational scale r carries an exact inverse r^{-1}.  Scaling
--
--   k -> r k,
--   |k|^{-2} -> |k|^{-2} r^{-2}
--
-- preserves the projection-mode inverse law.  The angular symbol scales by
-- r^2, so the two factors cancel and
--
--   S_{r k}(omega) = S_k(omega).
--
-- This removes the homogeneity clause from the remaining imported annular
-- kernel theorem: only smooth annular localization, Euclidean L1 integrability
-- of the master kernel, and periodization remain analytic authorities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_) 
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

normSquaredScale : ∀ scalar value →
  V.normSquared (V.scale scalar value)
  ≡ scalar * scalar * V.normSquared value
normSquaredScale scalar (V.v3 x y z) =
  solve (scalar ∷ x ∷ y ∷ z ∷ [])

scaledProjectionMode :
  Threshold.PositiveThreshold → V.ProjectionMode → V.ProjectionMode
scaledProjectionMode scale modeData =
  V.projection-mode
    (V.scale (Threshold.threshold scale) (V.mode modeData))
    (V.inverseNormSquared modeData
      * Threshold.thresholdInverse scale
      * Threshold.thresholdInverse scale)
    inverseScaled
  where
  r = Threshold.threshold scale
  rinv = Threshold.thresholdInverse scale
  inv = V.inverseNormSquared modeData
  n2 = V.normSquared (V.mode modeData)

  inverseScaled :
    (inv * rinv * rinv)
      * V.normSquared (V.scale r (V.mode modeData))
    ≡ 1ℚ
  inverseScaled
    rewrite normSquaredScale r (V.mode modeData)
          | V.inverseLaw modeData
          | Threshold.inverseMeaning scale =
    solve []

scaledProjectionModeMode : ∀ scale modeData →
  V.mode (scaledProjectionMode scale modeData)
  ≡ V.scale (Threshold.threshold scale) (V.mode modeData)
scaledProjectionModeMode scale modeData = refl

scaledProjectionModeInverse : ∀ scale modeData →
  V.inverseNormSquared (scaledProjectionMode scale modeData)
  ≡ V.inverseNormSquared modeData
      * Threshold.thresholdInverse scale
      * Threshold.thresholdInverse scale
scaledProjectionModeInverse scale modeData = refl

angularStrainScaleMode : ∀ scalar theta omega →
  Angular.angularStrain (V.scale scalar theta) omega
  ≡ Strain.scaleMatrix (scalar * scalar)
      (Angular.angularStrain theta omega)
angularStrainScaleMode scalar
    (V.v3 tx ty tz) (V.v3 wx wy wz) =
  Matrix.matrixExt
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (scalar ∷ tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))

scaleMatrixCompose : ∀ left right matrix →
  Strain.scaleMatrix left (Strain.scaleMatrix right matrix)
  ≡ Strain.scaleMatrix (left * right) matrix
scaleMatrixCompose left right
    (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33) =
  Matrix.matrixExt
    (solve (left ∷ right ∷ m11 ∷ []))
    (solve (left ∷ right ∷ m12 ∷ []))
    (solve (left ∷ right ∷ m13 ∷ []))
    (solve (left ∷ right ∷ m21 ∷ []))
    (solve (left ∷ right ∷ m22 ∷ []))
    (solve (left ∷ right ∷ m23 ∷ []))
    (solve (left ∷ right ∷ m31 ∷ []))
    (solve (left ∷ right ∷ m32 ∷ []))
    (solve (left ∷ right ∷ m33 ∷ []))

scaledAngularCancellation :
  ∀ scale modeData omega →
  Strain.scaleMatrix
    (V.inverseNormSquared (scaledProjectionMode scale modeData))
    (Angular.angularStrain
      (V.mode (scaledProjectionMode scale modeData)) omega)
  ≡
  Strain.scaleMatrix
    (V.inverseNormSquared modeData)
    (Angular.angularStrain (V.mode modeData) omega)
scaledAngularCancellation scale modeData omega =
  let
    r = Threshold.threshold scale
    rinv = Threshold.thresholdInverse scale
    inv = V.inverseNormSquared modeData
    angular = Angular.angularStrain (V.mode modeData) omega
  in
  trans
    (cong
      (Strain.scaleMatrix
        (inv * rinv * rinv))
      (angularStrainScaleMode r (V.mode modeData) omega))
    (trans
      (scaleMatrixCompose (inv * rinv * rinv) (r * r) angular)
      (matrixScalarCancellation scale inv angular))
  where
  matrixScalarCancellation :
    ∀ scale inv matrix →
    Strain.scaleMatrix
      ((inv * Threshold.thresholdInverse scale
        * Threshold.thresholdInverse scale)
        * (Threshold.threshold scale * Threshold.threshold scale))
      matrix
    ≡ Strain.scaleMatrix inv matrix
  matrixScalarCancellation scale inv
      (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33)
    rewrite Threshold.inverseMeaning scale =
    Matrix.matrixExt
      (solve (inv ∷ m11 ∷ []))
      (solve (inv ∷ m12 ∷ []))
      (solve (inv ∷ m13 ∷ []))
      (solve (inv ∷ m21 ∷ []))
      (solve (inv ∷ m22 ∷ []))
      (solve (inv ∷ m23 ∷ []))
      (solve (inv ∷ m31 ∷ []))
      (solve (inv ∷ m32 ∷ []))
      (solve (inv ∷ m33 ∷ []))

fourierStrainMultiplierScaleInvariant :
  ∀ scale modeData omega →
  Strain.fourierStrainMultiplier (scaledProjectionMode scale modeData) omega
  ≡ Strain.fourierStrainMultiplier modeData omega
fourierStrainMultiplierScaleInvariant scale modeData omega =
  trans
    (Strain.fourierStrainMultiplierExact
      (scaledProjectionMode scale modeData) omega)
    (trans
      (scaledAngularCancellation scale modeData omega)
      (sym (Strain.fourierStrainMultiplierExact modeData omega)))

fourierStrainOrderZeroHomogeneityClosed : Bool
fourierStrainOrderZeroHomogeneityClosed = true

fourierStrainOrderZeroHomogeneityClosedIsTrue :
  fourierStrainOrderZeroHomogeneityClosed ≡ true
fourierStrainOrderZeroHomogeneityClosedIsTrue = refl

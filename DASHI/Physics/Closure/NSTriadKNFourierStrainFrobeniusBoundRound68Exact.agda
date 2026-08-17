module DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew Majda.
-- Title: "Remarks on the Breakdown of Smooth Solutions for the 3-D Euler
-- Equations".
-- DOI: 10.1007/BF01240221.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- ROUND 68 / SCALE-FREE PHYSICAL STRAIN NORM
--
-- For a = theta cross omega, the angular strain numerator is
--
--   A = -1/2 (theta tensor a + a tensor theta).
--
-- Because theta.a=0, direct component expansion gives
--
--   ||A||_F^2 = (1/2) |theta|^2 |a|^2.
--
-- Lagrange's identity gives |a|^2 <= |theta|^2 |omega|^2.  Multiplying by
-- the physical inverse-square factor twice and using inv*|theta|^2=1 yields
--
--   ||Strain_theta(omega)||_F^2 <= (1/2) |omega|^2.
--
-- This is an exact rational, scale-free matrix bound on the actual physical
-- multiplier.  It is a genuine normalization input for the B/Gram lane and a
-- uniform amplitude input for the compact annular E multiplier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

half : ℚ
half = Int.+ 1 / 2

frobeniusSquared : Matrix.Matrix3 → ℚ
frobeniusSquared matrix =
    L2.square (Matrix.m11 matrix)
  + L2.square (Matrix.m12 matrix)
  + L2.square (Matrix.m13 matrix)
  + L2.square (Matrix.m21 matrix)
  + L2.square (Matrix.m22 matrix)
  + L2.square (Matrix.m23 matrix)
  + L2.square (Matrix.m31 matrix)
  + L2.square (Matrix.m32 matrix)
  + L2.square (Matrix.m33 matrix)

frobeniusSquaredScale : ∀ scalar matrix →
  frobeniusSquared (Strain.scaleMatrix scalar matrix)
  ≡ L2.square scalar * frobeniusSquared matrix
frobeniusSquaredScale scalar
    (Matrix.matrix3 m11 m12 m13 m21 m22 m23 m31 m32 m33) =
  solve
    (scalar ∷ m11 ∷ m12 ∷ m13 ∷ m21 ∷ m22 ∷ m23
      ∷ m31 ∷ m32 ∷ m33 ∷ [])

angularStrainFrobeniusExact : ∀ theta omega →
  frobeniusSquared (Angular.angularStrain theta omega)
  ≡ half * V.normSquared theta * V.normSquared (BS.cross theta omega)
angularStrainFrobeniusExact
    (V.v3 tx ty tz) (V.v3 wx wy wz) =
  solve (tx ∷ ty ∷ tz ∷ wx ∷ wy ∷ wz ∷ [])

crossNormBelowProduct : ∀ theta omega →
  V.normSquared (BS.cross theta omega)
  ≤ V.normSquared theta * V.normSquared omega
crossNormBelowProduct theta omega =
  let
    dotSquareNN = L2.squareNonnegative (V.dot theta omega)
    lagrange = BS.crossNormLagrange theta omega
    subtractBelow :
      V.normSquared theta * V.normSquared omega
        - L2.square (V.dot theta omega)
      ≤ V.normSquared theta * V.normSquared omega
    subtractBelow =
      L2.subtractNonnegativeBelow
        (V.normSquared theta * V.normSquared omega)
        (L2.square (V.dot theta omega)) dotSquareNN
  in
  subst
    (λ left → left ≤ V.normSquared theta * V.normSquared omega)
    (sym lagrange)
    subtractBelow

normSquaredNonnegative : ∀ value → 0ℚ ≤ V.normSquared value
normSquaredNonnegative (V.v3 x y z) =
  L2.addNonnegative
    (L2.squareNonnegative x)
    (L2.addNonnegative (L2.squareNonnegative y) (L2.squareNonnegative z))

halfNonnegative : 0ℚ ≤ half
halfNonnegative =
  let
    open import Relation.Nullary.Decidable.Core using (toWitness)
    open ℚP using (_≤?_)
  in toWitness {a? = 0ℚ ≤? half} _

angularStrainFrobeniusBound : ∀ theta omega →
  frobeniusSquared (Angular.angularStrain theta omega)
  ≤ half * V.normSquared theta *
      (V.normSquared theta * V.normSquared omega)
angularStrainFrobeniusBound theta omega =
  let
    thetaNN = normSquaredNonnegative theta
    halfThetaNN : 0ℚ ≤ half * V.normSquared theta
    halfThetaNN =
      let instance
        halfNNI = nonNegative halfNonnegative
        thetaNNI = nonNegative thetaNN
        productNNI = ℚP.nonNeg*nonNeg⇒nonNeg half (V.normSquared theta)
      in ℚP.nonNegative⁻¹ (half * V.normSquared theta)
    scaled =
      let instance factorNNI = nonNegative halfThetaNN
      in ℚP.*-monoˡ-≤-nonNeg
        (half * V.normSquared theta)
        (crossNormBelowProduct theta omega)
  in
  subst
    (λ left → left ≤ half * V.normSquared theta *
      (V.normSquared theta * V.normSquared omega))
    (sym (angularStrainFrobeniusExact theta omega))
    scaled

physicalStrainFrobeniusBound : ∀ modeData omega →
  frobeniusSquared (Strain.fourierStrainMultiplier modeData omega)
  ≤ half * V.normSquared omega
physicalStrainFrobeniusBound modeData omega =
  let
    inv = V.inverseNormSquared modeData
    norm = V.normSquared (V.mode modeData)
    omegaNorm = V.normSquared omega
    angular = Angular.angularStrain (V.mode modeData) omega

    scaledMeaning :
      frobeniusSquared (Strain.fourierStrainMultiplier modeData omega)
      ≡ L2.square inv * frobeniusSquared angular
    scaledMeaning = trans
      (cong frobeniusSquared
        (Strain.fourierStrainMultiplierExact modeData omega))
      (frobeniusSquaredScale inv angular)

    angularBound = angularStrainFrobeniusBound (V.mode modeData) omega
    invSquareNN = L2.squareNonnegative inv
    scaledBound :
      L2.square inv * frobeniusSquared angular
      ≤ L2.square inv * (half * norm * (norm * omegaNorm))
    scaledBound =
      let instance invNNI = nonNegative invSquareNN
      in ℚP.*-monoˡ-≤-nonNeg (L2.square inv) angularBound

    endpoint :
      L2.square inv * (half * norm * (norm * omegaNorm))
      ≡ half * omegaNorm
    endpoint = trans
      (solve (inv ∷ norm ∷ half ∷ omegaNorm ∷ []))
      (trans
        (cong (λ law → half * law * law * omegaNorm)
          (V.inverseLaw modeData))
        (solve (half ∷ omegaNorm ∷ [])))
  in
  subst (λ left → left ≤ half * omegaNorm) (sym scaledMeaning)
    (subst
      (λ right → L2.square inv * frobeniusSquared angular ≤ right)
      endpoint scaledBound)

round68PhysicalStrainFrobeniusBoundOneHalf : Bool
round68PhysicalStrainFrobeniusBoundOneHalf = true

round68PhysicalStrainFrobeniusBoundOneHalfIsTrue :
  round68PhysicalStrainFrobeniusBoundOneHalf ≡ true
round68PhysicalStrainFrobeniusBoundOneHalfIsTrue = refl

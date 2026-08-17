module DASHI.Physics.Closure.NSTriadKNFourierStrainExactFiniteDifferenceRound68Exact where

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
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND 68 / EXACT MULTIPLIER DIFFERENCE
--
-- Round67 supplied an explicit C4 radial transition and an exact h^2 Taylor
-- factor for that cutoff.  The other part of the physical annular multiplier
-- is the order-zero Fourier strain symbol
--
--   S(theta,omega) = |theta|^{-2} A(theta,omega),
--
-- with A quadratic in theta.  This file differentiates that object without
-- importing an abstract multivariable calculus theorem.
--
-- First, the angular numerator has the exact polarization identity
--
--   A(theta+h)-A(theta) = L_theta(h) + A(h),
--
-- where L is bilinear in theta,h and A(h) is the literal quadratic remainder.
-- Second, for two exact ProjectionModes x,y,
--
--   inv(y)-inv(x)
--     = inv(x) inv(y) (|x|^2-|y|^2).
--
-- When y=x+h this becomes
--
--   inv(y)-inv(x)
--     = - inv(x) inv(y) (2 x.h + |h|^2).
--
-- Combining the two gives an exact finite-difference decomposition of the
-- physical strain multiplier.  The remaining six-three work is therefore
-- quantitative estimation of explicit linear/quadratic terms; there is no
-- longer an opaque angular differentiability premise.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

matrixAdd : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixAdd a b = Matrix.matrix3
  (Matrix.m11 a + Matrix.m11 b)
  (Matrix.m12 a + Matrix.m12 b)
  (Matrix.m13 a + Matrix.m13 b)
  (Matrix.m21 a + Matrix.m21 b)
  (Matrix.m22 a + Matrix.m22 b)
  (Matrix.m23 a + Matrix.m23 b)
  (Matrix.m31 a + Matrix.m31 b)
  (Matrix.m32 a + Matrix.m32 b)
  (Matrix.m33 a + Matrix.m33 b)

matrixNegate : Matrix.Matrix3 → Matrix.Matrix3
matrixNegate a = Strain.scaleMatrix (- (1ℚ)) a
  where
  open import Data.Rational.Base using (1ℚ)

matrixSubtract : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixSubtract a b = matrixAdd a (matrixNegate b)

-- The part of the quadratic angular symbol which is linear in the increment.
angularLinearVariation : V.Vector3 → V.Vector3 → V.Vector3 → Matrix.Matrix3
angularLinearVariation theta h omega =
  let
    thetaCross = BS.cross theta omega
    hCross = BS.cross h omega
    mh = Angular.minusHalf
  in
  Matrix.matrix3
    (mh * (V.x theta * V.x hCross + V.x hCross * V.x theta
         + V.x h * V.x thetaCross + V.x thetaCross * V.x h))
    (mh * (V.x theta * V.y hCross + V.x hCross * V.y theta
         + V.x h * V.y thetaCross + V.x thetaCross * V.y h))
    (mh * (V.x theta * V.z hCross + V.x hCross * V.z theta
         + V.x h * V.z thetaCross + V.x thetaCross * V.z h))
    (mh * (V.y theta * V.x hCross + V.y hCross * V.x theta
         + V.y h * V.x thetaCross + V.y thetaCross * V.x h))
    (mh * (V.y theta * V.y hCross + V.y hCross * V.y theta
         + V.y h * V.y thetaCross + V.y thetaCross * V.y h))
    (mh * (V.y theta * V.z hCross + V.y hCross * V.z theta
         + V.y h * V.z thetaCross + V.y thetaCross * V.z h))
    (mh * (V.z theta * V.x hCross + V.z hCross * V.x theta
         + V.z h * V.x thetaCross + V.z thetaCross * V.x h))
    (mh * (V.z theta * V.y hCross + V.z hCross * V.y theta
         + V.z h * V.y thetaCross + V.z thetaCross * V.y h))
    (mh * (V.z theta * V.z hCross + V.z hCross * V.z theta
         + V.z h * V.z thetaCross + V.z thetaCross * V.z h))

angularStrainExactPolarization : ∀ theta h omega →
  Angular.angularStrain (V.add theta h) omega
  ≡ matrixAdd
      (Angular.angularStrain theta omega)
      (matrixAdd
        (angularLinearVariation theta h omega)
        (Angular.angularStrain h omega))
angularStrainExactPolarization
    (V.v3 tx ty tz) (V.v3 hx hy hz) (V.v3 wx wy wz) =
  Matrix.matrixExt
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))
    (solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ wx ∷ wy ∷ wz ∷ Angular.minusHalf ∷ []))

inverseNormSquaredDifferenceExact : ∀ left right →
  V.inverseNormSquared right - V.inverseNormSquared left
  ≡ V.inverseNormSquared left * V.inverseNormSquared right
      * (V.normSquared (V.mode left) - V.normSquared (V.mode right))
inverseNormSquaredDifferenceExact left right =
  let
    il = V.inverseNormSquared left
    ir = V.inverseNormSquared right
    nl = V.normSquared (V.mode left)
    nr = V.normSquared (V.mode right)
  in
  trans
    (sym (solve (il ∷ ir ∷ nl ∷ nr ∷ [])))
    (trans
      (cong
        (λ pair → ir * pair - il * (V.inverseNormSquared right * nr))
        (V.inverseLaw left))
      (trans
        (cong
          (λ pair → ir * 1ℚ - il * pair)
          (V.inverseLaw right))
        (solve (il ∷ ir ∷ []))))
  where
  open import Data.Rational.Base using (1ℚ)

normSquaredIncrementExact : ∀ theta h →
  V.normSquared (V.add theta h)
  ≡ V.normSquared theta
      + (V.dot theta h + V.dot theta h)
      + V.normSquared h
normSquaredIncrementExact
    (V.v3 tx ty tz) (V.v3 hx hy hz) =
  solve (tx ∷ ty ∷ tz ∷ hx ∷ hy ∷ hz ∷ [])

inverseNormSquaredDisplacementExact : ∀ left right h →
  V.mode right ≡ V.add (V.mode left) h →
  V.inverseNormSquared right - V.inverseNormSquared left
  ≡ - (V.inverseNormSquared left * V.inverseNormSquared right)
      * ((V.dot (V.mode left) h + V.dot (V.mode left) h)
        + V.normSquared h)
inverseNormSquaredDisplacementExact left right h rightIsIncrement =
  let
    il = V.inverseNormSquared left
    ir = V.inverseNormSquared right
    theta = V.mode left
    base = inverseNormSquaredDifferenceExact left right
    normRight :
      V.normSquared (V.mode right)
      ≡ V.normSquared theta
          + (V.dot theta h + V.dot theta h)
          + V.normSquared h
    normRight = trans
      (cong V.normSquared rightIsIncrement)
      (normSquaredIncrementExact theta h)
  in
  trans base
    (trans
      (cong
        (λ selected → il * ir * (V.normSquared theta - selected))
        normRight)
      (solve
        (il ∷ ir ∷ V.normSquared theta ∷ V.dot theta h
          ∷ V.normSquared h ∷ [])))

scaleMatrixAdd : ∀ scalar a b →
  Strain.scaleMatrix scalar (matrixAdd a b)
  ≡ matrixAdd (Strain.scaleMatrix scalar a) (Strain.scaleMatrix scalar b)
scaleMatrixAdd scalar
    (Matrix.matrix3 a11 a12 a13 a21 a22 a23 a31 a32 a33)
    (Matrix.matrix3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  Matrix.matrixExt
    (solve (scalar ∷ a11 ∷ b11 ∷ []))
    (solve (scalar ∷ a12 ∷ b12 ∷ []))
    (solve (scalar ∷ a13 ∷ b13 ∷ []))
    (solve (scalar ∷ a21 ∷ b21 ∷ []))
    (solve (scalar ∷ a22 ∷ b22 ∷ []))
    (solve (scalar ∷ a23 ∷ b23 ∷ []))
    (solve (scalar ∷ a31 ∷ b31 ∷ []))
    (solve (scalar ∷ a32 ∷ b32 ∷ []))
    (solve (scalar ∷ a33 ∷ b33 ∷ []))

scaledAngularDifferenceDecomposition : ∀ il ir angularLeft angularRight →
  Strain.scaleMatrix ir angularRight
  ≡ matrixAdd
      (Strain.scaleMatrix il angularLeft)
      (matrixAdd
        (Strain.scaleMatrix ir (matrixSubtract angularRight angularLeft))
        (Strain.scaleMatrix (ir - il) angularLeft))
scaledAngularDifferenceDecomposition il ir
    (Matrix.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33)
    (Matrix.matrix3 r11 r12 r13 r21 r22 r23 r31 r32 r33) =
  Matrix.matrixExt
    (solve (il ∷ ir ∷ l11 ∷ r11 ∷ []))
    (solve (il ∷ ir ∷ l12 ∷ r12 ∷ []))
    (solve (il ∷ ir ∷ l13 ∷ r13 ∷ []))
    (solve (il ∷ ir ∷ l21 ∷ r21 ∷ []))
    (solve (il ∷ ir ∷ l22 ∷ r22 ∷ []))
    (solve (il ∷ ir ∷ l23 ∷ r23 ∷ []))
    (solve (il ∷ ir ∷ l31 ∷ r31 ∷ []))
    (solve (il ∷ ir ∷ l32 ∷ r32 ∷ []))
    (solve (il ∷ ir ∷ l33 ∷ r33 ∷ []))

-- Exact physical finite difference.  This form deliberately leaves the two
-- terms separate so quantitative consumers can estimate angular variation and
-- inverse-square variation with the branch geometry best suited to each.
fourierStrainFiniteDifferenceExact : ∀ left right h omega →
  V.mode right ≡ V.add (V.mode left) h →
  Strain.fourierStrainMultiplier right omega
  ≡ matrixAdd
      (Strain.fourierStrainMultiplier left omega)
      (matrixAdd
        (Strain.scaleMatrix
          (V.inverseNormSquared right)
          (matrixAdd
            (angularLinearVariation (V.mode left) h omega)
            (Angular.angularStrain h omega)))
        (Strain.scaleMatrix
          (V.inverseNormSquared right - V.inverseNormSquared left)
          (Angular.angularStrain (V.mode left) omega)))
fourierStrainFiniteDifferenceExact left right h omega rightIsIncrement =
  let
    angularIncrement :
      Angular.angularStrain (V.mode right) omega
      ≡ matrixAdd
          (Angular.angularStrain (V.mode left) omega)
          (matrixAdd
            (angularLinearVariation (V.mode left) h omega)
            (Angular.angularStrain h omega))
    angularIncrement = trans
      (cong (λ selected → Angular.angularStrain selected omega) rightIsIncrement)
      (angularStrainExactPolarization (V.mode left) h omega)
  in
  trans
    (Strain.fourierStrainMultiplierExact right omega)
    (trans
      (cong (Strain.scaleMatrix (V.inverseNormSquared right)) angularIncrement)
      (trans
        (scaleMatrixAdd
          (V.inverseNormSquared right)
          (Angular.angularStrain (V.mode left) omega)
          (matrixAdd
            (angularLinearVariation (V.mode left) h omega)
            (Angular.angularStrain h omega)))
        (trans
          (cong
            (matrixAdd
              (Strain.scaleMatrix (V.inverseNormSquared right)
                (Angular.angularStrain (V.mode left) omega)))
            (scaleMatrixAdd
              (V.inverseNormSquared right)
              (angularLinearVariation (V.mode left) h omega)
              (Angular.angularStrain h omega)))
          (trans
            (scaledAngularDifferenceDecomposition
              (V.inverseNormSquared left)
              (V.inverseNormSquared right)
              (Angular.angularStrain (V.mode left) omega)
              (matrixAdd
                (angularLinearVariation (V.mode left) h omega)
                (Angular.angularStrain h omega)))
            (cong
              (λ base → matrixAdd base
                (matrixAdd
                  (Strain.scaleMatrix
                    (V.inverseNormSquared right)
                    (matrixAdd
                      (angularLinearVariation (V.mode left) h omega)
                      (Angular.angularStrain h omega)))
                  (Strain.scaleMatrix
                    (V.inverseNormSquared right - V.inverseNormSquared left)
                    (Angular.angularStrain (V.mode left) omega))))
              (sym (Strain.fourierStrainMultiplierExact left omega))))))))

round68AngularMultiplierDifferentiatedAlgebraically : Bool
round68AngularMultiplierDifferentiatedAlgebraically = true

round68InverseSquareDifferenceConstructed : Bool
round68InverseSquareDifferenceConstructed = true

round68PhysicalStrainFiniteDifferenceConstructed : Bool
round68PhysicalStrainFiniteDifferenceConstructed = true

round68PhysicalStrainFiniteDifferenceConstructedIsTrue :
  round68PhysicalStrainFiniteDifferenceConstructed ≡ true
round68PhysicalStrainFiniteDifferenceConstructedIsTrue = refl

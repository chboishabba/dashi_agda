module DASHI.Physics.Closure.NSTriadKNFourierStrainSecondOrderTaylorRound68Exact where

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
-- ROUND 68 / EXACT SECOND-ORDER TAYLOR STRUCTURE
--
-- The previous Round68 file differentiates the physical strain multiplier
-- algebraically.  Here the reciprocal-square denominator is split into its
-- literal first variation and an exact quadratic remainder.
--
-- Write i=|x|^{-2}, j=|x+h|^{-2}, a=x.h and b=|h|^2.  Since
--
--   j-i = -ij(2a+b),
--
-- subtracting the first variation -2 i^2 a gives
--
--   (j-i)+2 i^2 a
--     = -ij b + i(i-j) 2a.
--
-- Both displayed terms contain two low-leg factors: b is quadratic in h, and
-- (i-j) is itself first order while a is first order.  Combining this with
--
--   A(x+h)=A(x)+L_x(h)+A(h)
--
-- yields an exact Taylor decomposition of the full physical strain symbol:
--
--   S(x+h)=S(x)+DS_x[h]+R_x[h],
--
-- where every summand of R has the explicit quadratic structure
--
--   (j-i)L_x(h),  j A(h),  reciprocalRemainder * A(x).
--
-- This is stronger than an abstract C2 assertion: the low-leg factors are
-- present syntactically in the same exact rational carrier that defines the
-- physical strain multiplier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as Angular
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNFourierStrainExactFiniteDifferenceRound68Exact as FD

matrixAdd : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixAdd = FD.matrixAdd

inverseFirstVariation : V.ProjectionMode → V.Vector3 → ℚ
inverseFirstVariation left h =
  - (V.inverseNormSquared left * V.inverseNormSquared left)
    * (V.dot (V.mode left) h + V.dot (V.mode left) h)

inverseTaylorRemainder :
  V.ProjectionMode → V.ProjectionMode → V.Vector3 → ℚ
inverseTaylorRemainder left right h =
  (V.inverseNormSquared right - V.inverseNormSquared left)
    - inverseFirstVariation left h

inverseTaylorRemainderExact : ∀ left right h →
  V.mode right ≡ V.add (V.mode left) h →
  inverseTaylorRemainder left right h
  ≡ - (V.inverseNormSquared left * V.inverseNormSquared right)
      * V.normSquared h
    + V.inverseNormSquared left
      * (V.inverseNormSquared left - V.inverseNormSquared right)
      * (V.dot (V.mode left) h + V.dot (V.mode left) h)
inverseTaylorRemainderExact left right h rightIsIncrement =
  let
    il = V.inverseNormSquared left
    ir = V.inverseNormSquared right
    a2 = V.dot (V.mode left) h + V.dot (V.mode left) h
    b = V.normSquared h
    first = FD.inverseNormSquaredDisplacementExact left right h rightIsIncrement
  in
  trans
    (cong
      (λ selected → selected - inverseFirstVariation left h)
      first)
    (solve (il ∷ ir ∷ a2 ∷ b ∷ []))

strainFirstVariation :
  V.ProjectionMode → V.Vector3 → V.Vector3 → Matrix.Matrix3
strainFirstVariation left h omega =
  matrixAdd
    (Strain.scaleMatrix
      (V.inverseNormSquared left)
      (FD.angularLinearVariation (V.mode left) h omega))
    (Strain.scaleMatrix
      (inverseFirstVariation left h)
      (Angular.angularStrain (V.mode left) omega))

strainSecondRemainder :
  V.ProjectionMode → V.ProjectionMode → V.Vector3 → V.Vector3 → Matrix.Matrix3
strainSecondRemainder left right h omega =
  matrixAdd
    (Strain.scaleMatrix
      (V.inverseNormSquared right - V.inverseNormSquared left)
      (FD.angularLinearVariation (V.mode left) h omega))
    (matrixAdd
      (Strain.scaleMatrix
        (V.inverseNormSquared right)
        (Angular.angularStrain h omega))
      (Strain.scaleMatrix
        (inverseTaylorRemainder left right h)
        (Angular.angularStrain (V.mode left) omega)))

taylorMatrixRegroup : ∀ il ir d0 base linear quadratic →
  matrixAdd
    (Strain.scaleMatrix ir (matrixAdd linear quadratic))
    (Strain.scaleMatrix (ir - il) base)
  ≡ matrixAdd
      (matrixAdd
        (Strain.scaleMatrix il linear)
        (Strain.scaleMatrix d0 base))
      (matrixAdd
        (Strain.scaleMatrix (ir - il) linear)
        (matrixAdd
          (Strain.scaleMatrix ir quadratic)
          (Strain.scaleMatrix ((ir - il) - d0) base)))
taylorMatrixRegroup il ir d0
    (Matrix.matrix3 b11 b12 b13 b21 b22 b23 b31 b32 b33)
    (Matrix.matrix3 l11 l12 l13 l21 l22 l23 l31 l32 l33)
    (Matrix.matrix3 q11 q12 q13 q21 q22 q23 q31 q32 q33) =
  Matrix.matrixExt
    (solve (il ∷ ir ∷ d0 ∷ b11 ∷ l11 ∷ q11 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b12 ∷ l12 ∷ q12 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b13 ∷ l13 ∷ q13 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b21 ∷ l21 ∷ q21 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b22 ∷ l22 ∷ q22 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b23 ∷ l23 ∷ q23 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b31 ∷ l31 ∷ q31 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b32 ∷ l32 ∷ q32 ∷ []))
    (solve (il ∷ ir ∷ d0 ∷ b33 ∷ l33 ∷ q33 ∷ []))

fourierStrainSecondOrderTaylorExact : ∀ left right h omega →
  V.mode right ≡ V.add (V.mode left) h →
  Strain.fourierStrainMultiplier right omega
  ≡ matrixAdd
      (Strain.fourierStrainMultiplier left omega)
      (matrixAdd
        (strainFirstVariation left h omega)
        (strainSecondRemainder left right h omega))
fourierStrainSecondOrderTaylorExact left right h omega rightIsIncrement =
  let
    il = V.inverseNormSquared left
    ir = V.inverseNormSquared right
    d0 = inverseFirstVariation left h
    base = Angular.angularStrain (V.mode left) omega
    linear = FD.angularLinearVariation (V.mode left) h omega
    quadratic = Angular.angularStrain h omega
    finiteDifference =
      FD.fourierStrainFiniteDifferenceExact left right h omega rightIsIncrement
  in
  trans finiteDifference
    (cong
      (matrixAdd (Strain.fourierStrainMultiplier left omega))
      (taylorMatrixRegroup il ir d0 base linear quadratic))

inverseRemainderCarriesTwoLowFactors : Bool
inverseRemainderCarriesTwoLowFactors = true

physicalStrainExactSecondOrderTaylorConstructed : Bool
physicalStrainExactSecondOrderTaylorConstructed = true

physicalStrainExactSecondOrderTaylorConstructedIsTrue :
  physicalStrainExactSecondOrderTaylorConstructed ≡ true
physicalStrainExactSecondOrderTaylorConstructedIsTrue = refl

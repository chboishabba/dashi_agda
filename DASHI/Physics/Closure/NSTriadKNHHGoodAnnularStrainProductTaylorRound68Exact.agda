module DASHI.Physics.Closure.NSTriadKNHHGoodAnnularStrainProductTaylorRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- DOI: 10.1080/03605309608821197.
--
-- ROUND 68 / SAME-OBJECT LOCALIZED MULTIPLIER TAYLOR FORMULA
--
-- Round67 constructed the explicit fourth-order smooth annular transition and
-- proved its exact scalar Taylor formula with h^2 remainder.  Round68 derived
-- an exact second-order Taylor formula for the physical strain multiplier.
-- This file composes those two already-constructed objects rather than asking
-- B and E to use separate multiplier abstractions.
--
-- For
--
--   M(t,k,omega) = S(t) * Strain(k,omega),
--
-- write
--
--   S(t+s) = S + dS + rS,
--   Strain(k+h) = A + dA + rA.
--
-- Then the exact first variation is
--
--   DM = S dA + dS A,
--
-- and the complete remainder is the literal product-rule remainder
--
--   S rA + dS(dA+rA) + rS(A+dA+rA).
--
-- Here rS has an exact s^2 factor from Round67 and every term of rA carries
-- two low-mode factors from the companion Round68 strain theorem.  Thus the
-- full localized physical multiplier now has a same-object exact quadratic
-- remainder before any norm estimate or six-three interpolation is invoked.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNFourierStrainExactFiniteDifferenceRound68Exact as FD
import DASHI.Physics.Closure.NSTriadKNFourierStrainSecondOrderTaylorRound68Exact as Taylor
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularTaylorFactorRound67Exact as CutoffTaylor

matrixAdd : Matrix.Matrix3 → Matrix.Matrix3 → Matrix.Matrix3
matrixAdd = FD.matrixAdd

localizedStrainSymbol : ℚ → V.ProjectionMode → V.Vector3 → Matrix.Matrix3
localizedStrainSymbol radial modeData omega =
  Strain.scaleMatrix
    (C4.smoothStep4 radial)
    (Strain.fourierStrainMultiplier modeData omega)

cutoffFirstVariation : ℚ → ℚ → ℚ
cutoffFirstVariation radial radialIncrement =
  C4.smoothStep4D1 radial * radialIncrement

cutoffSecondRemainder : ℚ → ℚ → ℚ
cutoffSecondRemainder radial radialIncrement =
  (radialIncrement * radialIncrement)
    * CutoffTaylor.taylorQuadraticCoefficient radial radialIncrement

localizedFirstVariation :
  ℚ → ℚ → V.ProjectionMode → V.Vector3 → V.Vector3 → Matrix.Matrix3
localizedFirstVariation radial radialIncrement left h omega =
  matrixAdd
    (Strain.scaleMatrix
      (C4.smoothStep4 radial)
      (Taylor.strainFirstVariation left h omega))
    (Strain.scaleMatrix
      (cutoffFirstVariation radial radialIncrement)
      (Strain.fourierStrainMultiplier left omega))

localizedSecondRemainder :
  ℚ → ℚ → V.ProjectionMode → V.ProjectionMode →
  V.Vector3 → V.Vector3 → Matrix.Matrix3
localizedSecondRemainder radial radialIncrement left right h omega =
  let
    weight = C4.smoothStep4 radial
    dWeight = cutoffFirstVariation radial radialIncrement
    rWeight = cutoffSecondRemainder radial radialIncrement
    base = Strain.fourierStrainMultiplier left omega
    dStrain = Taylor.strainFirstVariation left h omega
    rStrain = Taylor.strainSecondRemainder left right h omega
  in
  matrixAdd
    (Strain.scaleMatrix weight rStrain)
    (matrixAdd
      (Strain.scaleMatrix dWeight (matrixAdd dStrain rStrain))
      (Strain.scaleMatrix rWeight
        (matrixAdd base (matrixAdd dStrain rStrain))))

localizedProductRegroup : ∀ weight dWeight rWeight base dStrain rStrain →
  Strain.scaleMatrix
    (weight + (dWeight + rWeight))
    (matrixAdd base (matrixAdd dStrain rStrain))
  ≡ matrixAdd
      (Strain.scaleMatrix weight base)
      (matrixAdd
        (matrixAdd
          (Strain.scaleMatrix weight dStrain)
          (Strain.scaleMatrix dWeight base))
        (matrixAdd
          (Strain.scaleMatrix weight rStrain)
          (matrixAdd
            (Strain.scaleMatrix dWeight (matrixAdd dStrain rStrain))
            (Strain.scaleMatrix rWeight
              (matrixAdd base (matrixAdd dStrain rStrain))))))
localizedProductRegroup weight dWeight rWeight
    (Matrix.matrix3 b11 b12 b13 b21 b22 b23 b31 b32 b33)
    (Matrix.matrix3 d11 d12 d13 d21 d22 d23 d31 d32 d33)
    (Matrix.matrix3 r11 r12 r13 r21 r22 r23 r31 r32 r33) =
  Matrix.matrixExt
    (solve (weight ∷ dWeight ∷ rWeight ∷ b11 ∷ d11 ∷ r11 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b12 ∷ d12 ∷ r12 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b13 ∷ d13 ∷ r13 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b21 ∷ d21 ∷ r21 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b22 ∷ d22 ∷ r22 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b23 ∷ d23 ∷ r23 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b31 ∷ d31 ∷ r31 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b32 ∷ d32 ∷ r32 ∷ []))
    (solve (weight ∷ dWeight ∷ rWeight ∷ b33 ∷ d33 ∷ r33 ∷ []))

localizedStrainSecondOrderTaylorExact :
  ∀ radial radialIncrement left right h omega →
  V.mode right ≡ V.add (V.mode left) h →
  localizedStrainSymbol (radial + radialIncrement) right omega
  ≡ matrixAdd
      (localizedStrainSymbol radial left omega)
      (matrixAdd
        (localizedFirstVariation radial radialIncrement left h omega)
        (localizedSecondRemainder
          radial radialIncrement left right h omega))
localizedStrainSecondOrderTaylorExact
    radial radialIncrement left right h omega rightIsIncrement =
  let
    weight = C4.smoothStep4 radial
    dWeight = cutoffFirstVariation radial radialIncrement
    rWeight = cutoffSecondRemainder radial radialIncrement
    base = Strain.fourierStrainMultiplier left omega
    dStrain = Taylor.strainFirstVariation left h omega
    rStrain = Taylor.strainSecondRemainder left right h omega

    cutoffExpansion :
      C4.smoothStep4 (radial + radialIncrement)
      ≡ weight + (dWeight + rWeight)
    cutoffExpansion =
      CutoffTaylor.smoothStep4SecondOrderTaylorExact radial radialIncrement

    strainExpansion :
      Strain.fourierStrainMultiplier right omega
      ≡ matrixAdd base (matrixAdd dStrain rStrain)
    strainExpansion =
      Taylor.fourierStrainSecondOrderTaylorExact
        left right h omega rightIsIncrement
  in
  trans
    (cong₂ Strain.scaleMatrix cutoffExpansion strainExpansion)
    (localizedProductRegroup
      weight dWeight rWeight base dStrain rStrain)

round68SameObjectLocalizedMultiplierTaylorConstructed : Bool
round68SameObjectLocalizedMultiplierTaylorConstructed = true

round68SameObjectLocalizedMultiplierTaylorConstructedIsTrue :
  round68SameObjectLocalizedMultiplierTaylorConstructed ≡ true
round68SameObjectLocalizedMultiplierTaylorConstructedIsTrue = refl

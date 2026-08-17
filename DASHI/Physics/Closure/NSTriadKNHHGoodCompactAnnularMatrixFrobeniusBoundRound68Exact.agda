module DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixFrobeniusBoundRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND 68 / UNIFORM MASTER-SYMBOL AMPLITUDE
--
-- The concrete compact annular symbol is
--
--   M(k,omega) = phi(|k|^2) Strain_k(omega),
--
-- with 0<=phi<=1.  Round68 already proved
--
--   ||Strain_k(omega)||_F^2 <= (1/2)|omega|^2.
--
-- Hence the same physical master symbol satisfies exactly
--
--   ||M(k,omega)||_F^2 <= (1/2)|omega|^2.
--
-- This is the first uniform matrix-size theorem on the actual compact annular
-- E/B object, rather than on a surrogate cutoff or abstract kernel record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain
import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularScalarCutoffRound68Exact as Cutoff
import DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularMatrixSymbolRound68Exact as Symbol
import DASHI.Physics.Closure.NSTriadKNFourierStrainFrobeniusBoundRound68Exact as Frobenius

squareCutoffBelowOne : ∀ rho →
  L2.square (Cutoff.compactAnnularScalarCutoff rho) ≤ 1ℚ
squareCutoffBelowOne rho =
  let
    phi = Cutoff.compactAnnularScalarCutoff rho
    phiNN = Cutoff.compactAnnularCutoffNonnegative rho
    phi≤1 = Cutoff.compactAnnularCutoffBelowOne rho
    oneNN : 0ℚ ≤ 1ℚ
    oneNN = Cutoff.zeroBelowOne
    product = L2.nonnegativeProductMonotone
      phiNN phiNN oneNN oneNN phi≤1 phi≤1
  in
  subst (L2.square phi ≤_) (ℚP.*-identityˡ 1ℚ) product

frobeniusSquaredNonnegative : ∀ matrix →
  0ℚ ≤ Frobenius.frobeniusSquared matrix
frobeniusSquaredNonnegative matrix =
  L2.addNonnegative
    (L2.addNonnegative
      (L2.addNonnegative
        (L2.addNonnegative
          (L2.addNonnegative
            (L2.addNonnegative
              (L2.addNonnegative
                (L2.addNonnegative
                  (L2.squareNonnegative (Matrix.m11 matrix))
                  (L2.squareNonnegative (Matrix.m12 matrix)))
                (L2.squareNonnegative (Matrix.m13 matrix)))
              (L2.squareNonnegative (Matrix.m21 matrix)))
            (L2.squareNonnegative (Matrix.m22 matrix)))
          (L2.squareNonnegative (Matrix.m23 matrix)))
        (L2.squareNonnegative (Matrix.m31 matrix)))
      (L2.squareNonnegative (Matrix.m32 matrix)))
    (L2.squareNonnegative (Matrix.m33 matrix))

compactAnnularMatrixFrobeniusBelowPhysical : ∀ modeData omega →
  Frobenius.frobeniusSquared (Symbol.compactAnnularMatrixSymbol modeData omega)
  ≤ Frobenius.frobeniusSquared
      (Strain.fourierStrainMultiplier modeData omega)
compactAnnularMatrixFrobeniusBelowPhysical modeData omega =
  let
    phi = Cutoff.compactAnnularScalarCutoff
      (V.normSquared (V.mode modeData))
    base = Strain.fourierStrainMultiplier modeData omega
    baseMass = Frobenius.frobeniusSquared base
    phiSq≤1 = squareCutoffBelowOne (V.normSquared (V.mode modeData))
    baseMassNN = frobeniusSquaredNonnegative base
    scaled : L2.square phi * baseMass ≤ 1ℚ * baseMass
    scaled =
      L2.nonnegativeProductMonotone
        (L2.squareNonnegative phi) baseMassNN
        ℚP.0≤1 baseMassNN
        phiSq≤1 ℚP.≤-refl
  in
  subst
    (λ left → left ≤ baseMass)
    (sym (Frobenius.frobeniusSquaredScale phi base))
    (subst (λ right → L2.square phi * baseMass ≤ right)
      (ℚP.*-identityˡ baseMass) scaled)

compactAnnularMatrixFrobeniusBound : ∀ modeData omega →
  Frobenius.frobeniusSquared (Symbol.compactAnnularMatrixSymbol modeData omega)
  ≤ Frobenius.half * V.normSquared omega
compactAnnularMatrixFrobeniusBound modeData omega =
  ℚP.≤-trans
    (compactAnnularMatrixFrobeniusBelowPhysical modeData omega)
    (Frobenius.physicalStrainFrobeniusBound modeData omega)

round68CompactAnnularMatrixFrobeniusBoundOneHalf : Bool
round68CompactAnnularMatrixFrobeniusBoundOneHalf = true

round68CompactAnnularMatrixFrobeniusBoundOneHalfIsTrue :
  round68CompactAnnularMatrixFrobeniusBoundOneHalf ≡ true
round68CompactAnnularMatrixFrobeniusBoundOneHalfIsTrue = refl

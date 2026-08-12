module DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Turn the regular principal-log representation
--
--   J_X = I + c1 A_X + c2(X) A_X^2
--
-- into the exact finite column-mass variation theorem needed by Gate I.  With
-- c1 fixed by convention,
--
--   J_X-J_Y
--    = c1(A_X-A_Y)
--      + (c2(X)-c2(Y)) A_X^2
--      + c2(Y)(A_X^2-A_Y^2).
--
-- Hence the finite l1 column mass obeys
--
--   col(J_X-J_Y)
--    <= |c1| col(A_X-A_Y)
--       + |c2(X)-c2(Y)| col(A_X^2)
--       + |c2(Y)| col(A_X^2-A_Y^2).
--
-- This is the precise operator-level consumer for the scalar coefficient
-- modulus.  The normalized axis n=X/|X| never appears.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation

matrixScale : ℚ → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
matrixScale coefficient matrix row column = coefficient * matrix row column

matrixAdd : Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
matrixAdd left right row column = left row column + right row column

principalLogAdMatrix :
  ℚ → ℚ → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix → Jacobian.Lie3Matrix
principalLogAdMatrix c1 c2 ad adSquare =
  matrixAdd Jacobian.identity3
    (matrixAdd (matrixScale c1 ad) (matrixScale c2 adSquare))

principalLogAdDifferenceTelescope :
  ∀ c1 c2X c2Y adX adY adSquareX adSquareY row column →
  Variation.matrixDifference
    (principalLogAdMatrix c1 c2X adX adSquareX)
    (principalLogAdMatrix c1 c2Y adY adSquareY)
    row column
  ≡ matrixAdd
      (matrixScale c1 (Variation.matrixDifference adX adY))
      (matrixAdd
        (matrixScale (c2X - c2Y) adSquareX)
        (matrixScale c2Y
          (Variation.matrixDifference adSquareX adSquareY)))
      row column
principalLogAdDifferenceTelescope
    c1 c2X c2Y adX adY adSquareX adSquareY row column =
  ℚRing.solve-∀
    c1 c2X c2Y
    (adX row column) (adY row column)
    (adSquareX row column) (adSquareY row column)
    (Jacobian.identity3 row column)

matrixScaleColumnMassExact :
  ∀ coefficient matrix column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (matrixScale coefficient matrix) column
  ≡ ∣ coefficient ∣
      * RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 matrix column
matrixScaleColumnMassExact coefficient matrix column =
  trans
    (Sums.sumRationalCong Physical.lieCoordinates3 _ _
      (λ row → ℚP.∣p*q∣≡∣p∣*∣q∣ coefficient (matrix row column)))
    (Sums.sumRationalScale
      ∣ coefficient ∣ Physical.lieCoordinates3
      (λ row → ∣ matrix row column ∣))

matrixScaleColumnMassBound :
  ∀ coefficient matrix bound column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 matrix column ≤ bound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (matrixScale coefficient matrix) column
  ≤ ∣ coefficient ∣ * bound
matrixScaleColumnMassBound coefficient matrix bound column matrixBound =
  subst
    (λ lower → lower ≤ ∣ coefficient ∣ * bound)
    (sym (matrixScaleColumnMassExact coefficient matrix column))
    (Norm.scaleNonnegative
      ∣ coefficient ∣ (ℚP.0≤∣p∣ coefficient) matrixBound)

matrixAddColumnMassBound :
  ∀ left right leftBound rightBound column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 left column
    ≤ leftBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 right column
    ≤ rightBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (matrixAdd left right) column
  ≤ leftBound + rightBound
matrixAddColumnMassBound left right leftBound rightBound column
    leftMass rightMass =
  let
    triangle :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (matrixAdd left right) column
      ≤ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 left column
        + RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3 right column
    triangle =
      trans
        (Schur.sumPointwiseBelow Physical.lieCoordinates3 _ _
          (λ row → ℚP.∣p+q∣≤∣p∣+∣q∣
            (left row column) (right row column)))
        (Sums.sumRationalCong Physical.lieCoordinates3 _ _
          (λ row → ℚRing.solve-∀
            ∣ left row column ∣ ∣ right row column ∣))
  in
  ℚP.≤-trans triangle (ℚP.+-mono-≤ leftMass rightMass)

principalLogAdVariationColumnMassBound :
  ∀ c1 c2X c2Y adX adY adSquareX adSquareY
    adVariationBound adSquareNormBound adSquareVariationBound column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference adX adY) column
    ≤ adVariationBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    adSquareX column
    ≤ adSquareNormBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference adSquareX adSquareY) column
    ≤ adSquareVariationBound →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (principalLogAdMatrix c1 c2X adX adSquareX)
      (principalLogAdMatrix c1 c2Y adY adSquareY)) column
  ≤ ∣ c1 ∣ * adVariationBound
    + (∣ c2X - c2Y ∣ * adSquareNormBound
      + ∣ c2Y ∣ * adSquareVariationBound)
principalLogAdVariationColumnMassBound
    c1 c2X c2Y adX adY adSquareX adSquareY
    adVariationBound adSquareNormBound adSquareVariationBound column
    adVariationMass adSquareMass adSquareVariationMass =
  let
    first = matrixScale c1 (Variation.matrixDifference adX adY)
    second = matrixScale (c2X - c2Y) adSquareX
    third = matrixScale c2Y
      (Variation.matrixDifference adSquareX adSquareY)

    firstBound = matrixScaleColumnMassBound
      c1 (Variation.matrixDifference adX adY)
      adVariationBound column adVariationMass
    secondBound = matrixScaleColumnMassBound
      (c2X - c2Y) adSquareX
      adSquareNormBound column adSquareMass
    thirdBound = matrixScaleColumnMassBound
      c2Y (Variation.matrixDifference adSquareX adSquareY)
      adSquareVariationBound column adSquareVariationMass

    rhsBound = matrixAddColumnMassBound
      first (matrixAdd second third)
      (∣ c1 ∣ * adVariationBound)
      (∣ c2X - c2Y ∣ * adSquareNormBound
        + ∣ c2Y ∣ * adSquareVariationBound)
      column firstBound
      (matrixAddColumnMassBound
        second third
        (∣ c2X - c2Y ∣ * adSquareNormBound)
        (∣ c2Y ∣ * adSquareVariationBound)
        column secondBound thirdBound)

    massExact :
      RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (Variation.matrixDifference
          (principalLogAdMatrix c1 c2X adX adSquareX)
          (principalLogAdMatrix c1 c2Y adY adSquareY)) column
      ≡ RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
        (matrixAdd first (matrixAdd second third)) column
    massExact =
      Sums.sumRationalCong Physical.lieCoordinates3 _ _
        (λ row → cong ∣_∣
          (principalLogAdDifferenceTelescope
            c1 c2X c2Y adX adY adSquareX adSquareY row column))
  in
  subst
    (λ lower → lower
      ≤ ∣ c1 ∣ * adVariationBound
        + (∣ c2X - c2Y ∣ * adSquareNormBound
          + ∣ c2Y ∣ * adSquareVariationBound))
    (sym massExact)
    rhsBound

cmp109PrincipalLogAdPolynomialVariationIdentityLevel : ProofLevel
cmp109PrincipalLogAdPolynomialVariationIdentityLevel = machineChecked

cmp109PrincipalLogAdPolynomialVariationMassLevel : ProofLevel
cmp109PrincipalLogAdPolynomialVariationMassLevel = machineChecked

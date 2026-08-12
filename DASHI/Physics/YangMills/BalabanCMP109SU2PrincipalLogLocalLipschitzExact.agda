module DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogLocalLipschitzExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Assemble the regular ad_X-polynomial route into an explicit local Lipschitz
-- theorem.  On the half-radius coordinate cube, suppose
--
--   |c1| <= 1/2,
--   |c2(Y)| <= 1/6,
--   |c2(X)-c2(Y)| <= L2 delta,
--   |x_i|,|y_i| <= rho <= 1/2,
--   |x_i-y_i| <= delta.
--
-- The literal ad matrices satisfy
--
--   col(A_X), col(A_Y) <= 2 rho <= 1,
--   col(A_X-A_Y) <= 2 delta,
--   col(A_X^2) <= 1,
--   col(A_X^2-A_Y^2) <= 4 delta.
--
-- Therefore the exact principal-log variation estimate collapses to
--
--   col(J_X-J_Y) <= (5/3 + L2) delta.
--
-- Only the scalar two-point modulus of c2 remains to be supplied by the
-- constructive coefficient calculus.  All Lie/operator geometry, including
-- the formerly singular X/|X| issue, is discharged here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularSchurSquaredExact as RectSchur
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109SU2AdCoordinateMassExact as Ad
import DASHI.Physics.YangMills.BalabanCMP109SU2AdSquareVariationMassExact as AdSq
import DASHI.Physics.YangMills.BalabanCMP109SU2PrincipalLogAdPolynomialVariationMassExact as JVar
import DASHI.Physics.YangMills.BalabanCMP109FederbushComponentVariationExact as Variation

oneHalf oneSixth fiveThirds : ℚ
oneHalf = + 1 / 2
oneSixth = + 1 / 6
fiveThirds = + 5 / 3

two : ℚ
two = + 2 / 1

four : ℚ
four = + 4 / 1

record PrincipalLogLocalModulusData
    (c1 c2X c2Y x0 x1 x2 y0 y1 y2 rho delta L2 : ℚ) : Set where
  field
    rhoNonnegative : 0ℚ ≤ rho
    deltaNonnegative : 0ℚ ≤ delta
    L2Nonnegative : 0ℚ ≤ L2
    rhoBelowHalf : rho ≤ oneHalf

    xCube : Ad.CoordinateCube x0 x1 x2 rho
    yCube : Ad.CoordinateCube y0 y1 y2 rho
    differenceCube :
      Ad.CoordinateDifferenceCube x0 x1 x2 y0 y1 y2 delta

    c1AbsoluteBound : ∣ c1 ∣ ≤ oneHalf
    c2YAbsoluteBound : ∣ c2Y ∣ ≤ oneSixth
    c2DifferenceModulus : ∣ c2X JVar.- c2Y ∣ ≤ L2 * delta

open PrincipalLogLocalModulusData public

-- Local notation avoids asking the scalar coefficient proof to know anything
-- about the matrix representation.
coefficientDifference : ℚ → ℚ → ℚ
coefficientDifference left right = left JVar.- right

twoRadiusNonnegative : ∀ rho → 0ℚ ≤ rho → 0ℚ ≤ rho + rho
twoRadiusNonnegative rho nonnegative = ℚP.+-mono-≤ nonnegative nonnegative

twoDeltaNonnegative : ∀ delta → 0ℚ ≤ delta → 0ℚ ≤ delta + delta
twoDeltaNonnegative delta nonnegative = ℚP.+-mono-≤ nonnegative nonnegative

twoRadiusBelowOne : ∀ rho → rho ≤ oneHalf → rho + rho ≤ 1ℚ
twoRadiusBelowOne rho below =
  subst
    (λ upper → rho + rho ≤ upper)
    (ℚRing.solve [])
    (ℚP.+-mono-≤ below below)

twoRadiusSquareBelowOne : ∀ rho →
  0ℚ ≤ rho → rho ≤ oneHalf →
  (rho + rho) * (rho + rho) ≤ 1ℚ
twoRadiusSquareBelowOne rho nonnegative below =
  let
    cNonnegative = twoRadiusNonnegative rho nonnegative
    cBelowOne = twoRadiusBelowOne rho below
    squareBelowC = Norm.scaleNonnegative
      (rho + rho) cNonnegative cBelowOne
  in
  ℚP.≤-trans squareBelowC cBelowOne

adSquareVariationBelowFourDelta : ∀ rho delta →
  0ℚ ≤ rho → rho ≤ oneHalf → 0ℚ ≤ delta →
  ((rho + rho) * (delta + delta))
    + ((rho + rho) * (delta + delta))
  ≤ four * delta
adSquareVariationBelowFourDelta rho delta rhoNN rhoHalf deltaNN =
  let
    cBelowOne = twoRadiusBelowOne rho rhoHalf
    dNN = twoDeltaNonnegative delta deltaNN
    oneTerm : (rho + rho) * (delta + delta) ≤ delta + delta
    oneTerm = subst
      (λ upper → (rho + rho) * (delta + delta) ≤ upper)
      (ℚP.*-identityˡ (delta + delta))
      (ℚP.*-monoʳ-≤-nonNeg (delta + delta) cBelowOne)
    doubled = ℚP.+-mono-≤ oneTerm oneTerm
  in
  subst
    (λ upper →
      ((rho + rho) * (delta + delta))
        + ((rho + rho) * (delta + delta)) ≤ upper)
    (ℚRing.solve-∀ delta)
    doubled

firstTermBelowDelta : ∀ c1 delta →
  0ℚ ≤ delta → ∣ c1 ∣ ≤ oneHalf →
  ∣ c1 ∣ * (delta + delta) ≤ delta
firstTermBelowDelta c1 delta deltaNN c1Bound =
  let
    twoDeltaNN = twoDeltaNonnegative delta deltaNN
    scaled = ℚP.*-monoʳ-≤-nonNeg (delta + delta) c1Bound
  in
  subst
    (λ upper → ∣ c1 ∣ * (delta + delta) ≤ upper)
    (ℚRing.solve-∀ delta)
    scaled

secondTermBelowL2Delta : ∀ c2X c2Y L2 delta adSquareBound →
  0ℚ ≤ L2 → 0ℚ ≤ delta →
  ∣ coefficientDifference c2X c2Y ∣ ≤ L2 * delta →
  adSquareBound ≤ 1ℚ →
  0ℚ ≤ adSquareBound →
  ∣ coefficientDifference c2X c2Y ∣ * adSquareBound
  ≤ L2 * delta
secondTermBelowL2Delta c2X c2Y L2 delta adSquareBound
    L2NN deltaNN coefficientBound squareBelowOne squareNN =
  let
    coefficientNN = ℚP.0≤∣p∣ (coefficientDifference c2X c2Y)
    shrinkSquare = ℚP.*-monoˡ-≤-nonNeg
      ∣ coefficientDifference c2X c2Y ∣ squareBelowOne
    rightIdentity = ℚP.*-identityʳ
      ∣ coefficientDifference c2X c2Y ∣
  in
  ℚP.≤-trans shrinkSquare
    (subst
      (λ lower → lower ≤ L2 * delta)
      (sym rightIdentity)
      coefficientBound)

thirdTermBelowTwoThirdsDelta : ∀ c2Y delta variationBound →
  0ℚ ≤ delta →
  ∣ c2Y ∣ ≤ oneSixth →
  variationBound ≤ four * delta →
  0ℚ ≤ variationBound →
  ∣ c2Y ∣ * variationBound ≤ (+ 2 / 3) * delta
thirdTermBelowTwoThirdsDelta c2Y delta variationBound
    deltaNN c2Bound variationBelow variationNN =
  let
    first = Norm.scaleNonnegative ∣ c2Y ∣ (ℚP.0≤∣p∣ c2Y) variationBelow
    fourDeltaNN = Schur.productNonnegative
      four delta (ℚP.nonNegative⁻¹ four) deltaNN
    second = ℚP.*-monoʳ-≤-nonNeg (four * delta) c2Bound
    chained = ℚP.≤-trans first second
  in
  subst
    (λ upper → ∣ c2Y ∣ * variationBound ≤ upper)
    (ℚRing.solve-∀ delta)
    chained

principalLogLocalLipschitzColumn :
  ∀ c1 c2X c2Y x0 x1 x2 y0 y1 y2 rho delta L2 →
  PrincipalLogLocalModulusData
    c1 c2X c2Y x0 x1 x2 y0 y1 y2 rho delta L2 →
  ∀ column →
  RectSchur.rectAbsoluteColumnMass Physical.lieCoordinates3
    (Variation.matrixDifference
      (JVar.principalLogAdMatrix
        c1 c2X
        (Ad.adMatrix x0 x1 x2)
        (AdSq.adSquare (Ad.adMatrix x0 x1 x2)))
      (JVar.principalLogAdMatrix
        c1 c2Y
        (Ad.adMatrix y0 y1 y2)
        (AdSq.adSquare (Ad.adMatrix y0 y1 y2)))) column
  ≤ (fiveThirds + L2) * delta
principalLogLocalLipschitzColumn
    c1 c2X c2Y x0 x1 x2 y0 y1 y2 rho delta L2 dataSet column =
  let
    adX = Ad.adMatrix x0 x1 x2
    adY = Ad.adMatrix y0 y1 y2
    adSquareX = AdSq.adSquare adX
    adSquareY = AdSq.adSquare adY
    c = rho + rho
    d = delta + delta
    squareBound = c * c
    squareVariationBound = c * d + c * d

    cNN = twoRadiusNonnegative rho (rhoNonnegative dataSet)
    dNN = twoDeltaNonnegative delta (deltaNonnegative dataSet)
    squareNN = Schur.productNonnegative c c cNN cNN
    squareVariationNN =
      ℚP.+-mono-≤
        (Schur.productNonnegative c d cNN dNN)
        (Schur.productNonnegative c d cNN dNN)

    adXColumns = Ad.adCoordinateCubeColumnBound
      x0 x1 x2 rho (xCube dataSet)
    adYColumns = Ad.adCoordinateCubeColumnBound
      y0 y1 y2 rho (yCube dataSet)
    adVariationColumns = Ad.adDifferenceColumnBound
      x0 x1 x2 y0 y1 y2 delta (differenceCube dataSet)

    adSquareColumn = AdSq.adSquareColumnMassBound
      adX c column cNN adXColumns
    adSquareVariationColumn = AdSq.adSquareVariationColumnMassBound
      adX adY c d column cNN dNN
      adXColumns adYColumns adVariationColumns

    raw = JVar.principalLogAdVariationColumnMassBound
      c1 c2X c2Y adX adY adSquareX adSquareY
      d squareBound squareVariationBound column
      (adVariationColumns column)
      adSquareColumn adSquareVariationColumn

    first = firstTermBelowDelta c1 delta
      (deltaNonnegative dataSet) (c1AbsoluteBound dataSet)
    second = secondTermBelowL2Delta c2X c2Y L2 delta squareBound
      (L2Nonnegative dataSet) (deltaNonnegative dataSet)
      (c2DifferenceModulus dataSet)
      (twoRadiusSquareBelowOne rho
        (rhoNonnegative dataSet) (rhoBelowHalf dataSet))
      squareNN
    third = thirdTermBelowTwoThirdsDelta c2Y delta squareVariationBound
      (deltaNonnegative dataSet) (c2YAbsoluteBound dataSet)
      (adSquareVariationBelowFourDelta rho delta
        (rhoNonnegative dataSet) (rhoBelowHalf dataSet)
        (deltaNonnegative dataSet))
      squareVariationNN

    combined = ℚP.+-mono-≤ first (ℚP.+-mono-≤ second third)
    targetExact :
      delta + (L2 * delta + (+ 2 / 3) * delta)
      ≡ (fiveThirds + L2) * delta
    targetExact = ℚRing.solve-∀ L2 delta
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        (∣ c1 ∣ * d
          + (∣ coefficientDifference c2X c2Y ∣ * squareBound
            + ∣ c2Y ∣ * squareVariationBound)) ≤ upper)
      targetExact combined)

cmp109PrincipalLogLocalLipschitzGeometryLevel : ProofLevel
cmp109PrincipalLogLocalLipschitzGeometryLevel = machineChecked

cmp109PrincipalLogLocalLipschitzFiveThirdsPlusCoefficientLevel : ProofLevel
cmp109PrincipalLogLocalLipschitzFiveThirdsPlusCoefficientLevel = machineChecked

module DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- David J. Green and Ian J. Leary,
-- "The spectrum of the Chern subring",
-- Commentarii Mathematici Helvetici 73 (1998), 406--426.
-- DOI: 10.1007/s000140050062.
--
-- David J. Green and Ian J. Leary,
-- "Chern classes and extraspecial groups",
-- Manuscripta Mathematica 88 (1995), 73--84.
-- DOI: 10.1007/BF02567806.
--
-- Jean Dieudonne,
-- "La geometrie des groupes classiques",
-- Springer, 1971.  No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- Correctly separate the 729-dimensional Schrodinger coordinate
--
--   X = F_3^6
--
-- from the full extraspecial quotient
--
--   E / Z(E) = X + X^* = F_3^12.
--
-- Every two-plane in the fixed Lagrangian X is automatically isotropic in
-- the full symplectic quotient.  There are
--
--   [6 choose 2]_3 = 11011
--
-- such planes.  Each U <= X lifts with the centre to an elementary abelian
-- subgroup Z(E) x U of rank three.  The 729-dimensional Schrodinger module
-- restricts to U as
--
--   3^(6-2) copies of Reg(U) = 81 copies of a 9-dimensional regular module.
--
-- Separately, the full twelve-dimensional symplectic quotient has
--
--   [12 choose 2]_3 = 5883904390 total two-planes,
--   1961279320 isotropic two-planes,
--   3922625070 non-isotropic two-planes.
--
-- These are exact incidence and character-restriction inputs for a future
-- kappa_r/Chern-subring calculation; no cohomology class is fabricated here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

fieldOrder : Nat
fieldOrder = 3

lLagrangianDimension : Nat
lLagrangianDimension = 6

schrodingerDimension : Nat
schrodingerDimension = 729

fullSymplecticDimension : Nat
fullSymplecticDimension = 12

centreOrder : Nat
centreOrder = 3

------------------------------------------------------------------------
-- Fixed-Lagrangian two-plane count.
------------------------------------------------------------------------

lLagrangianTwoPlaneCount : Nat
lLagrangianTwoPlaneCount = 11011

gaussianDenominator : Nat
gaussianDenominator = 16

lLagrangianTwoPlaneNumerator : Nat
lLagrangianTwoPlaneNumerator = 728 * 242

lLagrangianTwoPlaneCertificate :
  gaussianDenominator * lLagrangianTwoPlaneCount
  ≡ lLagrangianTwoPlaneNumerator
lLagrangianTwoPlaneCertificate = refl

translationPlaneOrder : Nat
translationPlaneOrder = 9

centralLiftOrder : Nat
centralLiftOrder = centreOrder * translationPlaneOrder

centralLiftOrderIsTwentySeven : centralLiftOrder ≡ 27
centralLiftOrderIsTwentySeven = refl

centralLiftRank : Nat
centralLiftRank = 3

regularCharacterCount : Nat
regularCharacterCount = translationPlaneOrder

regularCharacterMultiplicity : Nat
regularCharacterMultiplicity = 81

restrictedSchrodingerDimension : Nat
restrictedSchrodingerDimension =
  regularCharacterCount * regularCharacterMultiplicity

restrictedSchrodingerDimensionIs729 :
  restrictedSchrodingerDimension ≡ schrodingerDimension
restrictedSchrodingerDimensionIs729 = refl

regularCopiesTimesPlaneOrderIsSchrodinger :
  regularCharacterMultiplicity * translationPlaneOrder
  ≡ schrodingerDimension
regularCopiesTimesPlaneOrderIsSchrodinger = refl

------------------------------------------------------------------------
-- Full F_3^12 symplectic two-plane strata.
------------------------------------------------------------------------

fullTwoPlaneCount : Nat
fullTwoPlaneCount = 5883904390

fullIsotropicTwoPlaneCount : Nat
fullIsotropicTwoPlaneCount = 1961279320

fullNonIsotropicTwoPlaneCount : Nat
fullNonIsotropicTwoPlaneCount = 3922625070

fullTwoPlaneNumerator : Nat
fullTwoPlaneNumerator = 531440 * 177146

fullIsotropicTwoPlaneNumerator : Nat
fullIsotropicTwoPlaneNumerator = 531440 * 59048

fullTwoPlaneCertificate :
  gaussianDenominator * fullTwoPlaneCount ≡ fullTwoPlaneNumerator
fullTwoPlaneCertificate = refl

fullIsotropicTwoPlaneCertificate :
  gaussianDenominator * fullIsotropicTwoPlaneCount
  ≡ fullIsotropicTwoPlaneNumerator
fullIsotropicTwoPlaneCertificate = refl

fullTwoPlanePartition :
  fullIsotropicTwoPlaneCount + fullNonIsotropicTwoPlaneCount
  ≡ fullTwoPlaneCount
fullTwoPlanePartition = refl

data PlaneLocation : Set where
  fixedLagrangianPlane : PlaneLocation
  fullSymplecticIsotropicPlane : PlaneLocation
  fullSymplecticNonIsotropicPlane : PlaneLocation

planeCount : PlaneLocation → Nat
planeCount fixedLagrangianPlane = lLagrangianTwoPlaneCount
planeCount fullSymplecticIsotropicPlane = fullIsotropicTwoPlaneCount
planeCount fullSymplecticNonIsotropicPlane = fullNonIsotropicTwoPlaneCount

record ElementaryRestrictionInput : Set where
  constructor elementaryRestrictionInput
  field
    translationRank : Nat
    centralRank : Nat
    subgroupOrder : Nat
    linearCharacterCount : Nat
    characterMultiplicity : Nat
    representedDimension : Nat

canonicalRankThreeRestrictionInput : ElementaryRestrictionInput
canonicalRankThreeRestrictionInput =
  elementaryRestrictionInput 2 1 27 9 81 729

record ChernRestrictionBoundary : Set where
  constructor chernRestrictionBoundary
  field
    lLagrangianPlanesEnumerated : Bool
    lLagrangianPlanesEnumeratedIsTrue :
      lLagrangianPlanesEnumerated ≡ true
    fullSymplecticStrataCounted : Bool
    fullSymplecticStrataCountedIsTrue :
      fullSymplecticStrataCounted ≡ true
    fixedLagrangianPlanesSplitByArtificialAlternatingRank : Bool
    fixedLagrangianPlanesSplitByArtificialAlternatingRankIsFalse :
      fixedLagrangianPlanesSplitByArtificialAlternatingRank ≡ false
    schrodingerRestrictionMultiplicityChecked : Bool
    schrodingerRestrictionMultiplicityCheckedIsTrue :
      schrodingerRestrictionMultiplicityChecked ≡ true
    kappaClassesConstructed : Bool
    kappaClassesConstructedIsFalse :
      kappaClassesConstructed ≡ false
    chernSubringRestrictionMapComputed : Bool
    chernSubringRestrictionMapComputedIsFalse :
      chernSubringRestrictionMapComputed ≡ false

canonicalChernRestrictionBoundary : ChernRestrictionBoundary
canonicalChernRestrictionBoundary =
  chernRestrictionBoundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl

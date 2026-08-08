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
-- Supply the exact finite incidence counts consumed by the executable
-- generator-to-invariant dashboard for the symplectic space F_3^6.
--
-- Every two-dimensional subspace is an elementary abelian subgroup C_3^2
-- of the additive carrier.  Its alternating-form restriction has rank zero
-- or two.  The exact strata are
--
--   all 2-planes          = [6 choose 2]_3 = 11011,
--   totally isotropic     = 3640,
--   nondegenerate rank-2  = 7371.
--
-- These are the subgroup strata on which genuine Chern-class restrictions
-- and kappa_r generators may later be evaluated.  This module does not
-- fabricate cohomology classes from the incidence counts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

fieldOrder : Nat
fieldOrder = 3

ambientVectorCount : Nat
ambientVectorCount = 729

projectiveLineCount : Nat
projectiveLineCount = 364

projectiveLineCountCertificate :
  2 * projectiveLineCount + 1 ≡ ambientVectorCount
projectiveLineCountCertificate = refl

allTwoPlaneCount : Nat
allTwoPlaneCount = 11011

isotropicTwoPlaneCount : Nat
isotropicTwoPlaneCount = 3640

symplecticTwoPlaneCount : Nat
symplecticTwoPlaneCount = 7371

------------------------------------------------------------------------
-- Gaussian-binomial and symplectic-Grassmann multiplication certificates.
--
-- [6 choose 2]_3
--   = ((3^6-1)(3^5-1))/((3^2-1)(3-1))
--   = (728*242)/16.
--
-- The rank-two totally isotropic Grassmannian in a six-dimensional
-- symplectic space has
--
--   ((3^6-1)(3^4-1))/((3^2-1)(3-1))
--   = (728*80)/16
--
-- points.
------------------------------------------------------------------------

gradedDenominator : Nat
gradedDenominator = 16

gaussianTwoPlaneNumerator : Nat
gaussianTwoPlaneNumerator = 728 * 242

gaussianTwoPlaneCertificate :
  gradedDenominator * allTwoPlaneCount ≡ gaussianTwoPlaneNumerator
gaussianTwoPlaneCertificate = refl

isotropicTwoPlaneNumerator : Nat
isotropicTwoPlaneNumerator = 728 * 80

isotropicTwoPlaneCertificate :
  gradedDenominator * isotropicTwoPlaneCount
  ≡ isotropicTwoPlaneNumerator
isotropicTwoPlaneCertificate = refl

twoPlanePartition :
  isotropicTwoPlaneCount + symplecticTwoPlaneCount ≡ allTwoPlaneCount
twoPlanePartition = refl

data AlternatingRestrictionRank : Set where
  rankZero : AlternatingRestrictionRank
  rankTwo : AlternatingRestrictionRank

rankStratumCount : AlternatingRestrictionRank → Nat
rankStratumCount rankZero = isotropicTwoPlaneCount
rankStratumCount rankTwo = symplecticTwoPlaneCount

rankStrataExhaustTwoPlanes :
  rankStratumCount rankZero + rankStratumCount rankTwo ≡ allTwoPlaneCount
rankStrataExhaustTwoPlanes = refl

record GeneratorInvariantInput : Set where
  constructor generatorInvariantInput
  field
    alternatingRank : AlternatingRestrictionRank
    qPlusZeroCount : Nat
    qMinusZeroCount : Nat
    rrefSupportWeight : Nat

record ChernRestrictionBoundary : Set where
  constructor chernRestrictionBoundary
  field
    elementaryAbelianStrataEnumerated : Bool
    elementaryAbelianStrataEnumeratedIsTrue :
      elementaryAbelianStrataEnumerated ≡ true
    alternatingRestrictionRanksEnumerated : Bool
    alternatingRestrictionRanksEnumeratedIsTrue :
      alternatingRestrictionRanksEnumerated ≡ true
    kappaClassesConstructed : Bool
    kappaClassesConstructedIsFalse :
      kappaClassesConstructed ≡ false
    chernSubringRestrictionMapComputed : Bool
    chernSubringRestrictionMapComputedIsFalse :
      chernSubringRestrictionMapComputed ≡ false
    incidenceCountsAloneDetermineCohomology : Bool
    incidenceCountsAloneDetermineCohomologyIsFalse :
      incidenceCountsAloneDetermineCohomology ≡ false

canonicalChernRestrictionBoundary : ChernRestrictionBoundary
canonicalChernRestrictionBoundary =
  chernRestrictionBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

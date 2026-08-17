module DASHI.Moonshine.P11MatchedDihedralSixSectorBasisExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Anchor the six-coordinate p=11 split-lift falsifier to the repository's
-- actual matched-dihedral restriction.  Since p=11=2j+1 gives j=5, the
-- existing carrier has exactly
--
--   epsilon, rho1, rho2, rho3, rho4, rho5.
--
-- This file merely gives names and basis vectors to those already-existing
-- constructors; it does not introduce another representation theory.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (+_)

import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.P11MatchedDihedralSplitLiftNoGoExact as Lift

------------------------------------------------------------------------
-- The five actual PairIndex 5 values.
------------------------------------------------------------------------

pair1 : Matched.PairIndex 5
pair1 = Matched.firstPair

pair2 : Matched.PairIndex 5
pair2 = Matched.nextPair Matched.firstPair

pair3 : Matched.PairIndex 5
pair3 = Matched.nextPair (Matched.nextPair Matched.firstPair)

pair4 : Matched.PairIndex 5
pair4 = Matched.nextPair
  (Matched.nextPair (Matched.nextPair Matched.firstPair))

pair5 : Matched.PairIndex 5
pair5 = Matched.nextPair
  (Matched.nextPair (Matched.nextPair (Matched.nextPair Matched.firstPair)))

------------------------------------------------------------------------
-- Named actual sectors.
------------------------------------------------------------------------

epsilonSector : Matched.MatchedDihedralSector 5
epsilonSector = Matched.selectedSinglet

rho1Sector rho2Sector rho3Sector rho4Sector rho5Sector :
  Matched.MatchedDihedralSector 5
rho1Sector = Matched.pairedDoublet pair1
rho2Sector = Matched.pairedDoublet pair2
rho3Sector = Matched.pairedDoublet pair3
rho4Sector = Matched.pairedDoublet pair4
rho5Sector = Matched.pairedDoublet pair5

p11MatchedSectorCountIsSix : Matched.occurringSectorCount 5 ≡ 6
p11MatchedSectorCountIsSix = refl

p11MatchedDimensionIsEleven :
  Matched.doubletMass (Matched.allPairIndices 5) ≡ 10
p11MatchedDimensionIsEleven = refl

------------------------------------------------------------------------
-- Explicit basis vectors in the six-coordinate free module.
------------------------------------------------------------------------

epsilonBasis rho1Basis rho2Basis rho3Basis rho4Basis rho5Basis :
  Lift.P11MatchedSectorVector

epsilonBasis = Lift.sectorVector (+ 1) (+ 0) (+ 0) (+ 0) (+ 0) (+ 0)
rho1Basis = Lift.sectorVector (+ 0) (+ 1) (+ 0) (+ 0) (+ 0) (+ 0)
rho2Basis = Lift.sectorVector (+ 0) (+ 0) (+ 1) (+ 0) (+ 0) (+ 0)
rho3Basis = Lift.sectorVector (+ 0) (+ 0) (+ 0) (+ 1) (+ 0) (+ 0)
rho4Basis = Lift.sectorVector (+ 0) (+ 0) (+ 0) (+ 0) (+ 1) (+ 0)
rho5Basis = Lift.sectorVector (+ 0) (+ 0) (+ 0) (+ 0) (+ 0) (+ 1)

sectorBasis :
  Matched.MatchedDihedralSector 5 → Lift.P11MatchedSectorVector
sectorBasis Matched.selectedSinglet = epsilonBasis
sectorBasis (Matched.pairedDoublet Matched.firstPair) = rho1Basis
sectorBasis (Matched.pairedDoublet (Matched.nextPair Matched.firstPair)) = rho2Basis
sectorBasis
  (Matched.pairedDoublet
    (Matched.nextPair (Matched.nextPair Matched.firstPair))) = rho3Basis
sectorBasis
  (Matched.pairedDoublet
    (Matched.nextPair
      (Matched.nextPair (Matched.nextPair Matched.firstPair)))) = rho4Basis
sectorBasis
  (Matched.pairedDoublet
    (Matched.nextPair
      (Matched.nextPair
        (Matched.nextPair (Matched.nextPair Matched.firstPair))))) = rho5Basis

------------------------------------------------------------------------
-- The old countermodel's rho2 basis is literally the actual second doublet.
------------------------------------------------------------------------

rho2BasisMatchesSplitLiftWitness : rho2Basis ≡ Lift.rho2Basis
rho2BasisMatchesSplitLiftWitness = refl

rho2ActualSectorIsErasedByTestProjector :
  Lift.splitProjector (sectorBasis rho2Sector) ≡ Lift.zeroSectorVector
rho2ActualSectorIsErasedByTestProjector = refl

------------------------------------------------------------------------
-- Boundary: the basis chart is exact; the two-coordinate compression is still
-- only a test lens and is not promoted to the geometric supersingular map.
------------------------------------------------------------------------

record P11MatchedDihedralSixSectorBoundary : Set where
  field
    actualJ5MatchedSectorCountSix : Bool
    actualJ5MatchedSectorCountSixIsTrue : actualJ5MatchedSectorCountSix ≡ true

    actualSixSectorBasisConstructed : Bool
    actualSixSectorBasisConstructedIsTrue : actualSixSectorBasisConstructed ≡ true

    splitLiftCarrierAnchoredToActualSectors : Bool
    splitLiftCarrierAnchoredToActualSectorsIsTrue :
      splitLiftCarrierAnchoredToActualSectors ≡ true

    binaryTestProjectionPromotedToCanonicalRepresentationInvariant : Bool
    binaryTestProjectionPromotedToCanonicalRepresentationInvariantIsFalse :
      binaryTestProjectionPromotedToCanonicalRepresentationInvariant ≡ false

canonicalP11MatchedDihedralSixSectorBoundary :
  P11MatchedDihedralSixSectorBoundary
canonicalP11MatchedDihedralSixSectorBoundary =
  record
    { actualJ5MatchedSectorCountSix = true
    ; actualJ5MatchedSectorCountSixIsTrue = refl
    ; actualSixSectorBasisConstructed = true
    ; actualSixSectorBasisConstructedIsTrue = refl
    ; splitLiftCarrierAnchoredToActualSectors = true
    ; splitLiftCarrierAnchoredToActualSectorsIsTrue = refl
    ; binaryTestProjectionPromotedToCanonicalRepresentationInvariant = false
    ; binaryTestProjectionPromotedToCanonicalRepresentationInvariantIsFalse = refl
    }

module DASHI.Moonshine.OggRepresentationReductionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as D4Scan
import DASHI.Foundations.D4SO3RestrictionCharacterJ0To35Exact as D4Character
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet
import DASHI.Foundations.TetrahedralSO3RestrictionCharacterJ0To35Exact as TetCharacter
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.OctahedralSO3RestrictionCharacterJ0To35Exact as OctCharacter
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.IcosahedralSO3RestrictionCharacterJ0To35Exact as IcoCharacter
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.PolyhedralFixedSpaceDerivedNonaryExact as DerivedNonary
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact as Character
import DASHI.Foundations.PolyhedralRegularRepresentationShiftExact as Regular
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as CandidateSquare
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.OggPolyhedralReductionControlExact as Control
import DASHI.Moonshine.OggTetrahedralReductionControlExact as TetControl
import DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact as Intertwiner
import DASHI.Moonshine.TernarySevenOggSSPComparisonExact as Seven
import DASHI.Physics.Closure.PhysicalSSPHeckeModelClosureReceipt as Existing

------------------------------------------------------------------------
-- Continuous dimension lane and p=2 boundary.
------------------------------------------------------------------------

spinHalfIsTwo : Spin.su2Dimension 1 ≡ 2
spinHalfIsTwo = Spin.spinHalfDimensionIsTwo

spinHalfNotOnSO3DescentLane : Spin.EvenHighestWeight 1 → ⊥
spinHalfNotOnSO3DescentLane = Spin.spinorHighestWeightOneDoesNotDescend

j35IsDimension71 : Spin.jDimension Spin.j35 ≡ 71
j35IsDimension71 = Spin.j35DimensionIsSeventyOne

candidateSquareIncludesNonOggNine :
  CandidateSquare.candidateLevelNat
    (CandidateSquare.spatialLevel Spin.j4)
  ≡ 9
candidateSquareIncludesNonOggNine = refl

------------------------------------------------------------------------
-- Five irreps of nine: actual SO(3) j=4 restriction to rotational D4.
------------------------------------------------------------------------

fiveIrrepNineDimension : D4.j4D4Dimension ≡ 9
fiveIrrepNineDimension = D4.j4D4DimensionIsNine

fiveIrrepNineA2Present : D4.j4D4Multiplicity Candidate.A2 ≡ 1
fiveIrrepNineA2Present = D4.j4RestrictionA2IsPresent

fiveIrrepNineIsTrivialPlusRegular :
  (kind : Candidate.D4IrrepKind) →
  D4.j4D4Multiplicity kind
  ≡ D4.trivialD4Multiplicity kind + D4.regularD4Multiplicity kind
fiveIrrepNineIsTrivialPlusRegular = D4.j4IsTrivialPlusRegular

rawNineCellIsDifferentRepresentation :
  ((kind : Candidate.D4IrrepKind) →
    Candidate.rawNineMultiplicity kind ≡ D4.j4D4Multiplicity kind) →
  ⊥
rawNineCellIsDifferentRepresentation = D4.rawNinePermutationIsNotJ4Restriction

------------------------------------------------------------------------
-- Full character certification for four finite rotation groups.
------------------------------------------------------------------------

d4AllRowsCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : D4.D4RotationClass) →
  D4Character.branchingCharacter (D4Scan.branchingSpectrum j) class
  ≡ D4Character.restrictedCharacter j class
d4AllRowsCharacterExact = D4Character.branchingCharacterExact

tetrahedralAllRowsCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Tet.TetrahedralClass) →
  Tet.branchingCharacter (Tet.branchingSpectrum j) class
  ≡ Tet.restrictedCharacter j class
tetrahedralAllRowsCharacterExact = TetCharacter.branchingCharacterExact

octahedralAllRowsCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Oct.OctahedralClass) →
  Character.octahedralBranchingCharacter (Oct.branchingSpectrum j) class
  ≡ Character.restrictedOctahedralCharacter j class
octahedralAllRowsCharacterExact = OctCharacter.branchingCharacterExact

icosahedralAllRowsCharacterExact :
  (j : Spin.AngularMomentum0To35) →
  (class : Ico.IcosahedralClass) →
  Character.icosahedralBranchingCharacter (Ico.branchingSpectrum j) class
  ≡ Character.restrictedIcosahedralCharacter j class
icosahedralAllRowsCharacterExact = IcoCharacter.branchingCharacterExact

------------------------------------------------------------------------
-- Non-Ogg controls and regular-quotient no-go results.
------------------------------------------------------------------------

nineIsNotOgg : Control.OggDimensionWitness 9 → ⊥
nineIsNotOgg = Control.dimension9IsNotOgg

fifteenIsNotOgg : Control.OggDimensionWitness 15 → ⊥
fifteenIsNotOgg = TetControl.dimension15IsNotOgg

fortyThreeIsNotOgg : Control.OggDimensionWitness 43 → ⊥
fortyThreeIsNotOgg = DerivedNonary.dimension43IsNotOgg

fiftyThreeIsNotOgg : Control.OggDimensionWitness 53 → ⊥
fiftyThreeIsNotOgg = Control.dimension53IsNotOgg

sixtySevenIsNotOgg : Control.OggDimensionWitness 67 → ⊥
sixtySevenIsNotOgg = Control.dimension67IsNotOgg

d4RegularPeriodIsFour :
  Regular.nonidentityCharacterPeriod Regular.rotationalD4 ≡ 4
d4RegularPeriodIsFour = refl

tetrahedralRegularPeriodIsSix :
  Regular.nonidentityCharacterPeriod Regular.rotationalTetrahedral ≡ 6
tetrahedralRegularPeriodIsSix = refl

octahedralRegularPeriodIsTwelve :
  Regular.nonidentityCharacterPeriod Regular.rotationalOctahedral ≡ 12
octahedralRegularPeriodIsTwelve = refl

icosahedralRegularPeriodIsThirty :
  Regular.nonidentityCharacterPeriod Regular.rotationalIcosahedral ≡ 30
icosahedralRegularPeriodIsThirty = refl

tetrahedral3To15RegularCollision :
  Tet.branchingSpectrum Spin.j7
  ≡ Tet.addSpectrum Tet.regularSpectrum (Tet.branchingSpectrum Spin.j1)
tetrahedral3To15RegularCollision = Tet.j1ToJ7IsOneRegularShift

octahedral5To53RegularCollision :
  Oct.branchingSpectrum Spin.j26
  ≡ Oct.addSpectrum Oct.regularSpectrum
      (Oct.addSpectrum Oct.regularSpectrum (Oct.branchingSpectrum Spin.j2))
octahedral5To53RegularCollision = Oct.j2ToJ26IsTwoRegularShifts

icosahedral7To67RegularCollision :
  Ico.branchingSpectrum Spin.j33
  ≡ Ico.addSpectrum Ico.regularSpectrum (Ico.branchingSpectrum Spin.j3)
icosahedral7To67RegularCollision = Ico.j3ToJ33IsOneRegularShift

------------------------------------------------------------------------
-- Actual fixed-space probes and derived 369 address.
------------------------------------------------------------------------

c3NotS3 : Fixed.orderC3 ≡ Fixed.orderTernaryS3 → ⊥
c3NotS3 = Fixed.c3IsNotTernaryS3ByOrder

j3C3FixedSpaceIsThree : Fixed.fixedDimension Spin.j3 Fixed.C3Probe ≡ 3
j3C3FixedSpaceIsThree = Fixed.j3C3FixedDimension

sevenAndFortyThreeDerivedNonaryCollide :
  DerivedNonary.fixedSpaceNonary Spin.j3
  ≡ DerivedNonary.fixedSpaceNonary Spin.j21
sevenAndFortyThreeDerivedNonaryCollide =
  DerivedNonary.j3AndJ21DerivedNonaryCollide

------------------------------------------------------------------------
-- Arithmetic/modular side remains independent until an intertwiner is built.
------------------------------------------------------------------------

existingCarrierEqualityStillOpen :
  Existing.sspCarrierEqualsHeckeModelProved
    Existing.canonicalPhysicalSSPHeckeModelClosureReceipt
  ≡ false
existingCarrierEqualityStillOpen = Intertwiner.existingCarrierEqualityStillOpen

classicalIntertwinerStillOpen :
  Intertwiner.witnessConstructed
    Intertwiner.canonicalSSPRepresentationModularIntertwinerTarget
  ≡ false
classicalIntertwinerStillOpen = refl

unbiasedCandidateExceptionalLocusStillOpen :
  CandidateSquare.exceptionalLocusEqualityConstructed
    CandidateSquare.canonicalCandidateLevelSquareBoundary
  ≡ false
unbiasedCandidateExceptionalLocusStillOpen = refl

modularGenusZeroNotManufacturedHere :
  Modular.genusZeroIsInternallyProved Modular.canonicalModularCurveBoundary
  ≡ false
modularGenusZeroNotManufacturedHere = refl

sevenSevenOneIsNotSelector :
  Seven.sevenSevenOneUsedAsSSPSelector Seven.canonicalTernarySevenOggSSPBoundary
  ≡ false
sevenSevenOneIsNotSelector = refl

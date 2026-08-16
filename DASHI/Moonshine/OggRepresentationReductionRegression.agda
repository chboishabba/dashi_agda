module DASHI.Moonshine.OggRepresentationReductionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed
import DASHI.Foundations.PolyhedralRestrictionCriticalCharacterExact as Character
import DASHI.Moonshine.ModularCurveJFrickeInterfaceExact as Modular
import DASHI.Moonshine.OggPolyhedralReductionControlExact as Control
import DASHI.Moonshine.SSPRepresentationHeckeIntertwinerBoundaryExact as Intertwiner
import DASHI.Moonshine.TernarySevenOggSSPComparisonExact as Seven

------------------------------------------------------------------------
-- Continuous dimension lane and p=2 boundary.
------------------------------------------------------------------------

spinHalfIsTwo : Spin.su2Dimension 1 ≡ 2
spinHalfIsTwo = Spin.spinHalfDimensionIsTwo

spinHalfNotOnSO3DescentLane : Spin.EvenHighestWeight 1 → ⊥
spinHalfNotOnSO3DescentLane = Spin.spinorHighestWeightOneDoesNotDescend

j35IsDimension71 : Spin.jDimension Spin.j35 ≡ 71
j35IsDimension71 = Spin.j35DimensionIsSeventyOne

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
-- Non-Ogg controls and regular-quotient no-go results.
------------------------------------------------------------------------

nineIsNotOgg : Control.OggDimensionWitness 9 → ⊥
nineIsNotOgg = Control.dimension9IsNotOgg

fiftyThreeIsNotOgg : Control.OggDimensionWitness 53 → ⊥
fiftyThreeIsNotOgg = Control.dimension53IsNotOgg

sixtySevenIsNotOgg : Control.OggDimensionWitness 67 → ⊥
sixtySevenIsNotOgg = Control.dimension67IsNotOgg

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
-- Character certification for the rows used by those controls.
------------------------------------------------------------------------

nineOctahedralCharacterExact :
  (class : Oct.OctahedralClass) →
  Character.octahedralBranchingCharacter (Oct.branchingSpectrum Spin.j4) class
  ≡ Character.restrictedOctahedralCharacter Spin.j4 class
nineOctahedralCharacterExact = Character.j4OctahedralCharacterExact

sevenIcosahedralCharacterExact :
  (class : Ico.IcosahedralClass) →
  Character.icosahedralBranchingCharacter (Ico.branchingSpectrum Spin.j3) class
  ≡ Character.restrictedIcosahedralCharacter Spin.j3 class
sevenIcosahedralCharacterExact = Character.j3IcosahedralCharacterExact

------------------------------------------------------------------------
-- Actual fixed-space probes: C3 is not the six-element S3 permutation group.
------------------------------------------------------------------------

c3NotS3 : Fixed.orderC3 ≡ Fixed.orderTernaryS3 → ⊥
c3NotS3 = Fixed.c3IsNotTernaryS3ByOrder

j3C3FixedSpaceIsThree : Fixed.fixedDimension Spin.j3 Fixed.C3Probe ≡ 3
j3C3FixedSpaceIsThree = Fixed.j3C3FixedDimension

------------------------------------------------------------------------
-- Arithmetic/modular side remains independent until an intertwiner is built.
------------------------------------------------------------------------

existingCarrierEqualityStillOpen :
  Intertwiner.Existing.sspCarrierEqualsHeckeModelProved
    Intertwiner.Existing.canonicalPhysicalSSPHeckeModelClosureReceipt
  ≡ false
existingCarrierEqualityStillOpen = Intertwiner.existingCarrierEqualityStillOpen

classicalIntertwinerStillOpen :
  Intertwiner.witnessConstructed
    Intertwiner.canonicalSSPRepresentationModularIntertwinerTarget
  ≡ false
classicalIntertwinerStillOpen = refl

modularGenusZeroNotManufacturedHere :
  Modular.genusZeroIsInternallyProved Modular.canonicalModularCurveBoundary
  ≡ false
modularGenusZeroNotManufacturedHere = refl

sevenSevenOneIsNotSelector :
  Seven.sevenSevenOneUsedAsSSPSelector Seven.canonicalTernarySevenOggSSPBoundary
  ≡ false
sevenSevenOneIsNotSelector = refl

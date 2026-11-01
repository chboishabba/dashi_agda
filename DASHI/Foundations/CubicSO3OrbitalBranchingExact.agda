module DASHI.Foundations.CubicSO3OrbitalBranchingExact where

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
-- Expose the first low-angular-momentum SO(3) -> rotational-octahedral
-- branchings as exact orbital examples.  With O ~= S4 and irrep order
-- (A1,A2,E,T1,T2):
--
--   l=1, dim 3 : T1
--   l=2, dim 5 : E + T2
--   l=3, dim 7 : A2 + T1 + T2
--   l=4, dim 9 : A1 + E + T1 + T2.
--
-- Thus the seven-state f-wave carrier has an actual 1+3+3 cubic splitting.
-- The nine-state l=4 carrier has a different 1+2+3+3 cubic splitting, while
-- its rotational-D4 restriction (in D4SO3NineIrrepRestrictionExact) contains
-- all five D4 irrep species.  These are different restriction lenses on the
-- same continuous SO(3) carrier, not interchangeable partitions of an integer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4Kind

pWaveDimensionIsThree : Spin.jDimension Spin.j1 ≡ 3
pWaveDimensionIsThree = refl

pWaveCubicBranching :
  Oct.branchingSpectrum Spin.j1
  ≡ Oct.oct-spectrum 0 0 0 1 0
pWaveCubicBranching = refl

dWaveDimensionIsFive : Spin.jDimension Spin.j2 ≡ 5
dWaveDimensionIsFive = refl

dWaveCubicBranching :
  Oct.branchingSpectrum Spin.j2
  ≡ Oct.oct-spectrum 0 0 1 0 1
dWaveCubicBranching = refl

fWaveDimensionIsSeven : Spin.jDimension Spin.j3 ≡ 7
fWaveDimensionIsSeven = refl

fWaveCubicBranching :
  Oct.branchingSpectrum Spin.j3
  ≡ Oct.oct-spectrum 0 1 0 1 1
fWaveCubicBranching = refl

fWaveCubicDimensionsSumToSeven :
  Oct.octahedralIrrepDimension Oct.A2
  + Oct.octahedralIrrepDimension Oct.T1
  + Oct.octahedralIrrepDimension Oct.T2
  ≡ 7
fWaveCubicDimensionsSumToSeven = refl

gWaveDimensionIsNine : Spin.jDimension Spin.j4 ≡ 9
gWaveDimensionIsNine = refl

gWaveCubicBranching :
  Oct.branchingSpectrum Spin.j4
  ≡ Oct.oct-spectrum 1 0 1 1 1
gWaveCubicBranching = refl

gWaveCubicDimensionsSumToNine :
  Oct.octahedralIrrepDimension Oct.A1
  + Oct.octahedralIrrepDimension Oct.E
  + Oct.octahedralIrrepDimension Oct.T1
  + Oct.octahedralIrrepDimension Oct.T2
  ≡ 9
gWaveCubicDimensionsSumToNine = refl

------------------------------------------------------------------------
-- The same nine-dimensional V_4 under rotational D4 contains all five D4
-- irrep species.  This makes the dependence on the chosen reduction lens
-- explicit rather than treating "five irreps of nine" as an intrinsic fact of
-- the integer nine.
------------------------------------------------------------------------

gWaveD4A1Present : D4.j4D4Multiplicity D4Kind.A1 ≡ 2
gWaveD4A1Present = D4.allFiveSpeciesPresentA1

gWaveD4A2Present : D4.j4D4Multiplicity D4Kind.A2 ≡ 1
gWaveD4A2Present = D4.allFiveSpeciesPresentA2

gWaveD4B1Present : D4.j4D4Multiplicity D4Kind.B1 ≡ 1
gWaveD4B1Present = D4.allFiveSpeciesPresentB1

gWaveD4B2Present : D4.j4D4Multiplicity D4Kind.B2 ≡ 1
gWaveD4B2Present = D4.allFiveSpeciesPresentB2

gWaveD4EPresent : D4.j4D4Multiplicity D4Kind.E2 ≡ 2
gWaveD4EPresent = D4.allFiveSpeciesPresentE

record CubicOrbitalBranchingBoundary : Set where
  field
    fWaveSevenSplittingConstructed : Bool
    fWaveSevenSplittingConstructedIsTrue :
      fWaveSevenSplittingConstructed ≡ true

    gWaveNineCubicSplittingConstructed : Bool
    gWaveNineCubicSplittingConstructedIsTrue :
      gWaveNineCubicSplittingConstructed ≡ true

    sameNineCarrierHasFiveSpeciesUnderD4 : Bool
    sameNineCarrierHasFiveSpeciesUnderD4IsTrue :
      sameNineCarrierHasFiveSpeciesUnderD4 ≡ true

    branchingDependsOnReductionLens : Bool
    branchingDependsOnReductionLensIsTrue :
      branchingDependsOnReductionLens ≡ true

    dimensionAloneDeterminesBranching : Bool
    dimensionAloneDeterminesBranchingIsFalse :
      dimensionAloneDeterminesBranching ≡ false

canonicalCubicOrbitalBranchingBoundary : CubicOrbitalBranchingBoundary
canonicalCubicOrbitalBranchingBoundary =
  record
    { fWaveSevenSplittingConstructed = true
    ; fWaveSevenSplittingConstructedIsTrue = refl
    ; gWaveNineCubicSplittingConstructed = true
    ; gWaveNineCubicSplittingConstructedIsTrue = refl
    ; sameNineCarrierHasFiveSpeciesUnderD4 = true
    ; sameNineCarrierHasFiveSpeciesUnderD4IsTrue = refl
    ; branchingDependsOnReductionLens = true
    ; branchingDependsOnReductionLensIsTrue = refl
    ; dimensionAloneDeterminesBranching = false
    ; dimensionAloneDeterminesBranchingIsFalse = refl
    }

module DASHI.Physics.YangMills.BalabanCMP109WalshFourOrbitFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.  Section 5, equations (5.6)--(5.8).
--
-- DASHI CONTRIBUTION
--
-- Compose two theorem-producing reductions that previously sat beside one
-- another:
--
--   source reflection covariance -> all nontrivial (C2)^4 Walsh sectors vanish
--   source permutation covariance -> 240 regular cells -> four representatives
--
-- Thus once the literal Wilson/FP/Haar scalar expression is identified with
-- Bałaban's scalar vacuum-polarisation projection, no nontrivial sign sector
-- needs Bishop interval evaluation at all; intervalisation starts on the four
-- trivial-character orbit representatives.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _/_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicRepresentativeSumExact as FourOrbit
import DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact as Source
import DASHI.Physics.YangMills.BalabanCMP109WalshCharacterOrbitCancellationExact as Character

sourceSymmetryRegularSumIsFourTrivialRepresentatives :
  ∀ {contribution : Grid.GridCell4 → ℚ} →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  Sums.sumRational Grid.regularGridCells contribution
  ≡ (+ 64 / 1) * contribution Orbit.oneOuterRepresentative
    + (+ 96 / 1) * contribution Orbit.twoOuterRepresentative
    + (+ 64 / 1) * contribution Orbit.threeOuterRepresentative
    + (+ 16 / 1) * contribution Orbit.fourOuterRepresentative
sourceSymmetryRegularSumIsFourTrivialRepresentatives symmetry =
  FourOrbit.regularInvariantSumIsFourRepresentatives
    (Source.asGeneratorInvariant symmetry)

sourceSymmetryKillsEveryNontrivialSignSector :
  ∀ {contribution : Grid.GridCell4 → ℚ}
    {character : Cube.Subset4} →
  Source.CMP109ScalarEuclideanSymmetry contribution →
  Walsh.NontrivialWalshCharacter character →
  (cell : Grid.GridCell4) →
  Character.signedOrbitWalshCoefficient contribution character cell
  ≡ 0ℚ
sourceSymmetryKillsEveryNontrivialSignSector =
  Character.nontrivialSignedOrbitCharacterVanishes

record CMP109WalshFourOrbitBoundary : Set where
  field
    nontrivialSignSectorsKilledBeforeIntervals : ProofLevel
    fourGeometricRepresentativesRemain : ProofLevel
    literalScalarSameObjectIdentification : ProofLevel

canonicalCMP109WalshFourOrbitBoundary : CMP109WalshFourOrbitBoundary
canonicalCMP109WalshFourOrbitBoundary = record
  { nontrivialSignSectorsKilledBeforeIntervals = machineChecked
  ; fourGeometricRepresentativesRemain = machineChecked
  ; literalScalarSameObjectIdentification = conditional
  }

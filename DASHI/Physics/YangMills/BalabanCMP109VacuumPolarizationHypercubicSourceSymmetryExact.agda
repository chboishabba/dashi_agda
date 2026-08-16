module DASHI.Physics.YangMills.BalabanCMP109VacuumPolarizationHypercubicSourceSymmetryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Direct source locators: Section 5, equations (5.2)--(5.8).
-- In particular, (5.6) is the coordinate-permutation covariance of the vacuum
-- polarization tensor and (5.7) is its coordinate-reflection covariance.
-- Translation invariance and tensor symmetry are stated in (5.8).
--
-- DASHI CONTRIBUTION
--
-- The generated-grid orbit proof should not ask the Wilson, ghost, tadpole and
-- Haar pieces for seven independent symmetry receipts.  Bałaban proves the
-- Euclidean covariance for the FULL vacuum-polarization tensor before the beta
-- coefficient is extracted.  This module therefore packages only the two
-- source laws -- arbitrary coordinate reflection and adjacent coordinate
-- permutation -- and derives invariance under the seven concrete B_4
-- generators used by Round57.
--
-- The remaining physical leaf is consequently source identification:
-- show that the rational/Bishop scalar contribution being intervalized is the
-- scalar projection of Bałaban's literal tensor to which (5.6),(5.7) apply.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action

-- Coordinate reflections and adjacent transpositions are exactly the source
-- generators needed to instantiate (5.7) and (5.6), respectively.
data ReflectionAxis : Set where
  reflect0 reflect1 reflect2 reflect3 : ReflectionAxis

data AdjacentPermutation : Set where
  permute01 permute12 permute23 : AdjacentPermutation

reflectionGenerator : ReflectionAxis → Action.HypercubicGenerator
reflectionGenerator reflect0 = Action.flip0
reflectionGenerator reflect1 = Action.flip1
reflectionGenerator reflect2 = Action.flip2
reflectionGenerator reflect3 = Action.flip3

permutationGenerator : AdjacentPermutation → Action.HypercubicGenerator
permutationGenerator permute01 = Action.swap01
permutationGenerator permute12 = Action.swap12
permutationGenerator permute23 = Action.swap23

record CMP109ScalarEuclideanSymmetry
    (contribution : Grid.GridCell4 → ℚ) : Set where
  field
    -- Source (5.7), after scalar projection: arbitrary coordinate reflection.
    reflectionInvariant : ∀ axis cell →
      contribution cell
      ≡ contribution (Action.act (reflectionGenerator axis) cell)

    -- Source (5.6), after scalar projection: arbitrary adjacent permutation.
    -- Adjacent transpositions generate every coordinate permutation.
    permutationInvariant : ∀ permutation cell →
      contribution cell
      ≡ contribution (Action.act (permutationGenerator permutation) cell)

open CMP109ScalarEuclideanSymmetry public

asGeneratorInvariant : ∀ {contribution} →
  CMP109ScalarEuclideanSymmetry contribution →
  Action.GeneratorInvariantRationalContribution contribution
asGeneratorInvariant symmetry = record
  { generatorInvariant = generatorInvariantProof }
  where
  generatorInvariantProof : ∀ generator cell →
    _ ≡ _
  generatorInvariantProof Action.flip0 cell =
    reflectionInvariant symmetry reflect0 cell
  generatorInvariantProof Action.flip1 cell =
    reflectionInvariant symmetry reflect1 cell
  generatorInvariantProof Action.flip2 cell =
    reflectionInvariant symmetry reflect2 cell
  generatorInvariantProof Action.flip3 cell =
    reflectionInvariant symmetry reflect3 cell
  generatorInvariantProof Action.swap01 cell =
    permutationInvariant symmetry permute01 cell
  generatorInvariantProof Action.swap12 cell =
    permutationInvariant symmetry permute12 cell
  generatorInvariantProof Action.swap23 cell =
    permutationInvariant symmetry permute23 cell

sourceEuclideanSymmetryGivesFourOrbitReduction :
  ∀ {contribution}
    (symmetry : CMP109ScalarEuclideanSymmetry contribution)
    cell →
  contribution cell
  ≡ contribution (Action.representative (Orbit.orbitClass cell))
sourceEuclideanSymmetryGivesFourOrbitReduction symmetry cell =
  Action.cellContributionEqualsOrbitRepresentative
    (asGeneratorInvariant symmetry) cell

cmp109EuclideanSourceToHypercubicGeneratorsLevel : ProofLevel
cmp109EuclideanSourceToHypercubicGeneratorsLevel = machineChecked

-- Physical leaf: instantiate the two source laws for the actual scalar
-- Wilson+ghost+tadpole+Haar contribution used by the box evaluator.
cmp109LiteralVacuumPolarizationScalarProjectionSymmetryLevel : ProofLevel
cmp109LiteralVacuumPolarizationScalarProjectionSymmetryLevel = conditional

module DASHI.Foundations.TernaryNineAntipodalD4SeparationExact where

------------------------------------------------------------------------
-- SOURCE / REPRESENTATION CALIBRATION
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer. DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- The strict antipodal quotient of a nine-state balanced-ternary plane has
-- five orbit classes.  D4 also has five irrep species in the repository.
-- Equal count does not identify those two classifications.  The existing
-- source-native falsifier is stronger: the raw D4 permutation representation
-- on nine cells has A2 multiplicity zero, while the SO(3) j=4 restriction has
-- A2 multiplicity one.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.D4SO3NineIrrepRestrictionExact as D4

antipodalNineClassCount : Nat
antipodalNineClassCount = Orbit.antipodalClass9Count

antipodalNineClassCountIsFive : antipodalNineClassCount ≡ 5
antipodalNineClassCountIsFive = Orbit.antipodalClass9CountIsFive

d4IrrepSpeciesCount : Nat
d4IrrepSpeciesCount = 5

d4IrrepSpeciesCountIsFive : d4IrrepSpeciesCount ≡ 5
d4IrrepSpeciesCountIsFive = refl

rawNineA2Absent : Candidate.rawNineMultiplicity Candidate.A2 ≡ 0
rawNineA2Absent = Candidate.rawA2MultiplicityIsZero

j4RestrictionA2Present : D4.j4D4Multiplicity Candidate.A2 ≡ 1
j4RestrictionA2Present = D4.j4RestrictionA2IsPresent

sameNineDimensionDoesNotIdentifyRepresentations :
  ((kind : Candidate.D4IrrepKind) →
    Candidate.rawNineMultiplicity kind ≡ D4.j4D4Multiplicity kind) →
  ⊥
sameNineDimensionDoesNotIdentifyRepresentations =
  D4.rawNinePermutationIsNotJ4Restriction

record TernaryNineAntipodalD4Boundary : Set where
  field
    fiveAntipodalOrbitClassesAreFiveD4IrrepSpecies : Bool
    equalNineDimensionsIdentifyRepresentations : Bool
    missingA2CanBeRecoveredFromCardinalityAlone : Bool

canonicalTernaryNineAntipodalD4Boundary : TernaryNineAntipodalD4Boundary
canonicalTernaryNineAntipodalD4Boundary = record
  { fiveAntipodalOrbitClassesAreFiveD4IrrepSpecies = false
  ; equalNineDimensionsIdentifyRepresentations = false
  ; missingA2CanBeRecoveredFromCardinalityAlone = false
  }

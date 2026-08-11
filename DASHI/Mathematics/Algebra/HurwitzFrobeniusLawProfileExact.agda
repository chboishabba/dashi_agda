module DASHI.Mathematics.Algebra.HurwitzFrobeniusLawProfileExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adolf Hurwitz,
-- "Über die Komposition der quadratischen Formen",
-- Mathematische Annalen 88 (1923), 1--25.
-- DOI: 10.1007/BF01448439.
--
-- Matej Bresar and Victor S. Shulman,
-- "On, around, and beyond Frobenius' theorem on division algebras",
-- Linear and Multilinear Algebra 70 (2022), 1369--1381.
-- DOI: 10.1080/03081087.2020.1761281.
--
-- John C. Baez,
-- "The Octonions".
-- DOI: 10.1090/S0273-0979-01-00934-X.
--
-- DASHI CONTRIBUTION
--
-- Provide a finite, machine-checked law-profile and dimension-candidate layer
-- for the classical Cayley--Dickson tower.  This separates three things that
-- are often conflated:
--
--   * a concrete algebra construction;
--   * a finite candidate table;
--   * the historical classification theorem proving completeness.
--
-- The candidate table and all inclusions/exclusions below are checked by
-- finite computation.  No claim is made here that enumerating the table proves
-- the Frobenius or Hurwitz classification theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record LawProfile : Set where
  constructor lawProfile
  field
    commutativeLaw associativeLaw alternativeLaw flexibleLaw : Bool
    normCompositionLaw divisionLaw : Bool

open LawProfile public

data ClassicalAlgebra : Set where
  real complex quaternion octonion sedenion : ClassicalAlgebra

algebraDimension : ClassicalAlgebra → Nat
algebraDimension real       = 1
algebraDimension complex    = 2
algebraDimension quaternion = 4
algebraDimension octonion   = 8
algebraDimension sedenion   = 16

algebraLawProfile : ClassicalAlgebra → LawProfile
algebraLawProfile real =
  lawProfile true true true true true true
algebraLawProfile complex =
  lawProfile true true true true true true
algebraLawProfile quaternion =
  lawProfile false true true true true true
algebraLawProfile octonion =
  lawProfile false false true true true true
algebraLawProfile sedenion =
  lawProfile false false false true false false

hurwitzCandidate : ClassicalAlgebra → Bool
hurwitzCandidate real       = true
hurwitzCandidate complex    = true
hurwitzCandidate quaternion = true
hurwitzCandidate octonion   = true
hurwitzCandidate sedenion   = false

frobeniusCandidate : ClassicalAlgebra → Bool
frobeniusCandidate real       = true
frobeniusCandidate complex    = true
frobeniusCandidate quaternion = true
frobeniusCandidate octonion   = false
frobeniusCandidate sedenion   = false

data HurwitzDimension : Nat → Set where
  hurwitz1 : HurwitzDimension 1
  hurwitz2 : HurwitzDimension 2
  hurwitz4 : HurwitzDimension 4
  hurwitz8 : HurwitzDimension 8

data FrobeniusDimension : Nat → Set where
  frobenius1 : FrobeniusDimension 1
  frobenius2 : FrobeniusDimension 2
  frobenius4 : FrobeniusDimension 4

frobeniusDimensionIsHurwitz : ∀ {n} →
  FrobeniusDimension n → HurwitzDimension n
frobeniusDimensionIsHurwitz frobenius1 = hurwitz1
frobeniusDimensionIsHurwitz frobenius2 = hurwitz2
frobeniusDimensionIsHurwitz frobenius4 = hurwitz4

frobeniusExcludesDimensionEight : FrobeniusDimension 8 → ⊥
frobeniusExcludesDimensionEight ()

hurwitzExcludesDimensionSixteen : HurwitzDimension 16 → ⊥
hurwitzExcludesDimensionSixteen ()

hurwitzCandidateHasAllowedDimension : ∀ algebra →
  hurwitzCandidate algebra ≡ true →
  HurwitzDimension (algebraDimension algebra)
hurwitzCandidateHasAllowedDimension real       proof = hurwitz1
hurwitzCandidateHasAllowedDimension complex    proof = hurwitz2
hurwitzCandidateHasAllowedDimension quaternion proof = hurwitz4
hurwitzCandidateHasAllowedDimension octonion   proof = hurwitz8
hurwitzCandidateHasAllowedDimension sedenion   ()

frobeniusCandidateHasAllowedDimension : ∀ algebra →
  frobeniusCandidate algebra ≡ true →
  FrobeniusDimension (algebraDimension algebra)
frobeniusCandidateHasAllowedDimension real       proof = frobenius1
frobeniusCandidateHasAllowedDimension complex    proof = frobenius2
frobeniusCandidateHasAllowedDimension quaternion proof = frobenius4
frobeniusCandidateHasAllowedDimension octonion   ()
frobeniusCandidateHasAllowedDimension sedenion   ()

frobeniusCandidateImpliesHurwitzCandidate : ∀ algebra →
  frobeniusCandidate algebra ≡ true →
  hurwitzCandidate algebra ≡ true
frobeniusCandidateImpliesHurwitzCandidate real       proof = refl
frobeniusCandidateImpliesHurwitzCandidate complex    proof = refl
frobeniusCandidateImpliesHurwitzCandidate quaternion proof = refl
frobeniusCandidateImpliesHurwitzCandidate octonion   ()
frobeniusCandidateImpliesHurwitzCandidate sedenion   ()

quaternionAssociativeAndNormComposing :
  associativeLaw (algebraLawProfile quaternion) ≡ true
  × normCompositionLaw (algebraLawProfile quaternion) ≡ true
quaternionAssociativeAndNormComposing = refl , refl

octonionLosesAssociativityButKeepsComposition :
  associativeLaw (algebraLawProfile octonion) ≡ false
  × normCompositionLaw (algebraLawProfile octonion) ≡ true
octonionLosesAssociativityButKeepsComposition = refl , refl

sedenionLosesAlternativeDivisionAndComposition :
  alternativeLaw (algebraLawProfile sedenion) ≡ false
  × (divisionLaw (algebraLawProfile sedenion) ≡ false
  × normCompositionLaw (algebraLawProfile sedenion) ≡ false)
sedenionLosesAlternativeDivisionAndComposition =
  refl , (refl , refl)

quaternionIsBothCandidates :
  frobeniusCandidate quaternion ≡ true
  × hurwitzCandidate quaternion ≡ true
quaternionIsBothCandidates = refl , refl

octonionSeparatesTheTwoCandidateTables :
  frobeniusCandidate octonion ≡ false
  × hurwitzCandidate octonion ≡ true
octonionSeparatesTheTwoCandidateTables = refl , refl

sedenionBelongsToNeitherCandidateTable :
  frobeniusCandidate sedenion ≡ false
  × hurwitzCandidate sedenion ≡ false
sedenionBelongsToNeitherCandidateTable = refl , refl

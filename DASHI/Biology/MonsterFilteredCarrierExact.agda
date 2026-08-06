module DASHI.Biology.MonsterFilteredCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Robert L. Griess,
-- "The Friendly Giant", Inventiones Mathematicae 69 (1982), 1--102.
-- DOI: 10.1007/BF01389186.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- DASHI CONTRIBUTION
--
-- Represent 196883 as the dimension of an associated-graded candidate, not
-- as a claimed Monster branching rule.  The former tenfold bulk notation is
-- refined into
--
--   3^11 + 3^9 = 177147 + 19683 = 196830,
--
-- corresponding to nine ordinary balanced-ternary coarse channels and one
-- structurally distinct j completion channel, each carrying the same 3^9
-- fine-frequency carrier.  The 53-dimensional term is the reduced quotient
-- V54 / 1.  No displayed piece is declared Monster-invariant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat using (_+_)

ordinaryHarmonicBulk : Nat
ordinaryHarmonicBulk = 177147

completionJHarmonicBulk : Nat
completionJHarmonicBulk = 19683

structuredBulkDimension : Nat
structuredBulkDimension = ordinaryHarmonicBulk + completionJHarmonicBulk

reducedDimension : Nat
reducedDimension = 53

totalCandidateDimension : Nat
totalCandidateDimension = structuredBulkDimension + reducedDimension

structuredBulkDimensionExact : structuredBulkDimension ≡ 196830
structuredBulkDimensionExact = refl

totalCandidateDimensionExact : totalCandidateDimension ≡ 196883
totalCandidateDimensionExact = refl

record FilteredDimension : Set where
  constructor filteredDimension
  field
    lowerPiece : Nat
    upperQuotient : Nat
    total : Nat
    totalIsExtension : total ≡ lowerPiece + upperQuotient

open FilteredDimension public

dashIFilteredCarrier : FilteredDimension
dashIFilteredCarrier =
  filteredDimension structuredBulkDimension reducedDimension 196883 refl

record AssociatedGradedCandidate : Set where
  constructor associatedGradedCandidate
  field
    ordinaryPieceDimension : Nat
    completionPieceDimension : Nat
    reducedPieceDimension : Nat
    gradedTotalDimension : Nat
    gradedDimensionExact :
      gradedTotalDimension
      ≡ ordinaryPieceDimension
        + completionPieceDimension
        + reducedPieceDimension

open AssociatedGradedCandidate public

dashIAssociatedGraded : AssociatedGradedCandidate
dashIAssociatedGraded =
  associatedGradedCandidate 177147 19683 53 196883 refl

record ReductionOrigin : Set where
  constructor reductionOrigin
  field
    unreducedDimension : Nat
    trivialMultiplicity : Nat
    quotientDimension : Nat
    unreducedSplits :
      unreducedDimension ≡ trivialMultiplicity + quotientDimension

open ReductionOrigin public

sixByNineReductionOrigin : ReductionOrigin
sixByNineReductionOrigin = reductionOrigin 54 1 53 refl

record FilteredCarrierBoundary : Set where
  constructor filteredCarrierBoundary
  field
    arithmeticIdentityChecked : Bool
    arithmeticIdentityCheckedIsTrue : arithmeticIdentityChecked ≡ true

    structuredAssociatedGradedConstructed : Bool
    structuredAssociatedGradedConstructedIsTrue :
      structuredAssociatedGradedConstructed ≡ true

    tenIsPrimitiveSymmetryMultiplicity : Bool
    tenIsPrimitiveSymmetryMultiplicityIsFalse :
      tenIsPrimitiveSymmetryMultiplicity ≡ false

    gradedPiecesAreMonsterInvariant : Bool
    gradedPiecesAreMonsterInvariantIsFalse :
      gradedPiecesAreMonsterInvariant ≡ false

    publishedMonsterBranchingRuleObtained : Bool
    publishedMonsterBranchingRuleObtainedIsFalse :
      publishedMonsterBranchingRuleObtained ≡ false

    fullMonsterActionConstructed : Bool
    fullMonsterActionConstructedIsFalse :
      fullMonsterActionConstructed ≡ false

canonicalFilteredCarrierBoundary : FilteredCarrierBoundary
canonicalFilteredCarrierBoundary =
  filteredCarrierBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

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
-- Represent 196883 = 10 * 3^9 + 53 as the dimension of an associated-graded
-- candidate, not as a claimed Monster branching rule.  The 53-dimensional
-- term is the reduced quotient V54 / 1, equivalently V54 minus one declared
-- trivial summand in the representation ring.  The filtration may be mixed
-- by a later total action; no graded piece is declared Monster-invariant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

pow3nine : Nat
pow3nine = 19683

bulkMultiplicity : Nat
bulkMultiplicity = 10

reducedDimension : Nat
reducedDimension = 53

totalCandidateDimension : Nat
totalCandidateDimension = bulkMultiplicity * pow3nine + reducedDimension

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
  filteredDimension (bulkMultiplicity * pow3nine) reducedDimension 196883 refl

record AssociatedGradedCandidate : Set where
  constructor associatedGradedCandidate
  field
    bulkPieceDimension : Nat
    reducedPieceDimension : Nat
    gradedTotalDimension : Nat
    gradedDimensionExact :
      gradedTotalDimension ≡ bulkPieceDimension + reducedPieceDimension

open AssociatedGradedCandidate public

dashIAssociatedGraded : AssociatedGradedCandidate
dashIAssociatedGraded =
  associatedGradedCandidate
    (bulkMultiplicity * pow3nine)
    reducedDimension
    196883
    refl

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

    associatedGradedStructureConstructed : Bool
    associatedGradedStructureConstructedIsTrue :
      associatedGradedStructureConstructed ≡ true

    gradedPiecesAreMonsterInvariant : Bool
    gradedPiecesAreMonsterInvariantIsFalse :
      gradedPiecesAreMonsterInvariant ≡ false

    publishedMonsterBranchingRuleObtained : Bool
    publishedMonsterBranchingRuleObtainedIsFalse :
      publishedMonsterBranchingRuleObtained ≡ false

    fullMonsterActionConstructed : Bool
    fullMonsterActionConstructedIsFalse :
      fullMonsterActionConstructed ≡ false

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalFilteredCarrierBoundary : FilteredCarrierBoundary
canonicalFilteredCarrierBoundary =
  filteredCarrierBoundary true refl true refl false refl false refl false refl

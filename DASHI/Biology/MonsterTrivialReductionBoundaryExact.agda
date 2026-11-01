module DASHI.Biology.MonsterTrivialReductionBoundaryExact where

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
-- J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker and R. A. Wilson,
-- "Atlas of Finite Groups", Oxford University Press, 1985.
-- ISBN: 978-0-19-853199-9. No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- State the exact authority boundary requested in the thread:
--
--   V54 = 1 + V53-reduced
--
-- means removal of one declared trivial representation.  It neither treats
-- 53 as a bare remainder nor declares V53-reduced to be a nontrivial Monster
-- irreducible.  The standard Monster order/character data are recorded only
-- as imported scope facts, not re-proved in Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

record TrivialReduction : Set where
  constructor trivialReduction
  field
    carrierDimension : Nat
    trivialDimension : Nat
    reducedDimension : Nat
    carrierDimensionExact :
      carrierDimension ≡ trivialDimension + reducedDimension

open TrivialReduction public

sixByNineTrivialReduction : TrivialReduction
sixByNineTrivialReduction = trivialReduction 54 1 53 refl

data ReductionInterpretation : Set where
  representationRingSubtraction : ReductionInterpretation
  orthogonalInvariantLineRemoval : ReductionInterpretation
  quotientByInvariantLine : ReductionInterpretation
  arbitraryArithmeticRemainder : ReductionInterpretation
  standaloneMonsterIrrep : ReductionInterpretation

intendedInterpretation : ReductionInterpretation
intendedInterpretation = representationRingSubtraction

intendedInterpretationExact :
  intendedInterpretation ≡ representationRingSubtraction
intendedInterpretationExact = refl

record MonsterReductionBoundary : Set where
  constructor monsterReductionBoundary
  field
    minusOneRemovesDeclaredTrivialRepresentation : Bool
    minusOneRemovesDeclaredTrivialRepresentationIsTrue :
      minusOneRemovesDeclaredTrivialRepresentation ≡ true

    fiftyThreeIsBareRemainder : Bool
    fiftyThreeIsBareRemainderIsFalse :
      fiftyThreeIsBareRemainder ≡ false

    fiftyThreeIsClaimedMonsterIrrep : Bool
    fiftyThreeIsClaimedMonsterIrrepIsFalse :
      fiftyThreeIsClaimedMonsterIrrep ≡ false

    standardMonsterDataExcludeNontrivialDegree53Irrep : Bool
    standardMonsterDataExcludeNontrivialDegree53IrrepIsTrue :
      standardMonsterDataExcludeNontrivialDegree53Irrep ≡ true

    exclusionRulesOutMixedOrFilteredWholeCarrier : Bool
    exclusionRulesOutMixedOrFilteredWholeCarrierIsFalse :
      exclusionRulesOutMixedOrFilteredWholeCarrier ≡ false

canonicalMonsterReductionBoundary : MonsterReductionBoundary
canonicalMonsterReductionBoundary =
  monsterReductionBoundary true refl false refl false refl true refl false refl

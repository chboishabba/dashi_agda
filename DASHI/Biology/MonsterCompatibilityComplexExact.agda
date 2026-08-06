module DASHI.Biology.MonsterCompatibilityComplexExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras",
-- Inventiones Mathematicae 109 (1992), 405--444.
-- DOI: 10.1007/BF01232032.
--
-- Elizabeth Jurisich, James Lepowsky and Robert L. Wilson,
-- "Realizations of the Monster Lie Algebra", Selecta Mathematica,
-- New Series 1 (1995), 129--161. arXiv:hep-th/9408037.
-- DOI not asserted here without a repository-verified primary record.
--
-- DASHI CONTRIBUTION
--
-- Formalize the route in which the displayed 10 * 3^9 plus reduced-53
-- coordinates are input data to a compatibility differential.  A later
-- Monster-relevant object may be a kernel, quotient, image, cohomology object,
-- or completion; the displayed pieces therefore need not be invariant
-- summands of the final action.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

record FiniteComplexDimensions : Set where
  constructor finiteComplexDimensions
  field
    sourceDimension : Nat
    relationDimension : Nat
    kernelDimension : Nat
    imageDimension : Nat
    sourceSplitsKernelImage :
      sourceDimension ≡ kernelDimension + imageDimension

open FiniteComplexDimensions public

------------------------------------------------------------------------
-- This is only a dimension-level witness showing how a 196883-dimensional
-- source can feed a relation map without forcing its displayed 53 coordinates
-- to survive as an invariant final summand.
------------------------------------------------------------------------

dashICompatibilityDimensions : FiniteComplexDimensions
dashICompatibilityDimensions =
  finiteComplexDimensions 196883 53 196830 53 refl

bulkTenTernaryDimension : Nat
bulkTenTernaryDimension = 10 * 19683

bulkTenTernaryDimensionExact : bulkTenTernaryDimension ≡ 196830
bulkTenTernaryDimensionExact = refl

sourceDimensionExact :
  sourceDimension dashICompatibilityDimensions
  ≡ bulkTenTernaryDimension + 53
sourceDimensionExact = refl

------------------------------------------------------------------------
-- Typed outcomes of a compatibility program.
------------------------------------------------------------------------

data CompatibilityOutcome : Set where
  kernelObject : CompatibilityOutcome
  quotientObject : CompatibilityOutcome
  cohomologyObject : CompatibilityOutcome
  completedObject : CompatibilityOutcome

record CompatibilityRoute : Set where
  constructor compatibilityRoute
  field
    outcome : CompatibilityOutcome
    displayedReducedPieceSurvivesAsInvariantSummand : Bool
    displayedReducedPieceSurvivesAsInvariantSummandIsFalse :
      displayedReducedPieceSurvivesAsInvariantSummand ≡ false
    finalMonsterActionConstructed : Bool
    finalMonsterActionConstructedIsFalse :
      finalMonsterActionConstructed ≡ false

open CompatibilityRoute public

kernelRoute : CompatibilityRoute
kernelRoute = compatibilityRoute kernelObject false refl false refl

quotientRoute : CompatibilityRoute
quotientRoute = compatibilityRoute quotientObject false refl false refl

cohomologyRoute : CompatibilityRoute
cohomologyRoute = compatibilityRoute cohomologyObject false refl false refl

completionRoute : CompatibilityRoute
completionRoute = compatibilityRoute completedObject false refl false refl

record CompatibilityBoundary : Set where
  constructor compatibilityBoundary
  field
    dimensionAccountingIsExact : Bool
    dimensionAccountingIsExactIsTrue : dimensionAccountingIsExact ≡ true
    actualDifferentialConstructed : Bool
    actualDifferentialConstructedIsFalse : actualDifferentialConstructed ≡ false
    actualCohomologyComputed : Bool
    actualCohomologyComputedIsFalse : actualCohomologyComputed ≡ false

canonicalCompatibilityBoundary : CompatibilityBoundary
canonicalCompatibilityBoundary =
  compatibilityBoundary true refl false refl false refl

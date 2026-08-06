module DASHI.Biology.MonsterSubgroupBranchingBenchmarksExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. H. Conway,
-- "A Simple Construction for the Fischer-Griess Monster Group",
-- Inventiones Mathematicae 79 (1985), 513--540.
-- DOI: 10.1007/BF01388521.
--
-- Stephen Linton, Richard Parker, Peter Walsh and Robert A. Wilson,
-- "Computer Construction of the Monster",
-- Journal of Group Theory 1 (1998), 307--337.
-- DOI: 10.1515/jgth.1998.023.
--
-- Robert A. Wilson,
-- "New Computations in the Monster",
-- in Moonshine: The First Quarter Century and Beyond (2010), 393--403.
-- DOI: 10.1017/CBO9780511730054.019.
--
-- DASHI CONTRIBUTION
--
-- Record two genuine subgroup-level decomposition templates against which the
-- filtered DASHI carrier can be tested.  These are benchmarks, not evidence
-- that the proposed 10 * 3^9 + 53 grading occurs in the Monster.
--
-- For the centralizer 2.B of a 2A involution, the 196883-dimensional
-- constituent restricts with dimensions
--
--   1 + 4371 + 96255 + 96256 = 196883.
--
-- For the 2-local subgroup 2_+^(1+24).Co1, the 196884-dimensional ordinary
-- representation restricts as
--
--   (2^12 tensor 24) + 98280 + 300 = 196884.
--
-- The point is structural: full-Monster irreducibility is compatible with
-- decomposable coordinates after restriction, tensor/multiplicity blocks,
-- and later mixing by elements outside the chosen subgroup.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)

record BranchingBenchmark : Set where
  constructor branchingBenchmark
  field
    ambientDimension : Nat
    firstPiece : Nat
    secondPiece : Nat
    thirdPiece : Nat
    fourthPiece : Nat
    piecesSum :
      ambientDimension
      ≡ firstPiece + secondPiece + thirdPiece + fourthPiece

open BranchingBenchmark public

babyMonsterCentralizerBenchmark : BranchingBenchmark
babyMonsterCentralizerBenchmark =
  branchingBenchmark 196883 1 4371 96255 96256 refl

babyMonsterRestrictionDimensionExact :
  ambientDimension babyMonsterCentralizerBenchmark
  ≡ firstPiece babyMonsterCentralizerBenchmark
    + secondPiece babyMonsterCentralizerBenchmark
    + thirdPiece babyMonsterCentralizerBenchmark
    + fourthPiece babyMonsterCentralizerBenchmark
babyMonsterRestrictionDimensionExact =
  piecesSum babyMonsterCentralizerBenchmark

record TensorBranchingBenchmark : Set where
  constructor tensorBranchingBenchmark
  field
    ambientTensorDimension : Nat
    tensorLeft : Nat
    tensorRight : Nat
    residualFirst : Nat
    residualSecond : Nat
    tensorPiecesSum :
      ambientTensorDimension
      ≡ tensorLeft * tensorRight + residualFirst + residualSecond

open TensorBranchingBenchmark public

conwayTwoLocalBenchmark : TensorBranchingBenchmark
conwayTwoLocalBenchmark =
  tensorBranchingBenchmark 196884 4096 24 98280 300 refl

conwayTwoLocalDimensionExact :
  ambientTensorDimension conwayTwoLocalBenchmark
  ≡ tensorLeft conwayTwoLocalBenchmark
    * tensorRight conwayTwoLocalBenchmark
    + residualFirst conwayTwoLocalBenchmark
    + residualSecond conwayTwoLocalBenchmark
conwayTwoLocalDimensionExact =
  tensorPiecesSum conwayTwoLocalBenchmark

------------------------------------------------------------------------
-- Falsifiable subgroup-candidate protocol.
------------------------------------------------------------------------

record CandidateSubgroupTest : Set where
  constructor candidateSubgroupTest
  field
    subgroupNamed : Set
    embeddingWitness : Set
    knownAmbientRepresentationNamed : Set
    restrictionCharacterComputed : Set
    proposedFiltrationPreserved : Set
    associatedGradedDimensionsMatched : Set
    outsideElementMixingChecked : Set

-- No candidate H has yet discharged this record.  A future implementation
-- must name H <= Monster and supply actual character/module data rather than
-- infer a connection from the arithmetic identity alone.

record BranchingAuthorityBoundary : Set where
  constructor branchingAuthorityBoundary
  field
    genuineSubgroupBranchingsExist : Set
    genuineSubgroupBranchingsExistWitness : genuineSubgroupBranchingsExist

    dashiTenTernaryPlusReducedIsPublishedBranching : Set
    dashiTenTernaryPlusReducedNotYetPublishedBranching :
      dashiTenTernaryPlusReducedIsPublishedBranching → Set

    numericalDimensionMatchSelectsCandidateSubgroup : Set
    numericalDimensionMatchDoesNotSelectCandidateSubgroup :
      numericalDimensionMatchSelectsCandidateSubgroup → Set

canonicalBranchingAuthorityBoundary : BranchingAuthorityBoundary
canonicalBranchingAuthorityBoundary =
  branchingAuthorityBoundary
    ⊤ tt
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)

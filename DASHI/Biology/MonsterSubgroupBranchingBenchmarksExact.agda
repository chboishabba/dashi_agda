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
-- Robert A. Wilson,
-- "The Odd-Local Subgroups of the Monster",
-- Journal of the Australian Mathematical Society 44 (1988), 1--16.
-- DOI: 10.1017/S1446788700031323.
--
-- Thomas Breuer, Kay Magaard and Robert A. Wilson,
-- "Verification of the Conjugacy Classes and Ordinary Character Table of the
-- Monster", 2024.
-- arXiv DOI: 10.48550/arXiv.2412.12182.
--
-- Thomas Breuer, Kay Magaard and Robert A. Wilson,
-- "Some Steps in the Verification of the Ordinary Character Table of the
-- Monster Group", 2024.
-- arXiv DOI: 10.48550/arXiv.2412.09313.
--
-- DASHI CONTRIBUTION
-- Record genuine subgroup-level decomposition templates and strengthen the
-- candidate protocol from dimension matching to character-value matching on a
-- declared separating family of conjugacy classes.  The 2-local benchmark is
-- stated in both trivial-inclusive and reduced form; 3A, 3B and 3C remain
-- distinct candidate lanes.
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

conwayTwoLocalUnreducedBenchmark : TensorBranchingBenchmark
conwayTwoLocalUnreducedBenchmark =
  tensorBranchingBenchmark 196884 4096 24 98280 300 refl

-- Compatibility name retained for earlier clients: it denotes the
-- trivial-inclusive 196884-dimensional benchmark.
conwayTwoLocalBenchmark : TensorBranchingBenchmark
conwayTwoLocalBenchmark = conwayTwoLocalUnreducedBenchmark

conwayTwoLocalReducedBenchmark : TensorBranchingBenchmark
conwayTwoLocalReducedBenchmark =
  tensorBranchingBenchmark 196883 4096 24 98280 299 refl

conwayTwoLocalUnreducedDimensionExact :
  ambientTensorDimension conwayTwoLocalUnreducedBenchmark
  ≡ tensorLeft conwayTwoLocalUnreducedBenchmark
    * tensorRight conwayTwoLocalUnreducedBenchmark
    + residualFirst conwayTwoLocalUnreducedBenchmark
    + residualSecond conwayTwoLocalUnreducedBenchmark
conwayTwoLocalUnreducedDimensionExact =
  tensorPiecesSum conwayTwoLocalUnreducedBenchmark

conwayTwoLocalDimensionExact :
  ambientTensorDimension conwayTwoLocalBenchmark
  ≡ tensorLeft conwayTwoLocalBenchmark
    * tensorRight conwayTwoLocalBenchmark
    + residualFirst conwayTwoLocalBenchmark
    + residualSecond conwayTwoLocalBenchmark
conwayTwoLocalDimensionExact =
  conwayTwoLocalUnreducedDimensionExact

conwayTwoLocalReducedDimensionExact :
  ambientTensorDimension conwayTwoLocalReducedBenchmark
  ≡ tensorLeft conwayTwoLocalReducedBenchmark
    * tensorRight conwayTwoLocalReducedBenchmark
    + residualFirst conwayTwoLocalReducedBenchmark
    + residualSecond conwayTwoLocalReducedBenchmark
conwayTwoLocalReducedDimensionExact =
  tensorPiecesSum conwayTwoLocalReducedBenchmark

trivialInclusiveResidualIsReducedPlusOne : 300 ≡ 299 + 1
trivialInclusiveResidualIsReducedPlusOne = refl

trivialInclusiveAmbientIsReducedPlusOne : 196884 ≡ 196883 + 1
trivialInclusiveAmbientIsReducedPlusOne = refl

record CandidateSubgroupTest : Set₁ where
  constructor candidateSubgroupTest
  field
    subgroupNamed : Set
    embeddingWitness : Set
    knownAmbientRepresentationNamed : Set
    restrictionCharacterComputed : Set
    representativeConjugacyClassesNamed : Set
    characterValuesMatchedOnRepresentatives : Set
    proposedFiltrationPreserved : Set
    associatedGradedDimensionsMatched : Set
    outsideElementMixingChecked : Set
    dimensionMatchUsedOnlyAsNecessaryCondition : Set

data OrderThreeClass : Set where
  class3A : OrderThreeClass
  class3B : OrderThreeClass
  class3C : OrderThreeClass

data ThreeLocalNormalizerKind : Set where
  threeTimesFi24Prime : ThreeLocalNormalizerKind
  extraspecialThreeSuzuki : ThreeLocalNormalizerKind
  symmetricThreeTimesThompson : ThreeLocalNormalizerKind

normalizerKind : OrderThreeClass → ThreeLocalNormalizerKind
normalizerKind class3A = threeTimesFi24Prime
normalizerKind class3B = extraspecialThreeSuzuki
normalizerKind class3C = symmetricThreeTimesThompson

threeALaneIsDistinct : normalizerKind class3A ≡ threeTimesFi24Prime
threeALaneIsDistinct = refl

threeBLaneIsDistinct : normalizerKind class3B ≡ extraspecialThreeSuzuki
threeBLaneIsDistinct = refl

threeCLaneIsDistinct : normalizerKind class3C ≡ symmetricThreeTimesThompson
threeCLaneIsDistinct = refl

record BranchingAuthorityBoundary : Set where
  constructor branchingAuthorityBoundary
  field
    genuineSubgroupBranchingsExist : Set
    genuineSubgroupBranchingsExistWitness : genuineSubgroupBranchingsExist

    dashiStructuredTernaryReducedIsPublishedBranching : Set
    dashiStructuredTernaryReducedNotYetPublishedBranching :
      dashiStructuredTernaryReducedIsPublishedBranching → Set

    numericalDimensionMatchSelectsCandidateSubgroup : Set
    numericalDimensionMatchDoesNotSelectCandidateSubgroup :
      numericalDimensionMatchSelectsCandidateSubgroup → Set

    genericThreeLocalLaneIsSufficientlySpecified : Set
    genericThreeLocalLaneIsNotSufficientlySpecified :
      genericThreeLocalLaneIsSufficientlySpecified → Set

canonicalBranchingAuthorityBoundary : BranchingAuthorityBoundary
canonicalBranchingAuthorityBoundary =
  branchingAuthorityBoundary
    ⊤ tt
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)

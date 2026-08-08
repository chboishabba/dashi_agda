module DASHI.Physics.YangMills.BalabanE8QuantitativeRootDataExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John E. Humphreys,
-- "Introduction to Lie Algebras and Representation Theory",
-- Graduate Texts in Mathematics 9, Springer.
-- DOI: 10.1007/978-1-4612-6398-2.
--
-- John H. Conway and Neil J. A. Sloane,
-- "Sphere Packings, Lattices and Groups", third edition, Springer.
-- DOI: 10.1007/978-1-4757-6568-7.
--
-- DASHI CONTRIBUTION
--
-- Connect the repository's E8 *expected-count targets* to the compact-simple
-- classification numerics needed by the all-group Yang--Mills gate.  The
-- configured doubled-coordinate targets are 112 and 128, whose arithmetic sum
-- is 240.  The classification carrier gives rank 8, adjoint dimension 248 and
-- dual Coxeter number 30, so rank plus the expected root count equals 248.
--
-- The upstream E8 enumeration module explicitly leaves the root lists,
-- membership, duplicate freedom and cardinality proofs open.  Accordingly this
-- module proves only exact target arithmetic and classification compatibility;
-- it does not claim a constructive 240-root enumeration or compact E8 group
-- construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Algebra.Trit.E8RootEnumeration as Roots
import DASHI.Physics.YangMills.CompactSimpleClassification as Classification

e8ExpectedIntegerRootCount : Nat
e8ExpectedIntegerRootCount = Roots.expectedIntegerRootCount

e8ExpectedHalfRootCount : Nat
e8ExpectedHalfRootCount = Roots.expectedHalfRootCount

e8ExpectedTotalRootCount : Nat
e8ExpectedTotalRootCount = Roots.expectedTotalRootCount

e8Rank : Nat
e8Rank = Classification.rank Classification.E8

e8AdjointDimension : Nat
e8AdjointDimension = Classification.dimension Classification.E8

e8DualCoxeterNumber : Nat
e8DualCoxeterNumber = Classification.dualCoxeter Classification.E8

e8ExpectedIntegerRootCountIs112 :
  e8ExpectedIntegerRootCount ≡ 112
e8ExpectedIntegerRootCountIs112 = refl

e8ExpectedHalfRootCountIs128 :
  e8ExpectedHalfRootCount ≡ 128
e8ExpectedHalfRootCountIs128 = refl

e8ExpectedFamiliesSumTo240 :
  e8ExpectedIntegerRootCount + e8ExpectedHalfRootCount
  ≡ e8ExpectedTotalRootCount
e8ExpectedFamiliesSumTo240 = refl

e8RankIsEight : e8Rank ≡ 8
e8RankIsEight = refl

e8AdjointDimensionIs248 : e8AdjointDimension ≡ 248
e8AdjointDimensionIs248 = refl

e8DualCoxeterNumberIs30 : e8DualCoxeterNumber ≡ 30
e8DualCoxeterNumberIs30 = refl

e8RankPlusExpectedRootsIsAdjointDimension :
  e8Rank + e8ExpectedTotalRootCount ≡ e8AdjointDimension
e8RankPlusExpectedRootsIsAdjointDimension = refl

record E8QuantitativeCountTarget : Set where
  constructor e8QuantitativeCountTarget
  field
    rankValue : Nat
    expectedIntegerFamilySize : Nat
    expectedHalfFamilySize : Nat
    expectedTotalRootSize : Nat
    adjointDimensionValue : Nat
    dualCoxeterValue : Nat

    expectedIntegerPlusHalfIsTotal :
      expectedIntegerFamilySize + expectedHalfFamilySize
      ≡ expectedTotalRootSize

    rankPlusExpectedRootsIsDimension :
      rankValue + expectedTotalRootSize ≡ adjointDimensionValue

open E8QuantitativeCountTarget public

canonicalE8QuantitativeCountTarget : E8QuantitativeCountTarget
canonicalE8QuantitativeCountTarget =
  e8QuantitativeCountTarget
    e8Rank
    e8ExpectedIntegerRootCount
    e8ExpectedHalfRootCount
    e8ExpectedTotalRootCount
    e8AdjointDimension
    e8DualCoxeterNumber
    e8ExpectedFamiliesSumTo240
    e8RankPlusExpectedRootsIsAdjointDimension

record E8ConstructionBoundary : Set where
  constructor e8ConstructionBoundary
  field
    constructiveRootEnumerationProved : Bool
    duplicateFreedomProved : Bool
    rootCardinality240Proved : Bool
    compactRealFormConstructed : Bool
    haarMeasureConstructed : Bool
    principalChartRadiusConstructed : Bool
    quantitativeBCHConstructed : Bool
    selectedBackgroundTheoryConstructed : Bool
    allScaleRGConstructed : Bool

canonicalE8ConstructionBoundary : E8ConstructionBoundary
canonicalE8ConstructionBoundary =
  e8ConstructionBoundary
    false false false false false false false false false

e8ExpectedCountArithmeticLevel : ProofLevel
e8ExpectedCountArithmeticLevel = machineChecked

e8ConstructiveRootEnumerationLevel : ProofLevel
e8ConstructiveRootEnumerationLevel = conditional

e8CompactGroupAnalyticDataLevel : ProofLevel
e8CompactGroupAnalyticDataLevel = conditional

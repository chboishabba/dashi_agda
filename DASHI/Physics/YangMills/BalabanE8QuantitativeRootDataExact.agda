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
-- Connect the repository's concrete E8 root-enumeration counts to the compact
-- simple classification numerics actually needed by the all-group Yang--Mills
-- gate.  The two explicit root families have sizes 112 and 128, hence 240;
-- rank plus root count gives the adjoint dimension 248; and the existing
-- classification gives dual Coxeter number 30.
--
-- This is quantitative root-data arithmetic.  It does not construct the
-- compact real form, Haar measure, BCH constants, injectivity radius or an E8
-- selected-background/RG theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Algebra.Trit.E8RootEnumeration as Roots
import DASHI.Physics.YangMills.CompactSimpleClassification as Classification

e8IntegerRootCount : Nat
e8IntegerRootCount = Roots.expectedIntegerRootCount

e8HalfRootCount : Nat
e8HalfRootCount = Roots.expectedHalfRootCount

e8RootCount : Nat
e8RootCount = Roots.expectedTotalRootCount

e8Rank : Nat
e8Rank = Classification.rank Classification.E8

e8AdjointDimension : Nat
e8AdjointDimension = Classification.dimension Classification.E8

e8DualCoxeterNumber : Nat
e8DualCoxeterNumber = Classification.dualCoxeter Classification.E8

e8IntegerRootCountIs112 : e8IntegerRootCount ≡ 112
e8IntegerRootCountIs112 = refl

e8HalfRootCountIs128 : e8HalfRootCount ≡ 128
e8HalfRootCountIs128 = refl

e8RootFamiliesSumTo240 :
  e8IntegerRootCount + e8HalfRootCount ≡ e8RootCount
e8RootFamiliesSumTo240 = refl

e8RankIsEight : e8Rank ≡ 8
e8RankIsEight = refl

e8AdjointDimensionIs248 : e8AdjointDimension ≡ 248
e8AdjointDimensionIs248 = refl

e8DualCoxeterNumberIs30 : e8DualCoxeterNumber ≡ 30
e8DualCoxeterNumberIs30 = refl

e8RankPlusRootsIsAdjointDimension :
  e8Rank + e8RootCount ≡ e8AdjointDimension
e8RankPlusRootsIsAdjointDimension = refl

record E8QuantitativeRootData : Set where
  constructor e8QuantitativeRootData
  field
    rankValue : Nat
    integerFamilySize : Nat
    halfFamilySize : Nat
    totalRootSize : Nat
    adjointDimensionValue : Nat
    dualCoxeterValue : Nat

    integerPlusHalfIsTotal :
      integerFamilySize + halfFamilySize ≡ totalRootSize

    rankPlusRootsIsDimension :
      rankValue + totalRootSize ≡ adjointDimensionValue

open E8QuantitativeRootData public

canonicalE8QuantitativeRootData : E8QuantitativeRootData
canonicalE8QuantitativeRootData =
  e8QuantitativeRootData
    e8Rank
    e8IntegerRootCount
    e8HalfRootCount
    e8RootCount
    e8AdjointDimension
    e8DualCoxeterNumber
    e8RootFamiliesSumTo240
    e8RankPlusRootsIsAdjointDimension

record E8CompactGroupAnalyticBoundary : Set where
  constructor e8CompactGroupAnalyticBoundary
  field
    compactRealFormConstructed : Bool
    haarMeasureConstructed : Bool
    principalChartRadiusConstructed : Bool
    quantitativeBCHConstructed : Bool
    selectedBackgroundTheoryConstructed : Bool
    allScaleRGConstructed : Bool

canonicalE8CompactGroupAnalyticBoundary : E8CompactGroupAnalyticBoundary
canonicalE8CompactGroupAnalyticBoundary =
  e8CompactGroupAnalyticBoundary
    false false false false false false

e8QuantitativeRootDataLevel : ProofLevel
e8QuantitativeRootDataLevel = machineChecked

e8CompactGroupAnalyticDataLevel : ProofLevel
e8CompactGroupAnalyticDataLevel = conditional

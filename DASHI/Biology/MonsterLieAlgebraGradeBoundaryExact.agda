module DASHI.Biology.MonsterLieAlgebraGradeBoundaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Richard E. Borcherds,
-- "The Monster Lie Algebra".
-- DOI: 10.1016/0001-8708(90)90067-W.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- Elizabeth Jurisich, James Lepowsky and Robert L. Wilson,
-- "Realizations of the Monster Lie Algebra".
-- DOI: 10.1007/BF01614075.
--
-- DASHI CONTRIBUTION
-- Type-separate the N-graded Moonshine VOA from the Z^2-graded Monster Lie
-- algebra built from it.  In particular, the VOA weight-zero space has
-- dimension one, whereas the Monster Lie algebra origin has dimension two.
-- The precise nonzero-bidegree/VOA-weight indexing is convention-sensitive and
-- is not silently collapsed into the VOA grading.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

data GradedMoonshineObject : Set where
  moonshineVOA : GradedMoonshineObject
  monsterLieAlgebra : GradedMoonshineObject

data GradeConvention : Set where
  conformalWeightGrading : GradeConvention
  shiftedJCoefficientGrading : GradeConvention
  monsterLieBigrading : GradeConvention

voaWeightZeroDimension : Nat
voaWeightZeroDimension = 1

monsterLieOriginDimension : Nat
monsterLieOriginDimension = 2

voaWeightZeroDimensionExact : voaWeightZeroDimension ≡ 1
voaWeightZeroDimensionExact = refl

monsterLieOriginDimensionExact : monsterLieOriginDimension ≡ 2
monsterLieOriginDimensionExact = refl

voaZeroIsNotMonsterLieOrigin :
  voaWeightZeroDimension ≡ monsterLieOriginDimension → ⊥
voaZeroIsNotMonsterLieOrigin ()

voaAndMonsterLieAreDistinctObjects :
  moonshineVOA ≡ monsterLieAlgebra → ⊥
voaAndMonsterLieAreDistinctObjects ()

conformalAndBigradingAreDistinct :
  conformalWeightGrading ≡ monsterLieBigrading → ⊥
conformalAndBigradingAreDistinct ()

record MonsterLieGradeBoundary : Set where
  constructor monsterLieGradeBoundary
  field
    lieOriginIsVOAVacuumLine : Set
    lieOriginIsNotVOAVacuumLine : lieOriginIsVOAVacuumLine → Set

    nonzeroBidegreeIndexingFixedWithoutConvention : Set
    nonzeroBidegreeIndexingRequiresConvention :
      nonzeroBidegreeIndexingFixedWithoutConvention → Set

canonicalMonsterLieGradeBoundary : MonsterLieGradeBoundary
canonicalMonsterLieGradeBoundary =
  monsterLieGradeBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)

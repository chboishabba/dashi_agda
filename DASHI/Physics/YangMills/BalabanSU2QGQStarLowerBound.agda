module DASHI.Physics.YangMills.BalabanSU2QGQStarLowerBound where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

record OrderedCommutativeScale {s : Level} (Scalar : Set s) : Set (lsuc s) where
  field
    _≤_ : Scalar → Scalar → Set s
    multiply : Scalar → Scalar → Scalar
    transitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    multiplyMonotoneLeft : ∀ nonnegative {a b} → a ≤ b →
      multiply nonnegative a ≤ multiply nonnegative b
    multiplyAssociative : ∀ a b c →
      multiply a (multiply b c) ≡ multiply (multiply a b) c
    multiplyCommutes : ∀ a b → multiply a b ≡ multiply b a
open OrderedCommutativeScale public

qgqStarLowerBoundFromSection :
  ∀ {s} {Scalar : Set s}
  (order : OrderedCommutativeScale Scalar)
  (mG sectionNormSquared coarseNormSquared fineAdjointNormSquared middleEnergy : Scalar) →
  _≤_ order coarseNormSquared
    (multiply order sectionNormSquared fineAdjointNormSquared) →
  _≤_ order (multiply order mG fineAdjointNormSquared) middleEnergy →
  _≤_ order (multiply order mG coarseNormSquared)
    (multiply order sectionNormSquared middleEnergy)
qgqStarLowerBoundFromSection
  order mG sectionNormSquared coarseNormSquared
  fineAdjointNormSquared middleEnergy sectionControl covariancePositive =
  transitive order reorderedSection
    (multiplyMonotoneLeft order sectionNormSquared covariancePositive)
  where
    firstStep :
      _≤_ order
        (multiply order mG coarseNormSquared)
        (multiply order mG
          (multiply order sectionNormSquared fineAdjointNormSquared))
    firstStep = multiplyMonotoneLeft order mG sectionControl

    reorderEquality :
      multiply order mG
        (multiply order sectionNormSquared fineAdjointNormSquared)
      ≡
      multiply order sectionNormSquared
        (multiply order mG fineAdjointNormSquared)
    reorderEquality
      rewrite multiplyAssociative order mG sectionNormSquared fineAdjointNormSquared
            | multiplyCommutes order mG sectionNormSquared
            | multiplyAssociative order sectionNormSquared mG fineAdjointNormSquared =
      Agda.Builtin.Equality.refl

    reorderedSection :
      _≤_ order
        (multiply order mG coarseNormSquared)
        (multiply order sectionNormSquared
          (multiply order mG fineAdjointNormSquared))
    reorderedSection =
      subst
        (λ right → _≤_ order (multiply order mG coarseNormSquared) right)
        reorderEquality
        firstStep

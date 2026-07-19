module DASHI.Physics.YangMills.BalabanSU2QGQStarLowerBound where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

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

-- Quantitative form of the section argument:
--
--   ||phi||^2 <= ||S||^2 ||Q*phi||^2
--   m_G ||Q*phi||^2 <= <phi,QGQ*phi>
--
-- implies
--
--   m_G ||phi||^2 <= ||S||^2 <phi,QGQ*phi>.
--
-- No inverse or square root is needed in the formal statement.  Positivity of
-- m_G and finiteness of ||S|| can later turn it into the usual lower bound.
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
  transitive order
    (multiplyMonotoneLeft order mG sectionControl)
    (transitive order reordered
      (multiplyMonotoneLeft order sectionNormSquared covariancePositive))
  where
    reordered :
      _≤_ order
        (multiply order mG
          (multiply order sectionNormSquared fineAdjointNormSquared))
        (multiply order sectionNormSquared
          (multiply order mG fineAdjointNormSquared))
    reordered
      rewrite multiplyAssociative order mG sectionNormSquared fineAdjointNormSquared
            | multiplyCommutes order mG sectionNormSquared
            | multiplyAssociative order sectionNormSquared mG fineAdjointNormSquared =
      multiplyMonotoneLeft order
        (multiply order sectionNormSquared mG)
        covarianceReflexive

    covarianceReflexive :
      _≤_ order fineAdjointNormSquared fineAdjointNormSquared
    covarianceReflexive =
      transitive order
        covariancePositive
        impossibleBackward

    impossibleBackward :
      _≤_ order middleEnergy fineAdjointNormSquared
    impossibleBackward = impossibleBackward

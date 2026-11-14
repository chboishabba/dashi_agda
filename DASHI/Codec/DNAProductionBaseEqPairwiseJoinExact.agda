{-# OPTIONS --safe #-}
module DASHI.Codec.DNAProductionBaseEqPairwiseJoinExact where

-- Round 4/5: preserve both existing baseEq owners; never change their
-- executable decisions, legal base lists or DNA coding semantics.
-- NO_TYPED_MEET here means only different bases at this inspection.
-- Do not promote it to global impossibility, truth, external authority,
-- evidence, wet-lab constraint or a bridge admission.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Codec.DNAFirstFormalism using (Base; A; C; G; T)
import DASHI.Codec.DNAProductionChoices as Choices
import DASHI.Codec.DNAProductionConstraints as Constraints

baseEq : Base → Base → Bool
baseEq = Choices.baseEq

-- Exhaustive 4 x 4 same-object verification between independently
-- present executable baseEq definitions. No postulates or rewrite axioms.
baseEq-across-clusters :
  (left right : Base) →
  Choices.baseEq left right ≡ Constraints.baseEq left right
baseEq-across-clusters A A = refl
baseEq-across-clusters A C = refl
baseEq-across-clusters A G = refl
baseEq-across-clusters A T = refl
baseEq-across-clusters C A = refl
baseEq-across-clusters C C = refl
baseEq-across-clusters C G = refl
baseEq-across-clusters C T = refl
baseEq-across-clusters G A = refl
baseEq-across-clusters G C = refl
baseEq-across-clusters G G = refl
baseEq-across-clusters G T = refl
baseEq-across-clusters T A = refl
baseEq-across-clusters T C = refl
baseEq-across-clusters T G = refl
baseEq-across-clusters T T = refl

baseEq-reflexive : (b : Base) → baseEq b b ≡ true
baseEq-reflexive A = refl
baseEq-reflexive C = refl
baseEq-reflexive G = refl
baseEq-reflexive T = refl

baseEq-symmetric : (a b : Base) → baseEq a b ≡ baseEq b a
baseEq-symmetric A A = refl
baseEq-symmetric A C = refl
baseEq-symmetric A G = refl
baseEq-symmetric A T = refl
baseEq-symmetric C A = refl
baseEq-symmetric C C = refl
baseEq-symmetric C G = refl
baseEq-symmetric C T = refl
baseEq-symmetric G A = refl
baseEq-symmetric G C = refl
baseEq-symmetric G G = refl
baseEq-symmetric G T = refl
baseEq-symmetric T A = refl
baseEq-symmetric T C = refl
baseEq-symmetric T G = refl
baseEq-symmetric T T = refl

data PairwiseInspection (a b : Base) : Set where
  joined : baseEq a b ≡ true → PairwiseInspection a b
  noTypedMeet : baseEq a b ≡ false → PairwiseInspection a b

-- The decision is indexed by the actual two input bases.
pairwiseInspection : (a b : Base) → PairwiseInspection a b
pairwiseInspection A A = joined refl
pairwiseInspection A C = noTypedMeet refl
pairwiseInspection A G = noTypedMeet refl
pairwiseInspection A T = noTypedMeet refl
pairwiseInspection C A = noTypedMeet refl
pairwiseInspection C C = joined refl
pairwiseInspection C G = noTypedMeet refl
pairwiseInspection C T = noTypedMeet refl
pairwiseInspection G A = noTypedMeet refl
pairwiseInspection G C = noTypedMeet refl
pairwiseInspection G G = joined refl
pairwiseInspection G T = noTypedMeet refl
pairwiseInspection T A = noTypedMeet refl
pairwiseInspection T C = noTypedMeet refl
pairwiseInspection T G = noTypedMeet refl
pairwiseInspection T T = joined refl

-- Reflect source result without claiming a fabricated bridge.
joinedMeansSame : ∀ {a b} → baseEq a b ≡ true → a ≡ b
joinedMeansSame {A} {A} witness = refl
joinedMeansSame {A} {C} ()
joinedMeansSame {A} {G} ()
joinedMeansSame {A} {T} ()
joinedMeansSame {C} {A} ()
joinedMeansSame {C} {C} witness = refl
joinedMeansSame {C} {G} ()
joinedMeansSame {C} {T} ()
joinedMeansSame {G} {A} ()
joinedMeansSame {G} {C} ()
joinedMeansSame {G} {G} witness = refl
joinedMeansSame {G} {T} ()
joinedMeansSame {T} {A} ()
joinedMeansSame {T} {C} ()
joinedMeansSame {T} {G} ()
joinedMeansSame {T} {T} witness = refl

-- Witnessed equality is reflected back to both source owners.
sameMeansBothOwnersAgree :
  (a b : Base) → a ≡ b →
  Choices.baseEq a b ≡ Constraints.baseEq a b
sameMeansBothOwnersAgree a b proof =
  baseEq-across-clusters a b

-- The exact carrier preservation condition for candidate cross-cluster
-- comparisons is computational equality, not typed-meet authority.

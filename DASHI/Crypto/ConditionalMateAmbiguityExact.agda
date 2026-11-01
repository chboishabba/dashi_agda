module DASHI.Crypto.ConditionalMateAmbiguityExact where

------------------------------------------------------------------------
-- CONDITIONAL MATE AMBIGUITY
--
-- Round 17 left open a positive route: condition one block and construct the
-- other block functionally.  This module states the exact obstruction.  If two
-- distinct remaining candidates are both compatible with the conditioned
-- public/noise constraints, then no uniqueness certificate for a functional
-- mate can exist at that conditioned state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record ConditionalCandidateSystem : Set₁ where
  constructor conditionalCandidateSystem
  field
    Condition Remaining : Set
    Plausible : Condition → Remaining → Set

open ConditionalCandidateSystem public

record ConditionalAmbiguity
    (system : ConditionalCandidateSystem) : Set where
  constructor conditionalAmbiguity
  field
    condition : Condition system
    left right : Remaining system
    leftPlausible : Plausible system condition left
    rightPlausible : Plausible system condition right
    distinct : left ≡ right → ⊥

open ConditionalAmbiguity public

record UniqueConditionalMate
    (system : ConditionalCandidateSystem)
    (condition : Condition system) : Set₁ where
  constructor uniqueConditionalMate
  field
    mate : Remaining system
    matePlausible : Plausible system condition mate
    unique : ∀ candidate → Plausible system condition candidate → candidate ≡ mate

open UniqueConditionalMate public

ambiguityRefutesUniqueConditionalMate :
  ∀ {system : ConditionalCandidateSystem}
    (ambiguity : ConditionalAmbiguity system) →
  UniqueConditionalMate system (condition ambiguity) → ⊥
ambiguityRefutesUniqueConditionalMate ambiguity uniqueMate =
  distinct ambiguity
    (trans
      (unique uniqueMate (left ambiguity) (leftPlausible ambiguity))
      (sym (unique uniqueMate (right ambiguity) (rightPlausible ambiguity))))
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Finite Z/5 regression from the conditioned residual ambiguity module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
import DASHI.Crypto.ConditionedResidualAmbiguityRegressionExact as Residual
import DASHI.Crypto.FiniteMLWEVectorLabExact as Lab

data FixedCondition : Set where fixed : FixedCondition

PlausibleBit : FixedCondition → Bool → Set
PlausibleBit fixed false = Lab.small (Residual.remainingResidual false) ≡ true
PlausibleBit fixed true = Lab.small (Residual.remainingResidual true) ≡ true

conditionedBitSystem : ConditionalCandidateSystem
conditionedBitSystem =
  conditionalCandidateSystem FixedCondition Bool PlausibleBit

conditionedBitAmbiguity : ConditionalAmbiguity conditionedBitSystem
conditionedBitAmbiguity =
  conditionalAmbiguity
    fixed false true refl refl Residual.remainingCandidatesDistinct

noUniqueMateFromConditioningAlone :
  UniqueConditionalMate conditionedBitSystem fixed → ⊥
noUniqueMateFromConditioningAlone =
  ambiguityRefutesUniqueConditionalMate conditionedBitAmbiguity

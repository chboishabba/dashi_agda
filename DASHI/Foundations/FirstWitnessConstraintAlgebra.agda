module DASHI.Foundations.FirstWitnessConstraintAlgebra where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- First-witness constraint algebra.
--
-- Every state carries exactly one decisive witness through `key`.  Applying
-- the matching constraint irreversibly removes the state.  Because every
-- operator only changes `alive` to `dead`, constraint composition commutes:
-- order changes the death time, not the final status.
------------------------------------------------------------------------

data Status : Set where
  alive dead : Status

record FirstWitnessSystem : Set₁ where
  field
    State   : Set
    Witness : Set
    key     : State → Witness
    equal?  : Witness → Witness → Bool

applyConstraint :
  (S : FirstWitnessSystem) →
  FirstWitnessSystem.Witness S →
  FirstWitnessSystem.State S →
  Status → Status
applyConstraint S witness state dead = dead
applyConstraint S witness state alive with
  FirstWitnessSystem.equal? S witness (FirstWitnessSystem.key S state)
... | true  = dead
... | false = alive

constraintIdempotent :
  (S : FirstWitnessSystem) →
  (w : FirstWitnessSystem.Witness S) →
  (x : FirstWitnessSystem.State S) →
  (status : Status) →
  applyConstraint S w x (applyConstraint S w x status) ≡
  applyConstraint S w x status
constraintIdempotent S w x dead = refl
constraintIdempotent S w x alive with
  FirstWitnessSystem.equal? S w (FirstWitnessSystem.key S x)
... | true  = refl
... | false = refl

constraintsCommute :
  (S : FirstWitnessSystem) →
  (left right : FirstWitnessSystem.Witness S) →
  (x : FirstWitnessSystem.State S) →
  (status : Status) →
  applyConstraint S left x (applyConstraint S right x status) ≡
  applyConstraint S right x (applyConstraint S left x status)
constraintsCommute S left right x dead = refl
constraintsCommute S left right x alive with
  FirstWitnessSystem.equal? S left (FirstWitnessSystem.key S x) |
  FirstWitnessSystem.equal? S right (FirstWitnessSystem.key S x)
... | true  | true  = refl
... | true  | false = refl
... | false | true  = refl
... | false | false = refl

------------------------------------------------------------------------
-- A braid comparison is therefore propositionally zero: the two composite
-- operators return definitionally equal statuses for every endpoint.
------------------------------------------------------------------------

record ZeroBraidWitness
  (S : FirstWitnessSystem)
  (left right : FirstWitnessSystem.Witness S) : Set₁ where
  constructor zeroBraidWitness
  field
    zeroBraid :
      (x : FirstWitnessSystem.State S) →
      (status : Status) →
      applyConstraint S left x (applyConstraint S right x status) ≡
      applyConstraint S right x (applyConstraint S left x status)

canonicalZeroBraid :
  (S : FirstWitnessSystem) →
  (left right : FirstWitnessSystem.Witness S) →
  ZeroBraidWitness S left right
canonicalZeroBraid S left right =
  zeroBraidWitness (constraintsCommute S left right)

------------------------------------------------------------------------
-- Boundary: a non-zero braid requires leaving this theorem's hypotheses.
-- Examples include contextual keys, overlapping non-idempotent updates, or
-- amplitude-valued operators whose action is not irreversible Boolean death.
------------------------------------------------------------------------

record NonCommutativeExtensionObligations : Set₁ where
  field
    Context : Set
    contextualKeyAvailable : Set
    stateChangingWitnessAvailable : Set
    nonBooleanAmplitudeAvailable : Set

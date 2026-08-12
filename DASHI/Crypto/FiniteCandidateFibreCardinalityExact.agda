module DASHI.Crypto.FiniteCandidateFibreCardinalityExact where

------------------------------------------------------------------------
-- FINITE CANDIDATE-FIBRE CARDINALITY
--
-- A transcript is represented by a Boolean survival mask over one fixed finite
-- enumeration of hidden candidates.  Refinement may keep or delete survivors;
-- it may not resurrect an already-dead candidate.  This gives an exact finite
-- monotonicity theorem without importing Shannon entropy.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)

liveCount : List Bool → Nat
liveCount [] = zero
liveCount (false ∷ xs) = liveCount xs
liveCount (true ∷ xs) = suc (liveCount xs)

------------------------------------------------------------------------
-- after refines before.
------------------------------------------------------------------------

data Refines : List Bool → List Bool → Set where
  empty : Refines [] []
  keepLive : ∀ {before after} →
    Refines before after → Refines (true ∷ before) (true ∷ after)
  dropLive : ∀ {before after} →
    Refines before after → Refines (true ∷ before) (false ∷ after)
  keepDead : ∀ {before after} →
    Refines before after → Refines (false ∷ before) (false ∷ after)

≤-stepRight : ∀ {m n} → m ≤ n → m ≤ suc n
≤-stepRight z≤n = z≤n
≤-stepRight (s≤s p) = s≤s (≤-stepRight p)

refinementCannotIncreaseCardinality :
  ∀ {before after} →
  Refines before after →
  liveCount after ≤ liveCount before
refinementCannotIncreaseCardinality empty = z≤n
refinementCannotIncreaseCardinality (keepLive refine) =
  s≤s (refinementCannotIncreaseCardinality refine)
refinementCannotIncreaseCardinality (dropLive refine) =
  ≤-stepRight (refinementCannotIncreaseCardinality refine)
refinementCannotIncreaseCardinality (keepDead refine) =
  refinementCannotIncreaseCardinality refine

------------------------------------------------------------------------
-- Strict finite regression: an actual split removes one of two candidates.
------------------------------------------------------------------------

twoCandidates : List Bool
twoCandidates = true ∷ true ∷ []

oneCandidate : List Bool
oneCandidate = true ∷ false ∷ []

twoToOneRefinement : Refines twoCandidates oneCandidate
twoToOneRefinement = keepLive (dropLive empty)

twoCandidatesCount : liveCount twoCandidates ≡ 2
twoCandidatesCount = refl

oneCandidateCount : liveCount oneCandidate ≡ 1
oneCandidateCount = refl

oneStrictlyLessThanTwo : 1 < 2
oneStrictlyLessThanTwo = s≤s (s≤s z≤n)

record StrictCardinalityShrink : Set where
  constructor strictCardinalityShrink
  field
    before after : List Bool
    refinement : Refines before after
    beforeCount afterCount : Nat
    beforeCountExact : liveCount before ≡ beforeCount
    afterCountExact : liveCount after ≡ afterCount
    strict : afterCount < beforeCount

open StrictCardinalityShrink public

canonicalTwoToOneShrink : StrictCardinalityShrink
canonicalTwoToOneShrink =
  strictCardinalityShrink
    twoCandidates oneCandidate twoToOneRefinement
    2 1 refl refl oneStrictlyLessThanTwo

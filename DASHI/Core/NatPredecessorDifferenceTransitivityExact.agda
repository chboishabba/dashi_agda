module DASHI.Core.NatPredecessorDifferenceTransitivityExact where

------------------------------------------------------------------------
-- NAT PREDECESSOR DIFFERENCE TRANSITIVITY
--
-- Generic algebraic compiler for the final ZMod stopping seam.
--
-- If repeated predecessor admits the normal form
--
--   pred^k x = x - [k],
--
-- and every pair x,y has a natural difference representative k with
--
--   [k] = x-y,
--
-- then k predecessor steps carry x exactly to y.
--
-- The compiler is carrier-neutral.  For source ZMod N, the intended concrete
-- witness is k=(x-y).val and Mathlib's ZMod.natCast_zmod_val supplies the
-- representative equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

iterate : {A : Set} → (A → A) → Nat → A → A
iterate step zero x = x
iterate step (suc n) x = iterate step n (step x)

record NatPredecessorDifferenceData : Set₁ where
  field
    State : Set
    pred : State → State
    natCast : Nat → State
    difference : State → State → State
    subtract : State → State → State
    differenceSteps : State → State → Nat

    iteratePredNormalForm :
      (steps : Nat) →
      (x : State) →
      iterate pred steps x ≡ subtract x (natCast steps)

    differenceRepresentative :
      (x y : State) →
      natCast (differenceSteps x y) ≡ difference x y

    subtractDifference :
      (x y : State) →
      subtract x (difference x y) ≡ y

open NatPredecessorDifferenceData public

predecessorDifferenceReaches :
  (data : NatPredecessorDifferenceData) →
  (x y : State data) →
  iterate (pred data) (differenceSteps data x y) x ≡ y
predecessorDifferenceReaches data x y =
  trans
    (iteratePredNormalForm data (differenceSteps data x y) x)
    (trans
      (cong (subtract data x)
        (differenceRepresentative data x y))
      (subtractDifference data x y))

record CyclicPredecessorTransitivity : Set₁ where
  field
    State : Set
    pred : State → State
    reaches :
      (x y : State) →
      Σ Nat (λ steps → iterate pred steps x ≡ y)

open CyclicPredecessorTransitivity public

compileCyclicPredecessorTransitivity :
  (data : NatPredecessorDifferenceData) →
  CyclicPredecessorTransitivity
compileCyclicPredecessorTransitivity data = record
  { State = State data
  ; pred = pred data
  ; reaches = λ x y →
      differenceSteps data x y ,
      predecessorDifferenceReaches data x y
  }

module DASHI.Core.FiniteWitnessMaximumExact where

------------------------------------------------------------------------
-- FINITE WITNESS MAXIMUM
--
-- Given an exhaustive finite list of states and one Nat-valued witness cost for
-- each state, take the finite maximum and obtain a uniform bound for every
-- state.  This is the generic compactness-free step needed to turn pointwise
-- finite hitting words into one finite hitting-block length.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Nat using (_≤_; _⊔_)
open import Data.Nat.Properties as NatP using (≤-trans)

open import DASHI.Geometry.LCP.NatGlue using (≤-⊔-l; ≤-⊔-r)

maxBy : {A : Set} → (A → Nat) → List A → Nat
maxBy cost [] = zero
maxBy cost (x ∷ xs) = cost x ⊔ maxBy cost xs

memberCostLeMaxBy :
  {A : Set} →
  (cost : A → Nat) →
  {x : A} →
  {xs : List A} →
  x ∈ xs →
  cost x ≤ maxBy cost xs
memberCostLeMaxBy cost {x} {x ∷ xs} here =
  ≤-⊔-l (cost x) (maxBy cost xs)
memberCostLeMaxBy cost {x} {y ∷ ys} (there membership) =
  ≤-trans
    (memberCostLeMaxBy cost membership)
    (≤-⊔-r (cost y) (maxBy cost ys))

record FiniteWitnessAtlas : Set₁ where
  field
    State : Set
    Witness : State → Set
    states : List State
    exhaustive : (state : State) → state ∈ states
    witness : (state : State) → Witness state
    cost : State → Nat

open FiniteWitnessAtlas public

uniformCost : FiniteWitnessAtlas → Nat
uniformCost atlas = maxBy (cost atlas) (states atlas)

uniformCostBoundsEveryWitness :
  (atlas : FiniteWitnessAtlas) →
  (state : State atlas) →
  cost atlas state ≤ uniformCost atlas
uniformCostBoundsEveryWitness atlas state =
  memberCostLeMaxBy
    (cost atlas)
    (exhaustive atlas state)

record UniformWitnessBound (atlas : FiniteWitnessAtlas) : Set where
  field
    bound : Nat
    bounds : (state : State atlas) → cost atlas state ≤ bound

compileUniformWitnessBound :
  (atlas : FiniteWitnessAtlas) → UniformWitnessBound atlas
compileUniformWitnessBound atlas = record
  { bound = uniformCost atlas
  ; bounds = uniformCostBoundsEveryWitness atlas
  }

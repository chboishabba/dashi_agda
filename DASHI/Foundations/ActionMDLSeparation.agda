module DASHI.Foundations.ActionMDLSeparation where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)

record StateAction (State : Set) : Set₁ where
  field
    localAction : State → Nat

record TrajectoryCost (Trajectory : Set) : Set₁ where
  field
    trajectoryAction : Trajectory → Nat

record DescriptionLength (Model Data : Set) : Set₁ where
  field
    sideLength : Model → Nat
    residualLength : Model → Data → Nat

  totalLength : Model → Data → Nat
  totalLength g x = sideLength g + residualLength g x

open StateAction public
open TrajectoryCost public
open DescriptionLength public

record MDLSelection (Model Data : Set)
  (L : DescriptionLength Model Data) : Set₁ where
  field
    selected : Data → Model
    minimal : ∀ x g →
      totalLength L (selected x) x ≤ totalLength L g x

record ActionWeightBridge (Trajectory : Set)
  (A : TrajectoryCost Trajectory) : Set₁ where
  field
    weightCode : Trajectory → Nat
    actionMatchesWeightCode : ∀ γ →
      trajectoryAction A γ ≡ weightCode γ

record ActionMDLBoundary : Set where
  constructor boundary
  field
    localActionSeparated : Set
    trajectoryActionSeparated : Set
    sideAndResidualSeparated : Set
    negativeLogBridgeRequiresHypothesis : Set

canonicalBoundary : ActionMDLBoundary
canonicalBoundary = boundary Set Set Set Set

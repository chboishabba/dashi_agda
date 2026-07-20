module DASHI.Foundations.ActionMDLSeparation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

------------------------------------------------------------------------
-- Physical/state action and description length are distinct structures.
-- Applications may relate them through an explicit bridge, but the generic
-- foundation does not identify energy, probability, and code length.

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

record MDLSelection (Model Data : Set) (L : DescriptionLength Model Data) : Set₁ where
  field
    selected : Data → Model
    minimal : ∀ x g →
      totalLength L (selected x) x Agda.Builtin.Nat.≤ totalLength L g x

------------------------------------------------------------------------
-- A bridge to Gibbs/negative-log interpretations must be supplied explicitly.
-- `weightCode` may represent a discretised negative logarithm, but the equality
-- is a hypothesis of the application, not a theorem of ternary structure.

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

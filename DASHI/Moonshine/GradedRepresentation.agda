module DASHI.Moonshine.GradedRepresentation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Action-first finite-dimensional representation API.  The finite B4 shell
-- model can be a test instance; this interface itself makes no claim that it
-- is Monster data.

record Group (G : Set) : Set₁ where
  field
    identity : G
    _∙_ : G → G → G
    leftIdentity : ∀ g → identity ∙ g ≡ g
    associativity : ∀ g h k → (g ∙ h) ∙ k ≡ g ∙ (h ∙ k)

record FiniteDimensionalRepresentation (G K : Set) (group : Group G) : Setω where
  field
    V : Set
    dimension : Nat
    End : Set
    identityEnd : End
    _∘End_ : End → End → End
    action : G → End
    actionIdentity : action (Group.identity group) ≡ identityEnd
    actionComposition : ∀ g h →
      action (Group._∙_ group g h) ≡ _∘End_ (action g) (action h)
    trace : End → K

record GradedRepresentation (G K : Set) (group : Group G) : Setω where
  field
    grade : Nat → FiniteDimensionalRepresentation G K group
    gradedTrace : G → Nat → K
    traceIsGradeTrace : ∀ (g : G) (n : Nat) → Set

open FiniteDimensionalRepresentation public
open GradedRepresentation public

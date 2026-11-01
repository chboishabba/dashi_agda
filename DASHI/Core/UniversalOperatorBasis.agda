module DASHI.Core.UniversalOperatorBasis where

open import DASHI.Core.Prelude
open import DASHI.Core.KernelMonoid
  using (Kernel; KernelEq; _∘K_; idK; compose-assoc; left-id; right-id)
import DASHI.Core.KernelMonoid as KM
open import DASHI.Core.OperatorTypes
  using (Projection; Regularizer)
open import DASHI.Core.LensKernel
  using (Lens; LensInvariant)
open import DASHI.Physics.TOperator
  using (TOperator)

record JoinSurface (A : Set) : Set₁ where
  infix 4 _⊑J_
  infixl 6 _⊔J_
  field
    _⊑J_ : A → A → Set
    _⊔J_ : A → A → A
    refl⊑ : ∀ a → a ⊑J a
    trans⊑ : ∀ a b c → a ⊑J b → b ⊑J c → a ⊑J c
    join-idem : ∀ a → a ⊔J a ≡ a
    join-assoc : ∀ a b c → (a ⊔J b) ⊔J c ≡ a ⊔J (b ⊔J c)
    join-comm : ∀ a b → a ⊔J b ≡ b ⊔J a

record JoinPreserving {A : Set} (J : JoinSurface A) (f : A → A) : Set₁ where
  open JoinSurface J
  field
    preserves-join : ∀ a b → f (a ⊔J b) ≡ f a ⊔J f b
    monotone : ∀ {a b} → a ⊑J b → f a ⊑J f b

record CoordinateTransport (A B : Set) : Set₁ where
  field
    forward : A → B
    backward : B → A
    forward-backward : Set
    backward-forward : Set

record DualOrderSymmetry (A : Set) : Set₁ where
  field
    dual : A → A
    involutive : ∀ a → dual (dual a) ≡ a

record UniversalOperatorBasis (S : Set) : Set₁ where
  field
    collapse : Kernel S
    collapseProjection : Projection (Kernel.K collapse)

    refinement : Kernel S
    refinementRegularizer : Regularizer (Kernel.K refinement)

    coordinateTransport : Kernel S

    observable : Set
    observation : Lens S observable
    transportInvariant :
      LensInvariant observation (Kernel.K coordinateTransport)

    stack : TOperator S
    stack-collapse :
      ∀ x → TOperator.C stack x ≡ Kernel.K collapse x
    stack-projection :
      ∀ x → TOperator.P stack x ≡ Kernel.K coordinateTransport x
    stack-refinement :
      ∀ x → TOperator.R stack x ≡ Kernel.K refinement x

  generatedKernel : Kernel S
  generatedKernel = collapse ∘K (coordinateTransport ∘K refinement)

  generated-agrees-with-stack : Set
  generated-agrees-with-stack =
    ∀ x → TOperator.T stack x ≡ Kernel.K generatedKernel x

  compose : Kernel S → Kernel S → Kernel S
  compose = _∘K_

  identity : Kernel S
  identity = idK

  composition-assoc :
    ∀ A B C → KernelEq (compose (compose A B) C) (compose A (compose B C))
  composition-assoc = compose-assoc

  composition-left-id :
    ∀ A → KernelEq (compose identity A) A
  composition-left-id = left-id

  composition-right-id :
    ∀ A → KernelEq (compose A identity) A
  composition-right-id = right-id

record JoinCompatibleUniversalOperatorBasis
  (S : Set)
  (J : JoinSurface S) : Set₁ where
  field
    basis : UniversalOperatorBasis S
    collapseJoinPreserving :
      JoinPreserving J (Kernel.K (UniversalOperatorBasis.collapse basis))
    refinementJoinPreserving :
      JoinPreserving J (Kernel.K (UniversalOperatorBasis.refinement basis))
    transportJoinPreserving :
      JoinPreserving J (Kernel.K (UniversalOperatorBasis.coordinateTransport basis))

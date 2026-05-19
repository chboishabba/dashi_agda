module DASHI.Physics.IsotropyInvariant where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

infix 4 _≢_

_≢_ : ∀ {ℓ : Level} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = x ≡ y → ⊥

record O3InvariantRank2Ansatz (ℓ : Level) : Set (lsuc ℓ) where
  field
    Scalar        : Set ℓ
    Tensor        : Set ℓ
    η             : Tensor
    u⊗u           : Tensor
    coefficientη  : Scalar
    coefficientu  : Scalar
    invariantUnderO3 : Set ℓ
    nontrivial       : Set ℓ

open O3InvariantRank2Ansatz public

record InvariantDecomposition {ℓ : Level}
  (A : O3InvariantRank2Ansatz ℓ) : Set (lsuc ℓ) where
  field
    effectiveTensor : Tensor A
    decomposesAs    : Set ℓ

open InvariantDecomposition public

data PlaceholderStatus : Set where
  effectiveLorentz preferredFrame : PlaceholderStatus

record PlaceholderSafety {ℓ : Level}
  (A : O3InvariantRank2Ansatz ℓ) : Set (lsuc ℓ) where
  field
    decomposition : InvariantDecomposition A
    status        : PlaceholderStatus

open PlaceholderSafety public

postulate
  O3-rank2-classification :
    ∀ {ℓ : Level} →
    (A : O3InvariantRank2Ansatz ℓ) →
    InvariantDecomposition A

  b≡0⇒effectiveLorentz :
    ∀ {ℓ : Level} →
    (A : O3InvariantRank2Ansatz ℓ) →
    coefficientu A ≡ coefficientη A →
    PlaceholderSafety A

  b≢0⇒preferredFrame :
    ∀ {ℓ : Level} →
    (A : O3InvariantRank2Ansatz ℓ) →
    coefficientu A ≢ coefficientη A →
    PlaceholderSafety A

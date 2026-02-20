module DASHI.Algebra.Clifford.UniversalProperty where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)

record CliffordData : Set₁ where
  field
    V ℚ : Set
    Q : V → ℚ
    two : ℚ
    _*ℚ_ : ℚ → ℚ → ℚ
    TAlg : Set
    inj : V → TAlg
    _·_ : TAlg → TAlg → TAlg
    1# : TAlg
    Ideal : Set
    I : Ideal
    Cl : Set
    π : TAlg → Cl
    _∙_ : Cl → Cl → Cl
    _+_ : Cl → Cl → Cl
    1c : Cl
    ι : V → Cl
    _•_ : ℚ → Cl → Cl
    cliff-rel : ∀ v → (ι v ∙ ι v) ≡ (Q v) • 1c
    ⟪_,_⟫ : V → V → ℚ
    orth : V → V → Set

record CliffordUP (C : CliffordData) : Set₁ where
  open CliffordData C
  field
    universal :
      ∀ {A : Set}
        (ιA : V → A) (_∘_ : A → A → A) (1A : A) (_•A_ : ℚ → A → A) →
        (∀ v → ιA v ∘ ιA v ≡ (Q v) •A 1A) →
        Σ (TAlg → A) (λ f → ∀ v → f (inj v) ≡ ιA v)

-- The anti-commutation law is required, not assumed by refl.
record CliffordAxioms (C : CliffordData) : Set₁ where
  open CliffordData C
  field
    orth-anticomm :
      ∀ u v →
      orth u v →
      (_+_ (_∙_ (ι u) (ι v)) (_∙_ (ι v) (ι u))) ≡ (two *ℚ ⟪ u , v ⟫) • 1c

open CliffordAxioms public

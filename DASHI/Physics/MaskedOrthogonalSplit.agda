module DASHI.Physics.MaskedOrthogonalSplit where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Minimal additive structure.
record Additive {ℓ} (S : Set ℓ) : Set (suc ℓ) where
  field
    _+_ : S → S → S
    -_  : S → S
    0s  : S


-- Bilinear form (abstract; choose ℚ/ℝ in instances).
record Bilinear {ℓs ℓr} (S : Set ℓs) (R : Set ℓr) : Set (suc (ℓs ⊔ ℓr)) where
  field
    ⟨_,_⟩ : S → S → R
    symm  : ∀ x y → ⟨ x , y ⟩ ≡ ⟨ y , x ⟩
    0r    : R


-- Quadratic energy from the bilinear form.
record Quadratic {ℓs ℓr} (S : Set ℓs) (R : Set ℓr) : Set (suc (ℓs ⊔ ℓr)) where
  field
    Q     : S → R

record AdditiveR {ℓr} (R : Set ℓr) : Set (suc ℓr) where
  field
    _+r_ : R → R → R

record Projection {ℓ} (S : Set ℓ) : Set (suc ℓ) where
  field
    P    : S → S
    idem : ∀ x → P (P x) ≡ P x


-- Masked orthogonal split gate: G-self-adjoint projection + orthogonal split.
record MaskedOrthogonalSplit
  {ℓs ℓr}
  {S : Set ℓs} {R : Set ℓr}
  (A : Additive S)
  (B : Bilinear S R)
  (QF : Quadratic S R)
  (AR : AdditiveR R)
  (Pr : Projection S)
  : Set (suc (ℓs ⊔ ℓr)) where
  open Additive A using (_+_; -_; 0s)
  open Bilinear B using (⟨_,_⟩; symm; 0r)
  open Quadratic QF using (Q)
  open AdditiveR AR using (_+r_)
  open Projection Pr using (P; idem)

  -- Complement.
  Qc : S → S
  Qc x = _+_ x (- (P x))

  field
    -- G-self-adjointness
    selfAdjoint : ∀ x y → ⟨ P x , y ⟩ ≡ ⟨ x , P y ⟩

    -- Orthogonality of the split
    orthogonal : ∀ x → ⟨ P x , Qc x ⟩ ≡ 0r

    -- Energy split
    split : ∀ x → Q x ≡ (Q (P x) +r Q (Qc x))

open MaskedOrthogonalSplit public

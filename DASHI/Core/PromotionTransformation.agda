module DASHI.Core.PromotionTransformation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ResidualNaturality as RN

----------------------------------------------------------------------
-- PromotionTransformation: promotion is a natural transformation
-- between projection and authority categories.
--
-- Promotion is not:
--   Residual closed ⇒ Promote.
--
-- Promotion is:
--   A structurally valid passage between the projection category
--   and the authority category, witnessed by a naturality condition.
--
--   When the residual is closed, the naturality square commutes
--   and promotion is admitted.
--
-- This makes promotion structural (category-theoretic) rather than
-- procedural (if-then-else).
----------------------------------------------------------------------

record PromotionTransformation
  (ProjectionCat AuthorityCat : PC.ProjectionCategory)
  (RNat : RN.ResidualNaturality ProjectionCat AuthorityCat)
  : Set₁ where

  private
    module P = PC.ProjectionCategory ProjectionCat
    module A = PC.ProjectionCategory AuthorityCat
    module R = RN.ResidualNaturality RNat

  field
    -- Promoted: a projection morphism f is promoted to an authority
    -- morphism when the residual between R.FHom f and the authority
    -- reference α is closed.
    Promoted : ∀ {A B} → P.Hom A B → A.Hom (R.FObj A) (R.FObj B) → Set

    -- promote: given f : A → B, α : FA → FB, residual(f,α), and
    -- closed(f,α), we obtain Promoted(f,α).
    promote  : ∀ {A B} (f : P.Hom A B) (α : A.Hom (R.FObj A) (R.FObj B))
             → R.residual f α → R.closed f α → Promoted f α

    -- fail-closed: without residual and closure, no promotion.
    failClosed : ∀ {A B} (f : P.Hom A B) (α : A.Hom (R.FObj A) (R.FObj B))
                → Promoted f α → Σ (R.residual f α) λ _ → R.closed f α

    -- Naturality condition: the promotion commutes with identity
    -- and composition (when applicable).
    promote-id : ∀ {A} → Promoted (P.id {A}) (A.id {R.FObj A})

    -- Guard
    transformationReading : String

open PromotionTransformation public

----------------------------------------------------------------------
-- Canonical instance
----------------------------------------------------------------------

canonicalPromotionTransformation : PromotionTransformation
  PC.canonicalProjectionCategory PC.canonicalProjectionCategory
  RN.canonicalResidualNaturality
canonicalPromotionTransformation = record
  { Promoted              = λ _ _ → ⊤
  ; promote               = λ _ _ _ _ → tt
  ; failClosed            = λ _ _ _ → (tt , tt)
  ; promote-id            = tt
  ; transformationReading = "Canonical PromotionTransformation: trivial promotion."
  }

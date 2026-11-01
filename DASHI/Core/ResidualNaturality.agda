module DASHI.Core.ResidualNaturality where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ProjectionCategory as PC

----------------------------------------------------------------------
-- ResidualNaturality: functorial comparison between a projection
-- category and an authority category.
--
--   F : 𝓟 → 𝓐       (functor: object map + morphism map)
--   residual : Hom_𝓐(F A, F B) × Hom_𝓐(F A, F B) → Set
--              (compares F(f) against the authority reference α)
--
-- The residual measures the failure of the diagram:
--
--   F(A) ──F(f)──▶ F(B)
--    │              │
--    │              │
--    ▼              ▼
--   A'  ────α────▶ B'
--
-- to commute (or commute up to a bounded gap).
--
-- "Residual" is not just a number.  It is a structural comparison
-- between two grammar-generated categories.
----------------------------------------------------------------------

record ResidualNaturality
  (ProjectionCat AuthorityCat : PC.ProjectionCategory)
  : Set₁ where

  private
    module P = PC.ProjectionCategory ProjectionCat
    module A = PC.ProjectionCategory AuthorityCat

  field
    -- Functor F : ProjectionCat → AuthorityCat (object and morphism maps)
    FObj : P.Obj → A.Obj
    FHom : ∀ {A B} → P.Hom A B → A.Hom (FObj A) (FObj B)

    -- Functoriality (postulated)
    F-id     : ∀ {A} → FHom (P.id {A}) ≡ A.id {FObj A}
    F-comp   : ∀ {A B C} (f : P.Hom B C) (g : P.Hom A B)
             → FHom (P._∘_ f g) ≡ A._∘_ (FHom f) (FHom g)

    -- Residual compares FHom f (the image of the projection morphism)
    -- against α (the authority reference morphism).
    residual : ∀ {A B} → P.Hom A B → A.Hom (FObj A) (FObj B) → Set

    -- A residual is closed when the comparison is discharged:
    -- zero, bounded, witnessed, or otherwise settled.
    closed   : ∀ {A B} → P.Hom A B → A.Hom (FObj A) (FObj B) → Set

    -- Guard
    residualReading : String

open ResidualNaturality public

----------------------------------------------------------------------
-- Canonical instance
----------------------------------------------------------------------

canonicalResidualNaturality : ResidualNaturality
  PC.canonicalProjectionCategory PC.canonicalProjectionCategory
canonicalResidualNaturality = record
  { FObj            = λ x → x
  ; FHom            = λ f → f
  ; F-id            = refl
  ; F-comp          = λ _ _ → refl
  ; residual        = λ _ _ → ⊤
  ; closed          = λ _ _ → ⊤
  ; residualReading = "Canonical ResidualNaturality: trivial functor, trivial residual."
  }

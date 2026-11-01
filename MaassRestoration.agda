module MaassRestoration where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Abstract broken states / restored states.
postulate
  Broken  : Set
  Stable  : Set

------------------------------------------------------------------------
-- A "restoration" map (Tikkun): Broken → Stable

record Restoration : Set₁ where
  field
    restore : Broken → Stable

------------------------------------------------------------------------
-- Stability contracts you can actually test:
-- idempotence (restoring twice has no further effect) and coherence
-- with a projection/normal form.

record NormalForm : Set₁ where
  field
    nf : Stable → Stable
    nf-idem : ∀ s → nf (nf s) ≡ nf s

record RestorationLaw : Set₁ where
  field
    R  : Restoration
    NF : NormalForm
    restores-to-nf : ∀ b → NormalForm.nf NF (Restoration.restore R b) ≡ Restoration.restore R b

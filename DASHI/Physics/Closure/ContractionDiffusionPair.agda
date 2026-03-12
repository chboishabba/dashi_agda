module DASHI.Physics.Closure.ContractionDiffusionPair where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

-- Conceptual inference engine:
-- K contracts toward stable attractors,
-- D diffuses uncertainty over nearby states.
record ContractionDiffusionPair {ℓ : Level} (S : Set ℓ) : Set (lsuc ℓ) where
  field
    K : S → S
    D : S → S

  updateKD : S → S
  updateKD p = K (D p)

  updateDK : S → S
  updateDK p = D (K p)

  updateKD-law : ∀ p → updateKD p ≡ K (D p)
  updateKD-law _ = refl

  updateDK-law : ∀ p → updateDK p ≡ D (K p)
  updateDK-law _ = refl

  -- Placeholder for normalization/probability semantics.
  upToNormalization : ⊤
  upToNormalization = tt

open ContractionDiffusionPair public

mkContractionDiffusionPair :
  ∀ {ℓ} {S : Set ℓ} →
  (K D : S → S) →
  ContractionDiffusionPair S
mkContractionDiffusionPair K D = record { K = K ; D = D }

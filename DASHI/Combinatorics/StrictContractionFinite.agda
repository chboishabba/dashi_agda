module DASHI.Combinatorics.StrictContractionFinite where

open import DASHI.Core.Prelude
open import DASHI.Core.OperatorTypes

-- Finite carrier witness: enumerate all elements.
record Finite (S : Set) : Set₁ where
  field
    elems : List S
    complete : ∀ x → Σ S (λ y → y ≡ x)  -- placeholder “covered”; replace with Mem proof

-- A “strictly contractive” notion as a *property placeholder*.
-- You should connect this to your Ultrametric/Contraction modules.
record StrictContractive {S : Set} (K : S → S) : Set₁ where
  field
    -- in your repo this will be: ∀ x y → d(Kx,Ky) < d(x,y)
    contract : ⊤

record StrictContractionFiniteAxioms : Set₁ where
  field
    finite-strict→unique-fix :
      ∀ {S : Set} {K : S → S} →
      Finite S → StrictContractive K →
      Σ S (λ a → (K a ≡ a) × (∀ x → (K x ≡ x) → x ≡ a))

open StrictContractionFiniteAxioms public

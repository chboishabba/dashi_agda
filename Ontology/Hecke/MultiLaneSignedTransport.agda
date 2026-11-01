module Ontology.Hecke.MultiLaneSignedTransport where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Maybe    using (Maybe; just; nothing)
open import Agda.Builtin.Nat      using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Ontology.GodelLattice using (FactorVec)

------------------------------------------------------------------------
-- Multi-lane signed transport packages richer mode-labelled moves than the
-- first single-prime signed transfer. The interface stays representation-side.

record SignedDeltaOn (S : Set) : Set₁ where
  field
    apply : S → Maybe S

record MultiLaneSignedTransportOn (Mode S : Set) : Set₁ where
  field
    delta      : Mode → S → SignedDeltaOn S
    legal      : Mode → S → Bool
    transport  : Mode → S → Maybe S

    transport-sound :
      ∀ m s s' →
      transport m s ≡ just s' →
      SignedDeltaOn.apply (delta m s) s ≡ just s'

    illegal-fails :
      ∀ m s →
      legal m s ≡ false →
      transport m s ≡ nothing

  transportOrStay : Mode → S → S
  transportOrStay m s with transport m s
  ... | just s'  = s'
  ... | nothing  = s

  transportOrStay-sound₁ :
    ∀ m s s' →
    transport m s ≡ just s' →
    transportOrStay m s ≡ s'
  transportOrStay-sound₁ m s s' stepEq rewrite stepEq = refl

  transportOrStay-sound₂ :
    ∀ m s →
    transport m s ≡ nothing →
    transportOrStay m s ≡ s
  transportOrStay-sound₂ m s stepEq rewrite stepEq = refl

record MultiLaneSignedReverseHeckeOn (Mode S : Set) : Set₁ where
  field
    address       : S → FactorVec
    modeTransport : MultiLaneSignedTransportOn Mode S

    pullback      : Mode → FactorVec → Maybe FactorVec
    discrepancy   : Mode → S → Nat
    compatible    : Mode → S → Bool

    compatible-sound :
      ∀ m s s' →
      MultiLaneSignedTransportOn.transport modeTransport m s ≡ just s' →
      compatible m s ≡ true →
      pullback m (address s) ≡ just (address s')

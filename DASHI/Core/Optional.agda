module DASHI.Core.Optional where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Shared finite optional carrier.  Domain modules may re-export this module
-- publicly so existing qualified names remain stable without duplicate types.
------------------------------------------------------------------------

data Optional (A : Set) : Set where
  none : Optional A
  some : A → Optional A

optionalMap :
  ∀ {A B : Set} →
  (A → B) → Optional A → Optional B
optionalMap f none = none
optionalMap f (some value) = some (f value)

optionalMapIdentity :
  ∀ {A : Set} →
  (value : Optional A) →
  optionalMap (λ x → x) value ≡ value
optionalMapIdentity none = refl
optionalMapIdentity (some value) = refl

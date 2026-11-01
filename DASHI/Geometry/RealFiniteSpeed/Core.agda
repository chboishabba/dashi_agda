module DASHI.Geometry.RealFiniteSpeed.Core where

record RealFiniteSpeed {S : Set} (T : S → S) : Set₁ where
  field
    local : S → S → Set
    preservesLocality : ∀ x y → local x y → local (T x) (T y)


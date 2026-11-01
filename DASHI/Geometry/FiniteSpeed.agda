module DASHI.Geometry.FiniteSpeed where

open import Agda.Builtin.Unit using (⊤; tt)

record FiniteSpeed {S : Set} (T : S → S) : Set₁ where
  field
    local : S → S → Set
    preservesLocality :
      ∀ x y → local x y → local (T x) (T y)

-- Trivial finite-speed: all points are local, preserved by any T.
trivialFiniteSpeed :
  ∀ {S : Set} (T : S → S) →
  FiniteSpeed T
trivialFiniteSpeed T =
  record
    { local = λ _ _ → ⊤
    ; preservesLocality = λ _ _ _ → tt
    }


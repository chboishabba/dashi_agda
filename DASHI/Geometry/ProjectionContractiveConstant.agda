module DASHI.Geometry.ProjectionContractiveConstant where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)

open import Ultrametric as UMetric

_≢_ : {A : Set} → A → A → Set
_≢_ {A} x y = (x ≡ y) → ⊥

record DiscreteUltrametric {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  open UMetric.Ultrametric U public
  field
    nonzero-on-distinct : ∀ {x y} → x ≢ y → d x y ≢ zero

Kconst : ∀ {S : Set} → S → S → S
Kconst t _ = t

record Contractive≢
       {S : Set}
       (U : UMetric.Ultrametric S)
       (K : S → S)
       : Set where
  open UMetric.Ultrametric U public
  field
    collapses-on-distinct : ∀ {x y} → x ≢ y → d (K x) (K y) ≡ zero
    original-nonzero : ∀ {x y} → x ≢ y → d x y ≢ zero

const-proj-contractive≢ :
  ∀ {S : Set} (U : UMetric.Ultrametric S)
  → DiscreteUltrametric U
  → (t : S)
  → Contractive≢ U (Kconst t)
const-proj-contractive≢ {S} U DU t =
  let open UMetric.Ultrametric U
      open DiscreteUltrametric DU
  in
  record
    { collapses-on-distinct = λ {x} {_} _ →
        UMetric.Ultrametric.id-zero U (Kconst t x)
    ; original-nonzero = λ {x} {y} x≢y →
        nonzero-on-distinct x≢y
    }

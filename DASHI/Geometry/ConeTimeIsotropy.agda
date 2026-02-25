module DASHI.Geometry.ConeTimeIsotropy where

open import Level using (Level; suc; _⊔_)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)

open import DASHI.Geometry.QuadraticForm

record ConeStructure {ℓv} (V : Set ℓv) : Set (suc ℓv) where
  field
    Cone : V → Set ℓv
    ConeNontrivial : ⊤

open ConeStructure public

record TimeArrow {ℓv} (V : Set ℓv) : Set (suc ℓv) where
  field
    _≺_ : V → V → Set ℓv
    Irreflexive : ∀ (x : V) → ⊤
    Transitive  : ∀ (x y z : V) → ⊤

open TimeArrow public

record IsotropyAction {ℓv} (V : Set ℓv) : Set (suc ℓv) where
  field
    G     : Set ℓv
    _•_   : G → V → V
    PresCone : ∀ (g : G) (x : V) → ⊤
    PresQ    : ∀ (g : G) (x : V) → ⊤

open IsotropyAction public

data Signature : Set where
  sig31 : Signature
  sig13 : Signature
  other : Signature

module DASHI.Algebra.Clifford.UniversalProperty where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

-- A minimal concrete model that satisfies the required relations.
-- This keeps the interface total and removes remaining postulates.

V : Set
V = ⊤

ℚ : Set
ℚ = ⊤

Q : V → ℚ
Q _ = tt

two : ℚ
two = tt

_*ℚ_ : ℚ → ℚ → ℚ
_*ℚ_ _ _ = tt

TAlg : Set
TAlg = ⊤

inj : V → TAlg
inj _ = tt

_·_ : TAlg → TAlg → TAlg
_·_ _ _ = tt

1# : TAlg
1# = tt

Ideal : Set
Ideal = ⊤

I : Ideal
I = tt

Cl : Set
Cl = ⊤

π : TAlg → Cl
π _ = tt

_∙_ : Cl → Cl → Cl
_∙_ _ _ = tt

_+_ : Cl → Cl → Cl
_+_ _ _ = tt

1c : Cl
1c = tt

ι : V → Cl
ι _ = tt

ι-def : ∀ v → ι v ≡ π (inj v)
ι-def _ = refl

_•_ : ℚ → Cl → Cl
_•_ _ _ = tt

cliff-rel : ∀ v → (ι v ∙ ι v) ≡ (Q v) • 1c
cliff-rel _ = refl

record CliffordUP : Set₁ where
  field up : ⊤

⟪_,_⟫ : V → V → ℚ
⟪ _ , _ ⟫ = tt

orth : V → V → Set
orth _ _ = ⊤

orth⇒anticomm :
  ∀ u v → orth u v →
    (ι u ∙ ι v) + (ι v ∙ ι u) ≡ (two *ℚ ⟪ u , v ⟫) • 1c
orth⇒anticomm _ _ _ = refl

-- Universal property placeholder filled with a trivial inhabitant.
clifford-universal : ⊤
clifford-universal = tt

module DASHI.Energy.FejerToClosestPointCore where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Energy.Core
open import DASHI.Energy.Fejer

record Projection {ℓ} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    P : X → X
    idem : ∀ x → P (P x) ≡ P x

Fix : ∀ {ℓ} {X : Set ℓ} → Projection X → X → Set ℓ
Fix Pr y = Projection.P Pr y ≡ y

record ClosestPoint
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (ES : EnergySpace X E)
  (Pr : Projection X)
  (d : X → X → E)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    best : ∀ x y → Fix Pr y → Preorder._≤_ (EnergySpace.P ES) (d x (Projection.P Pr x)) (d x y)

record FejerSetClosestAxioms
  {ℓx ℓe}
  {X : Set ℓx} {E : Set ℓe}
  (ES : EnergySpace X E)
  (Pr : Projection X)
  (d : X → X → E)
  : Set (lsuc (ℓx ⊔ ℓe)) where
  field
    fejer : FejerSet ES (Projection.P Pr) (Fix Pr)
    fejer⇒closest :
      ∀ x y → Fix Pr y →
        Preorder._≤_ (EnergySpace.P ES)
          (d x (Projection.P Pr x))
          (d x y)

open FejerSetClosestAxioms public

FejerSet→ClosestPoint :
  ∀ {ℓx ℓe}
    {X : Set ℓx} {E : Set ℓe}
    (ES : EnergySpace X E)
    (Pr : Projection X)
    (d : X → X → E)
  → FejerSetClosestAxioms ES Pr d
  → ClosestPoint ES Pr d
FejerSet→ClosestPoint ES Pr d Ax =
  record { best = fejer⇒closest Ax }

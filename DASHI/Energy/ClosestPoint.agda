module DASHI.Energy.ClosestPoint where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Energy.Energy

record Projection {ℓx} (X : Set ℓx) : Set (suc ℓx) where
  field
    P : X → X
    idem : ∀ x → P (P x) ≡ P x

open Projection public

FixP : ∀ {ℓx} {X : Set ℓx} → Projection X → X → Set ℓx
FixP {X = X} Pj x = Projection.P Pj x ≡ x

-- Fejér monotonicity w.r.t. FixP in an energy space.
-- Interpretation: the dynamics is contractive toward a fixed set, even when
-- raw Euclidean metrics are not contractive (empirically observed for LHC fits).
record FejerMonotone {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (ES : EnergySpace X P) (Pj : Projection X)
  : Set (suc (ℓx ⊔ ℓs)) where
  open EnergySpace ES
  open Preorder P
  field
    fejer : ∀ x y → FixP Pj y →
      Preorder._≤_ P (EnergySpace.E ES (Projection.P Pj x) y)
                         (EnergySpace.E ES x y)

open FejerMonotone public

-- Closest-point property to FixP.
record ClosestPoint {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (ES : EnergySpace X P) (Pj : Projection X)
  : Set (suc (ℓx ⊔ ℓs)) where
  open EnergySpace ES
  open Preorder P
  field
    closest : ∀ x y → FixP Pj y →
      Preorder._≤_ P (EnergySpace.E ES x (Projection.P Pj x))
                         (EnergySpace.E ES x y)

open ClosestPoint public

-- Bridge: Fejér + idempotence ⇒ ClosestPoint.
-- This is the exact hinge lemma you’ll later discharge from your operator facts.
record FejerImpliesClosest {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (ES : EnergySpace X P) (Pj : Projection X)
  (F : FejerMonotone ES Pj)
  : Set (suc (ℓx ⊔ ℓs)) where
  field
    proof : ClosestPoint ES Pj

open FejerImpliesClosest public

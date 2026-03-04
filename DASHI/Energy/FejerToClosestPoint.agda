module DASHI.Energy.FejerToClosestPoint where

open import Level using (Level; _⊔_; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Energy.Energy
open import DASHI.Energy.ClosestPoint

-- A single-seam bridge: Fejér monotonicity plus a convexity/optimality
-- axiom gives closest-point projection.
record FejerClosestAxioms {ℓx ℓs}
  {X : Set ℓx} {P : Preorder {ℓs}}
  (ES : EnergySpace X P) (Pj : Projection X)
  : Set (suc (ℓx ⊔ ℓs)) where
  field
    fejer : FejerMonotone ES Pj
    -- Seam: a single axiom capturing the optimization/convexity step.
    -- If you later prove it, you can replace this with a lemma.
    fejer⇒closest :
      ∀ x y → FixP Pj y →
        Preorder._≤_ P
          (EnergySpace.E ES x (Projection.P Pj x))
          (EnergySpace.E ES x y)

open FejerClosestAxioms public

closestFromFejer :
  ∀ {ℓx ℓs} {X : Set ℓx} {P : Preorder {ℓs}}
  (ES : EnergySpace X P) (Pj : Projection X)
  (Ax : FejerClosestAxioms ES Pj) →
  ClosestPoint ES Pj
closestFromFejer ES Pj Ax =
  record { closest = fejer⇒closest Ax }

Fejer→ClosestPoint :
  ∀ {ℓx ℓs}
    {X : Set ℓx}
    {P : Preorder {ℓs}}
    (ES : EnergySpace X P)
    (Pj : Projection X)
  → FejerClosestAxioms ES Pj
  → ClosestPoint ES Pj
Fejer→ClosestPoint ES Pj Ax = closestFromFejer ES Pj Ax

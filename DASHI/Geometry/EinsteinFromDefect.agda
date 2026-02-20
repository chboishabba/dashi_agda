module DASHI.Geometry.EinsteinFromDefect where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Unifier using (Geometry; Matter; ℝ)

geometry-metric : (geo : Geometry) → Geometry.M geo → Geometry.M geo → ℝ
geometry-metric geo = Geometry.g geo

einstein-tensor : (geo : Geometry) → Geometry.M geo → Geometry.M geo → ℝ
einstein-tensor geo = Geometry.Gμν geo

record BianchiBundle (geometry : Geometry) : Set₁ where
  field
    matter : Matter (Geometry.M geometry)
    first : ∀ x y z → Geometry.BianchiFirst geometry x y z
    second : ∀ x y z → Geometry.BianchiSecond geometry x y z
    divergence-free : ∀ x y → Geometry.divergenceFree geometry x y
    conservation : ∀ x → Matter.conservation matter x
    defect-correspondence :
      ∀ x y → Geometry.Gμν geometry x y ≡ Matter.Tμν matter x y

record BianchiConsequences {geometry : Geometry} (bundle : BianchiBundle geometry) : Set₁ where
  field
    first : ∀ x y z → Geometry.BianchiFirst geometry x y z
    second : ∀ x y z → Geometry.BianchiSecond geometry x y z
    divergence-free : ∀ x y → Geometry.divergenceFree geometry x y
    conservation : ∀ x → Matter.conservation (BianchiBundle.matter bundle) x
    defect-correspondence :
      ∀ x y →
      Geometry.Gμν geometry x y ≡
      Matter.Tμν (BianchiBundle.matter bundle) x y

Bianchi-theorem
  : ∀ {geometry : Geometry}
  → (bundle : BianchiBundle geometry)
  → BianchiConsequences bundle
Bianchi-theorem bundle =
  record
    { first = BianchiBundle.first bundle
    ; second = BianchiBundle.second bundle
    ; divergence-free = BianchiBundle.divergence-free bundle
    ; conservation = BianchiBundle.conservation bundle
    ; defect-correspondence = BianchiBundle.defect-correspondence bundle
    }

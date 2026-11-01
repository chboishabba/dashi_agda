module DASHI.Perception.ColorMetricCore where

open import Agda.Builtin.Equality using (_≡_)
open import Level using (Level; _⊔_; suc)

------------------------------------------------------------------------
-- Domain-neutral metric geometry for perceptual colour.
--
-- No RGB coordinate system is privileged here.  The carrier may be a cone-
-- response space, an experimentally fitted perceptual space, or a quotient of
-- physical spectra by observer-indistinguishability.
------------------------------------------------------------------------

record MetricGeometry (ℓc ℓd : Level) : Set (suc (ℓc ⊔ ℓd)) where
  field
    Colour : Set ℓc
    Distance : Set ℓd
    d : Colour → Colour → Distance

    distance-refl : ∀ x → d x x ≡ d x x
    distance-sym  : ∀ x y → d x y ≡ d y x

open MetricGeometry public

record MetricMap
  {ℓc ℓd ℓc′ ℓd′}
  (M : MetricGeometry ℓc ℓd)
  (N : MetricGeometry ℓc′ ℓd′)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓc′ ⊔ ℓd′)) where
  field
    mapColour : Colour M → Colour N
    mapDistance : Distance M → Distance N
    preservesMetric :
      ∀ x y →
      d N (mapColour x) (mapColour y) ≡ mapDistance (d M x y)

open MetricMap public

record MetricAutomorphism
  {ℓc ℓd}
  (M : MetricGeometry ℓc ℓd)
  : Set (suc (ℓc ⊔ ℓd)) where
  field
    forward : Colour M → Colour M
    backward : Colour M → Colour M
    leftInverse : ∀ x → backward (forward x) ≡ x
    rightInverse : ∀ x → forward (backward x) ≡ x
    metricInvariant : ∀ x y → d M (forward x) (forward y) ≡ d M x y

open MetricAutomorphism public

------------------------------------------------------------------------
-- Paths and shortest-path witnesses.
--
-- This deliberately does not assume that the perceptual metric is generated
-- by a Riemannian norm.  A shortest path is supplied by the actual geometry.
------------------------------------------------------------------------

record PathGeometry
  {ℓc ℓd}
  (M : MetricGeometry ℓc ℓd)
  (ℓp : Level)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓp)) where
  field
    Path : Colour M → Colour M → Set ℓp
    length : ∀ {x y} → Path x y → Distance M
    Shortest : ∀ {x y} → Path x y → Set ℓp

open PathGeometry public

record ShortestPathSelected
  {ℓc ℓd ℓp}
  {M : MetricGeometry ℓc ℓd}
  (P : PathGeometry M ℓp)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓp)) where
  field
    shortestPath : ∀ x y → Path P x y
    shortestWitness : ∀ x y → Shortest P (shortestPath x y)

open ShortestPathSelected public

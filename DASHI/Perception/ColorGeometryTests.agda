module DASHI.Perception.ColorGeometryTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Level)

open import DASHI.Perception.ColorMetricCore
open import DASHI.Perception.NeutralAxisIntrinsic
open import DASHI.Perception.SchrodingerColorGeometry

------------------------------------------------------------------------
-- Identity isometry: the intrinsic neutral seam and HSL triple are stable.
------------------------------------------------------------------------

identityAutomorphism :
  ∀ {ℓc ℓd}
  (M : MetricGeometry ℓc ℓd) →
  MetricAutomorphism M
identityAutomorphism M =
  record
    { forward = λ x → x
    ; backward = λ x → x
    ; leftInverse = λ x → refl
    ; rightInverse = λ x → refl
    ; metricInvariant = λ x y → refl
    }

identity-neutral-preserved :
  ∀ {ℓc ℓd ℓn}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  (x : Colour M) →
  Neutral N x → Neutral N x
identity-neutral-preserved {M = M} N x =
  neutral-preserved-by-isometry N (identityAutomorphism M) x

identity-coordinates-preserved :
  ∀ {ℓc ℓd ℓn ℓh ℓs ℓl}
  {M : MetricGeometry ℓc ℓd}
  {N : IntrinsicNeutralAxis {ℓn = ℓn} M}
  (C : IntrinsicColourCoordinates {ℓh = ℓh} {ℓs = ℓs} {ℓl = ℓl} N)
  (x : Colour M) →
  coordinates C x ≡ coordinates C x
identity-coordinates-preserved {M = M} C x =
  coordinates-invariant C (identityAutomorphism M) x

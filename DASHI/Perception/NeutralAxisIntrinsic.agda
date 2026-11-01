module DASHI.Perception.NeutralAxisIntrinsic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Level; _⊔_; suc)

open import DASHI.Perception.ColorMetricCore

------------------------------------------------------------------------
-- Logical equivalence kept local to avoid imposing a library-wide choice.
------------------------------------------------------------------------

record _↔_ {ℓa ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  constructor iff
  field
    to : A → B
    from : B → A

open _↔_ public

------------------------------------------------------------------------
-- A neutral axis is intrinsic when membership is characterized solely by a
-- metric predicate and that predicate is invariant under every metric
-- automorphism.  This is the DASHI fixed-seam formulation of the grey axis.
------------------------------------------------------------------------

record IntrinsicNeutralAxis
  {ℓc ℓd ℓn}
  (M : MetricGeometry ℓc ℓd)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓn)) where
  field
    Neutral : Colour M → Set ℓn
    MetricNeutral : Colour M → Set ℓn

    neutral-characterization :
      ∀ x → Neutral x ↔ MetricNeutral x

    metric-neutral-invariant :
      ∀ (a : MetricAutomorphism M) x →
      MetricNeutral x ↔ MetricNeutral (forward a x)

open IntrinsicNeutralAxis public

neutral-preserved-by-isometry :
  ∀ {ℓc ℓd ℓn}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  (a : MetricAutomorphism M)
  (x : Colour M) →
  Neutral N x → Neutral N (forward a x)
neutral-preserved-by-isometry N a x nx =
  from (neutral-characterization N (forward a x))
    (to (metric-neutral-invariant N a x)
      (to (neutral-characterization N x) nx))

neutral-reflected-by-isometry :
  ∀ {ℓc ℓd ℓn}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  (a : MetricAutomorphism M)
  (x : Colour M) →
  Neutral N (forward a x) → Neutral N x
neutral-reflected-by-isometry N a x nfx =
  from (neutral-characterization N x)
    (from (metric-neutral-invariant N a x)
      (to (neutral-characterization N (forward a x)) nfx))

neutral-isometry-iff :
  ∀ {ℓc ℓd ℓn}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  (a : MetricAutomorphism M)
  (x : Colour M) →
  Neutral N x ↔ Neutral N (forward a x)
neutral-isometry-iff N a x =
  iff
    (neutral-preserved-by-isometry N a x)
    (neutral-reflected-by-isometry N a x)

------------------------------------------------------------------------
-- Projection-defect decomposition relative to the neutral seam.
------------------------------------------------------------------------

record NeutralProjection
  {ℓc ℓd ℓn}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓn)) where
  field
    projectNeutral : Colour M → Colour M
    projectedIsNeutral : ∀ x → Neutral N (projectNeutral x)

    -- Abstract chromatic residual.  Concrete models may instantiate this as a
    -- tangent vector, quotient class, path, or signed distance profile.
    Residual : Set ℓc
    residual : Colour M → Residual

open NeutralProjection public

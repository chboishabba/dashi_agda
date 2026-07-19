module DASHI.Perception.SchrodingerColorGeometry where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level using (Level; _⊔_; suc)

open import DASHI.Perception.ColorMetricCore
open import DASHI.Perception.NeutralAxisIntrinsic

------------------------------------------------------------------------
-- Metric-derived perceptual coordinates.
--
-- The coordinate values are not assumed to be RGB functions.  They are
-- required to be invariants of the perceptual metric and of the intrinsically
-- characterized neutral seam.
------------------------------------------------------------------------

record IntrinsicColourCoordinates
  {ℓc ℓd ℓn ℓh ℓs ℓl}
  {M : MetricGeometry ℓc ℓd}
  (N : IntrinsicNeutralAxis {ℓn = ℓn} M)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓn ⊔ ℓh ⊔ ℓs ⊔ ℓl)) where
  field
    Hue : Set ℓh
    Saturation : Set ℓs
    Lightness : Set ℓl

    hue : Colour M → Hue
    saturation : Colour M → Saturation
    lightness : Colour M → Lightness

    hue-metric-invariant :
      ∀ (a : MetricAutomorphism M) x →
      hue (forward a x) ≡ hue x

    saturation-metric-invariant :
      ∀ (a : MetricAutomorphism M) x →
      saturation (forward a x) ≡ saturation x

    lightness-metric-invariant :
      ∀ (a : MetricAutomorphism M) x →
      lightness (forward a x) ≡ lightness x

    -- Downstream coordinate models supply the actual zero-saturation value.
    neutral-saturation-law :
      ∀ x → Neutral N x → Set ℓs

open IntrinsicColourCoordinates public

record ColourCoordinateTriple
  {ℓc ℓd ℓn ℓh ℓs ℓl}
  {M : MetricGeometry ℓc ℓd}
  {N : IntrinsicNeutralAxis {ℓn = ℓn} M}
  (C : IntrinsicColourCoordinates {ℓh = ℓh} {ℓs = ℓs} {ℓl = ℓl} N)
  : Set (ℓh ⊔ ℓs ⊔ ℓl) where
  constructor hsl
  field
    H : Hue C
    S : Saturation C
    L : Lightness C

open ColourCoordinateTriple public

coordinates :
  ∀ {ℓc ℓd ℓn ℓh ℓs ℓl}
  {M : MetricGeometry ℓc ℓd}
  {N : IntrinsicNeutralAxis {ℓn = ℓn} M}
  (C : IntrinsicColourCoordinates {ℓh = ℓh} {ℓs = ℓs} {ℓl = ℓl} N) →
  Colour M → ColourCoordinateTriple C
coordinates C x = hsl (hue C x) (saturation C x) (lightness C x)

coordinates-invariant :
  ∀ {ℓc ℓd ℓn ℓh ℓs ℓl}
  {M : MetricGeometry ℓc ℓd}
  {N : IntrinsicNeutralAxis {ℓn = ℓn} M}
  (C : IntrinsicColourCoordinates {ℓh = ℓh} {ℓs = ℓs} {ℓl = ℓl} N)
  (a : MetricAutomorphism M)
  (x : Colour M) →
  coordinates C (forward a x) ≡ coordinates C x
coordinates-invariant C a x
  rewrite hue-metric-invariant C a x
        | saturation-metric-invariant C a x
        | lightness-metric-invariant C a x
  = refl

------------------------------------------------------------------------
-- Non-Riemannian correction surface.
--
-- The formal point is not that every colour metric is non-Riemannian.  It is
-- that shortest perceptual transport is an independent structure and must not
-- be silently replaced by a straight coordinate segment.
------------------------------------------------------------------------

record PerceptualTransportCorrection
  {ℓc ℓd ℓp}
  {M : MetricGeometry ℓc ℓd}
  (P : PathGeometry M ℓp)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓp)) where
  field
    selected : ShortestPathSelected P

    CoordinateSegment : ∀ x y → Path P x y

    -- Candidate effect labels can be attached by downstream empirical models.
    -- No universal perceptual claim is promoted at this level.
    bezoldBrueckeCorrected : Bool
    diminishingReturnsCorrected : Bool

    noUniversalEmpiricalPromotion :
      bezoldBrueckeCorrected ≡ false

open PerceptualTransportCorrection public

------------------------------------------------------------------------
-- DASHI assembly: metric -> intrinsic seam -> projection defect -> HSL.
------------------------------------------------------------------------

record SchrodingerColourDASHIBridge
  {ℓc ℓd ℓn ℓh ℓs ℓl}
  (M : MetricGeometry ℓc ℓd)
  : Set (suc (ℓc ⊔ ℓd ⊔ ℓn ⊔ ℓh ⊔ ℓs ⊔ ℓl)) where
  field
    neutralAxis : IntrinsicNeutralAxis {ℓn = ℓn} M
    neutralProjection : NeutralProjection neutralAxis
    intrinsicCoordinates :
      IntrinsicColourCoordinates {ℓh = ℓh} {ℓs = ℓs} {ℓl = ℓl}
        neutralAxis

open SchrodingerColourDASHIBridge public

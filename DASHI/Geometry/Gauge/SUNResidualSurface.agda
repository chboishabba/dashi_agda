module DASHI.Geometry.Gauge.SUNResidualSurface where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])
open import Data.Unit.Base using (⊤)

open import DASHI.Geometry.Gauge.SUNPrimitives

data SUNResidualSurfaceObligation : Set where
  needsResidualMetricComputation : SUNResidualSurfaceObligation
  needsResidualDeterminantRoute  : SUNResidualSurfaceObligation
  needsResidualTraceRoute        : SUNResidualSurfaceObligation
  needsResidualCurvatureAudit    : SUNResidualSurfaceObligation
  needsResidualCentreAudit       : SUNResidualSurfaceObligation

canonicalSUNResidualSurfaceObligations : List SUNResidualSurfaceObligation
canonicalSUNResidualSurfaceObligations =
  needsResidualMetricComputation
  ∷ needsResidualDeterminantRoute
  ∷ needsResidualTraceRoute
  ∷ needsResidualCurvatureAudit
  ∷ needsResidualCentreAudit
  ∷ []

record SUNResidualSurface (N : Nat) : Set₁ where
  field
    metricLeak : ResidualStatus
    determinantLeak : ResidualStatus
    traceLeak : ResidualStatus
    curvatureStatus : ResidualStatus
    bianchiLeak : ResidualStatus
    centreBlindness : ResidualStatus
    exactSUNLane :
      metricLeak ≡ zero →
      determinantLeak ≡ zero →
      traceLeak ≡ zero →
      Set
    openObligations : List SUNResidualSurfaceObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalSUNResidualSurfaceObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalSUNResidualSurface : (N : Nat) → SUNResidualSurface N
canonicalSUNResidualSurface N = record
  { metricLeak = zero
  ; determinantLeak = zero
  ; traceLeak = zero
  ; curvatureStatus = nonzero
  ; bianchiLeak = zero
  ; centreBlindness = unknown
  ; exactSUNLane = λ _ _ _ → ⊤
  ; openObligations = canonicalSUNResidualSurfaceObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

module DASHI.Physics.YangMills.BalabanPolymerDiameterEntropyLight where

------------------------------------------------------------------------
-- Lightweight YM audit surface for P06/P07/P08/P09.
--
-- This module deliberately carries only the theorem-surface records and
-- their source/status metadata.  The heavyweight polymer implementation
-- remains in BalabanPolymerDiameterEntropy; it imports graph combinatorics,
-- SFGC, large-field, and transitive Closure/Triadic arithmetic modules.
-- Keeping this audit boundary separate makes the YM gate checkable without
-- elaborating that unrelated graph.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface using
  ( ProofTargetSurface
  )
open import DASHI.Physics.YangMills.P01P33ProofSurfaces using
  ( polymerAnimalCountingBoundSurface
  ; kPSummabilityBoundSurface
  ; pZeroPositiveSurface
  ; entropyBeatenByFullDecaySurface
  )

record LightweightPolymerAuditSurface : Set where
  field
    p06AnimalCounting : ProofTargetSurface
    p07KPSummability  : ProofTargetSurface
    p08PZeroPositive  : ProofTargetSurface
    p09FullDecay      : ProofTargetSurface
    sourceSurfacesAreCanonical :
      p06AnimalCounting ≡ polymerAnimalCountingBoundSurface
    p07SurfaceIsCanonical :
      p07KPSummability ≡ kPSummabilityBoundSurface
    p08SurfaceIsCanonical :
      p08PZeroPositive ≡ pZeroPositiveSurface
    p09SurfaceIsCanonical :
      p09FullDecay ≡ entropyBeatenByFullDecaySurface
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalLightweightPolymerAuditSurface : LightweightPolymerAuditSurface
canonicalLightweightPolymerAuditSurface = record
  { p06AnimalCounting = polymerAnimalCountingBoundSurface
  ; p07KPSummability  = kPSummabilityBoundSurface
  ; p08PZeroPositive  = pZeroPositiveSurface
  ; p09FullDecay      = entropyBeatenByFullDecaySurface
  ; sourceSurfacesAreCanonical = refl
  ; p07SurfaceIsCanonical = refl
  ; p08SurfaceIsCanonical = refl
  ; p09SurfaceIsCanonical = refl
  ; noClayPromotion = refl
  }

lightweightPolymerAuditReady : Bool
lightweightPolymerAuditReady = true

lightweightPolymerAuditNoPromotion :
  lightweightPolymerAuditReady ≡ true
lightweightPolymerAuditNoPromotion = refl

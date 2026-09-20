module DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact where

------------------------------------------------------------------------
-- RELEASED D / SOURCE-NATIVE selected_periodic_candidate BODY
--
-- Port of LocalScheduleWitness.selected_periodic_candidate at its exact
-- dependency boundary.  The theorem itself is only a composition:
--
--   selected schedule
--     -> away extensions
--     -> origin blowup
--     -> spatial-cut divergence
--     -> MixedPeriodicAssembly.exists_candidate_force.
--
-- The hard construction is below these producers; this module removes the
-- theorem body itself from the native reconstruction debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_)

record SelectedPeriodicCandidateSurface : Set₁ where
  field
    Schedule : Set
    Force : Set
    Candidate : Force → Set
    SmoothForce : Force → Set

    AwayExtensions : Schedule → Set
    OriginBlowup : Schedule → Set
    SpatialCutDivergence : Schedule → Set
    SupportData : Schedule → Set
    VanishingResidualJets : Schedule → Set

open SelectedPeriodicCandidateSurface public

record SelectedPeriodicCandidateRules
    (S : SelectedPeriodicCandidateSurface) : Set₁ where
  field
    selectedAwayExtensions :
      (a : Schedule S) → AwayExtensions S a

    selectedOriginBlowup :
      (a : Schedule S) → OriginBlowup S a

    selectedSpatialCutDivergence :
      (a : Schedule S) → SpatialCutDivergence S a

    selectedSupportData :
      (a : Schedule S) → SupportData S a

    selectedVanishingResidualJets :
      (a : Schedule S) → VanishingResidualJets S a

    existsCandidateForce :
      (a : Schedule S) →
      AwayExtensions S a →
      OriginBlowup S a →
      SpatialCutDivergence S a →
      SupportData S a →
      VanishingResidualJets S a →
      Σ (Force S) λ f → Candidate S f × SmoothForce S f

open SelectedPeriodicCandidateRules public

selectedPeriodicCandidate :
  ∀ {S} →
  SelectedPeriodicCandidateRules S →
  (a : Schedule S) →
  Σ (Force S) λ f → Candidate S f × SmoothForce S f
selectedPeriodicCandidate R a =
  existsCandidateForce R a
    (selectedAwayExtensions R a)
    (selectedOriginBlowup R a)
    (selectedSpatialCutDivergence R a)
    (selectedSupportData R a)
    (selectedVanishingResidualJets R a)

selectedPeriodicCandidateBodyPorted : Bool
selectedPeriodicCandidateBodyPorted = true

awayExtensionsProducerClosedHere : Bool
awayExtensionsProducerClosedHere = false

originBlowupProducerClosedHere : Bool
originBlowupProducerClosedHere = false

spatialCutDivergenceProducerClosedHere : Bool
spatialCutDivergenceProducerClosedHere = false

mixedPeriodicAssemblyProducerClosedHere : Bool
mixedPeriodicAssemblyProducerClosedHere = false

clayPromotion : Bool
clayPromotion = false

selectedPeriodicCandidateBodyPortedIsTrue :
  selectedPeriodicCandidateBodyPorted ≡ true
selectedPeriodicCandidateBodyPortedIsTrue = refl

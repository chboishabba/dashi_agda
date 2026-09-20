module DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedCompactCandidateFromPeriodicExact where

------------------------------------------------------------------------
-- RELEASED C / selected_compact_candidate REUSES PERIODIC CANDIDATE
--
-- Port of LocalScheduleWitness.selected_compact_candidate:
--
--   selected_periodic_candidate ha
--      -> forcing, CandidateProperties, smooth forcing
--      -> R3CompactCandidate.ActualCandidate.of_localized_fields
--      -> compact whole-space candidate.
--
-- Thus C does not independently rebuild the schedule/candidate construction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedSelectedPeriodicCandidateNativeExact as D

record CompactLocalizationRules
    (S : D.SelectedPeriodicCandidateSurface) : Set₁ where
  field
    CompactCandidate : D.Force S → Set

    ofLocalizedFields :
      (f : D.Force S) →
      D.Candidate S f →
      D.SmoothForce S f →
      CompactCandidate f

open CompactLocalizationRules public

selectedCompactCandidate :
  ∀ {S} →
  (periodicRules : D.SelectedPeriodicCandidateRules S) →
  (localize : CompactLocalizationRules S) →
  (a : D.Schedule S) →
  Σ (D.Force S) λ f → CompactCandidate localize f
selectedCompactCandidate periodicRules localize a
  with D.selectedPeriodicCandidate periodicRules a
... | f , candidate , smooth =
  f , ofLocalizedFields localize f candidate smooth

cReusesSelectedPeriodicCandidate : Bool
cReusesSelectedPeriodicCandidate = true

selectedCompactCandidateBodyPorted : Bool
selectedCompactCandidateBodyPorted = true

r3LocalizationOfPeriodicFieldsClosedHere : Bool
r3LocalizationOfPeriodicFieldsClosedHere = false

wholeSpaceComparisonExclusionClosedHere : Bool
wholeSpaceComparisonExclusionClosedHere = false

clayPromotion : Bool
clayPromotion = false

cReusesSelectedPeriodicCandidateIsTrue :
  cReusesSelectedPeriodicCandidate ≡ true
cReusesSelectedPeriodicCandidateIsTrue = refl

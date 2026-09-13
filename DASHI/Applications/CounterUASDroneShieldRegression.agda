module DASHI.Applications.CounterUASDroneShieldRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASDroneShieldExact as CUAS
import DASHI.Applications.CounterUASSOTASourceAtlasExact as Sources
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- Regression surface for the defensive counter-UAS architecture.
--
-- The production owner is required to keep sensing, fused inference,
-- operating context, threat assessment, and mitigation authority distinct.
------------------------------------------------------------------------

record CounterUASDroneShieldRegression : Set₁ where
  constructor counterUASDroneShieldRegression
  field
    passiveRFIsObservationNotThreat :
      CUAS.passiveRFObservationDoesNotCreateThreatAuthority ≡ true
    detectionIsNotMitigationAuthority :
      CUAS.detectionDoesNotCreateMitigationAuthority ≡ true
    threatAssessmentIsNotMitigationAuthority :
      CUAS.threatAssessmentDoesNotCreateMitigationAuthority ≡ true
    unknownEmitterIsNotKnownIdentity :
      CUAS.unknownEmitterDoesNotCreateKnownIdentity ≡ true
    operatingContextRequiredForPortablePerformanceClaim :
      CUAS.performanceClaimRequiresOperatingContext ≡ true
    fusedTrackRetainsObservationProvenance :
      CUAS.fusedTrackRequiresObservationProvenance ≡ true
    trackAloneHasMitigationAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        CUAS.trackOnlyProjection
        CUAS.responseSemantics
        CUAS.mitigationQuery
    academicSourceAtlasNonPromoting :
      Sources.counterUASSOTASourceAtlasCreatesAuthority ≡ false

canonicalCounterUASDroneShieldRegression : CounterUASDroneShieldRegression
canonicalCounterUASDroneShieldRegression =
  counterUASDroneShieldRegression
    refl
    refl
    refl
    refl
    refl
    refl
    CUAS.trackOnlyMitigationAdequacyDefect
    Sources.counterUASSOTASourceAtlasCreatesAuthorityIsFalse

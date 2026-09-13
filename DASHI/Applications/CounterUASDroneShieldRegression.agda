module DASHI.Applications.CounterUASDroneShieldRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASDroneShieldExact as CUAS
import DASHI.Applications.CounterUASSOTASourceAtlasExact as Sources
import DASHI.Applications.CounterUASOperationalSourceAtlasExact as OperationalSources
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- Regression surface for the defensive counter-UAS architecture.
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
    noCatalogMatchDoesNotMeanNoRFDetection :
      CUAS.noCatalogMatchDoesNotImplyNoDetection ≡ true
    rfActivityDoesNotCreateEmitterIdentity :
      CUAS.rfActivityDoesNotCreateEmitterIdentity ≡ true
    openSetDetectionDoesNotCreateKnownClass :
      CUAS.openSetDetectionDoesNotCreateKnownClass ≡ true
    generatedSignatureIsReferenceNotIdentityAuthority :
      CUAS.generatedSignatureDoesNotCreateIdentityAuthority ≡ true
    catalogProjectionHasDetectionAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        CUAS.catalogOnlyProjection
        CUAS.rfSemantics
        CUAS.activityQuery
    anomalyProjectionHasIdentityAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        CUAS.anomalyOnlyProjection
        CUAS.openSetSemantics
        CUAS.identityQuery
    trackAloneHasMitigationAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        CUAS.trackOnlyProjection
        CUAS.responseSemantics
        CUAS.mitigationQuery
    specificationAloneHasPerformanceAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        CUAS.specificationProjection
        CUAS.evaluationSemantics
        CUAS.fieldPerformanceQuery
    academicSourceAtlasNonPromoting :
      Sources.counterUASSOTASourceAtlasCreatesAuthority ≡ false
    operationalSourceAtlasNonPromoting :
      OperationalSources.counterUASOperationalSourceAtlasCreatesAuthority ≡ false
    rfAI3ClaimSnapshotNonPromoting :
      OperationalSources.rfAI3SnapshotCreatesAuthority ≡ false

canonicalCounterUASDroneShieldRegression : CounterUASDroneShieldRegression
canonicalCounterUASDroneShieldRegression =
  counterUASDroneShieldRegression
    refl refl refl refl refl refl
    refl refl refl refl
    CUAS.catalogOnlyDetectionAdequacyDefect
    CUAS.anomalyOnlyIdentityAdequacyDefect
    CUAS.trackOnlyMitigationAdequacyDefect
    CUAS.specificationOnlyPerformanceAdequacyDefect
    Sources.counterUASSOTASourceAtlasCreatesAuthorityIsFalse
    OperationalSources.counterUASOperationalSourceAtlasCreatesAuthorityIsFalse
    OperationalSources.rfAI3SnapshotCreatesAuthorityIsFalse

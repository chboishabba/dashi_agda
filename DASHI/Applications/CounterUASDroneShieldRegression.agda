module DASHI.Applications.CounterUASDroneShieldRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASDroneShieldExact as CUAS
import DASHI.Applications.CounterUASOpenSetRFExact as OpenRF
import DASHI.Applications.CounterUASSOTASourceAtlasExact as Sources
import DASHI.Applications.CounterUASOpenSetRFSourceAtlasExact as OpenRFSources
import DASHI.Applications.CounterUASOperationalSourceAtlasExact as OperationalSources
import DASHI.Applications.CounterUASSensibLawAuthorityBridgeExact as LegalBridge
import DASHI.Law.SensibLawInternationalInstrumentLifecycleExact as Lifecycle
import DASHI.Law.SensibLawCCWLAWS2026Exact as CCW2026
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball

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
      OpenRF.noCatalogMatchDoesNotImplyNoDetection ≡ true
    rfActivityDoesNotCreateEmitterIdentity :
      OpenRF.rfActivityDoesNotCreateEmitterIdentity ≡ true
    openSetDetectionDoesNotCreateKnownClass :
      OpenRF.openSetDetectionDoesNotCreateKnownClass ≡ true
    generatedSignatureIsReferenceNotIdentityAuthority :
      OpenRF.generatedSignatureDoesNotCreateIdentityAuthority ≡ true
    catalogProjectionHasDetectionAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        OpenRF.catalogOnlyProjection
        OpenRF.rfSemantics
        OpenRF.activityQuery
    anomalyProjectionHasIdentityAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        OpenRF.anomalyOnlyProjection
        OpenRF.openSetSemantics
        OpenRF.identityQuery
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
    openSetAcademicSourceAtlasNonPromoting :
      OpenRFSources.counterUASOpenSetRFSourceAtlasCreatesAuthority ≡ false
    operationalSourceAtlasNonPromoting :
      OperationalSources.counterUASOperationalSourceAtlasCreatesAuthority ≡ false
    rfAI3ClaimSnapshotNonPromoting :
      OperationalSources.rfAI3SnapshotCreatesAuthority ≡ false
    consensusTextHasBindingAdequacyDefect :
      Adequacy.QueryAdequacyDefect
        Lifecycle.consensusOnlyProjection
        Lifecycle.instrumentSemantics
        Lifecycle.bindingEffectQuery
    joinedLifecycleDeterminesBinding :
      Adequacy.AdequateFor
        Lifecycle.consensusAndInstitutionalProjection
        Lifecycle.instrumentSemantics
        Lifecycle.bindingEffectQuery
    septemberInstrumentNatureStillUnresolved :
      CCW2026.september2026InstrumentNature ≡ Lifecycle.instrumentNatureUnresolved
    ccwOfficialSourceAtlasNonPromoting :
      CCW2026.ccwLAWS2026SourceAtlasCreatesAuthority ≡ false
    ccwAgendaSourceRetainsAttributionSnowball :
      AttributionSnowball.SourceRoleSnowballReceipt CCW2026.ccwGGE2026AgendaSource
    domesticAuthorityDoesNotSetInternationalApplicability :
      LegalBridge.domesticMitigationAuthorityDoesNotCreateInternationalLawApplicability ≡ true
    technicalAutonomyDoesNotCreateLawfulEngagement :
      LegalBridge.technicalAutonomyDoesNotCreateLawfulAutonomousEngagement ≡ true

canonicalCounterUASDroneShieldRegression : CounterUASDroneShieldRegression
canonicalCounterUASDroneShieldRegression =
  counterUASDroneShieldRegression
    refl refl refl refl refl refl
    refl refl refl refl
    OpenRF.catalogOnlyDetectionAdequacyDefect
    OpenRF.anomalyOnlyIdentityAdequacyDefect
    CUAS.trackOnlyMitigationAdequacyDefect
    CUAS.specificationOnlyPerformanceAdequacyDefect
    Sources.counterUASSOTASourceAtlasCreatesAuthorityIsFalse
    OpenRFSources.counterUASOpenSetRFSourceAtlasCreatesAuthorityIsFalse
    OperationalSources.counterUASOperationalSourceAtlasCreatesAuthorityIsFalse
    OperationalSources.rfAI3SnapshotCreatesAuthorityIsFalse
    Lifecycle.consensusOnlyBindingAdequacyDefect
    Lifecycle.consensusAndInstitutionalDetermineBinding
    refl
    CCW2026.ccwLAWS2026SourceAtlasCreatesAuthorityIsFalse
    CCW2026.ccwGGE2026AgendaSourceSnowballReceipt
    refl
    refl

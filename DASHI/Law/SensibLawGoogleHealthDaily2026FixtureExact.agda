module DASHI.Law.SensibLawGoogleHealthDaily2026FixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Law.SensibLawHealthRecordEvidenceExact as Health

------------------------------------------------------------------------
-- CONCRETE GOOGLE-HEALTH DAILY EXPORT FIXTURE
--
-- User-provided workbook:
--   google_health_daily_2026-08-10_to_2026-09-09
--
-- The filename advertises through 2026-09-09, but the observed data rows end
-- on 2026-09-08.  The fixture preserves that discrepancy rather than silently
-- manufacturing a 2026-09-09 observation.
--
-- This carrier is useful as a provider-adapter regression and later
-- activity/context series.  It does not backfill 2022 observations and does
-- not establish diagnosis, aggravation, or legal causation.
------------------------------------------------------------------------

googleHealthDaily2026Source : Observation.SourceArtifact
googleHealthDaily2026Source =
  Observation.sourceArtifact
    "google-health-daily-2026-08-10--filename-2026-09-09-observed-2026-09-08"
    Observation.externalSystemArtifact
    "google_health_daily_2026-08-10_to_2026-09-09"
    "Google Health / user-provided daily export"

googleHealthDaily2026Provenance :
  Observation.ProvenanceAnchor googleHealthDaily2026Source
googleHealthDaily2026Provenance =
  Observation.provenanceAnchor
    "user-provided workbook preserved as exact source carrier"
    "30 observed daily rows: 2026-08-10 through 2026-09-08"
    "same exported workbook / same subject context"
    ⊤

googleHealthDaily2026Artifact : Health.HealthRecordArtifact
googleHealthDaily2026Artifact =
  Health.healthRecordArtifact
    googleHealthDaily2026Source
    Health.wearableSeries
    "user health-record subject"
    "Google Health / connected wearable ecosystem"
    "daily observations"
    "observed 2026-08-10 through 2026-09-08; filename extends to 2026-09-09"
    googleHealthDaily2026Provenance

------------------------------------------------------------------------
-- Exact observed schema in the 2026-09-09-named workbook.
------------------------------------------------------------------------

data GoogleHealthDailyMetric : Set where
  steps : GoogleHealthDailyMetric
  distanceKm : GoogleHealthDailyMetric
  fatBurnZoneMinutes : GoogleHealthDailyMetric
  cardioZoneMinutes : GoogleHealthDailyMetric
  peakZoneMinutes : GoogleHealthDailyMetric

metricReference : GoogleHealthDailyMetric → String
metricReference steps = "steps"
metricReference distanceKm = "distance_km"
metricReference fatBurnZoneMinutes = "fat_burn_zone_minutes"
metricReference cardioZoneMinutes = "cardio_zone_minutes"
metricReference peakZoneMinutes = "peak_zone_minutes"

record GoogleHealthDaily2026SchemaBoundary : Set where
  constructor googleHealthDaily2026SchemaBoundary
  field
    rowCount : String
    declaredFilenameRange : String
    observedDateRange : String

    stepsPresentAllRows : Bool
    stepsPresentAllRowsIsTrue : stepsPresentAllRows ≡ true
    distancePresentAllRows : Bool
    distancePresentAllRowsIsTrue : distancePresentAllRows ≡ true

    zoneMinutesPartiallyPopulated : Bool
    zoneMinutesPartiallyPopulatedIsTrue : zoneMinutesPartiallyPopulated ≡ true
    rowsWithZoneMinuteValues : String

    filenameEndDateHasObservedRow : Bool
    filenameEndDateHasObservedRowIsFalse : filenameEndDateHasObservedRow ≡ false

    totalCaloriesColumnPresent : Bool
    totalCaloriesColumnPresentIsFalse : totalCaloriesColumnPresent ≡ false
    lightMinutesColumnPresent : Bool
    lightMinutesColumnPresentIsFalse : lightMinutesColumnPresent ≡ false
    moderateMinutesColumnPresent : Bool
    moderateMinutesColumnPresentIsFalse : moderateMinutesColumnPresent ≡ false
    vigorousMinutesColumnPresent : Bool
    vigorousMinutesColumnPresentIsFalse : vigorousMinutesColumnPresent ≡ false

    heartRateColumnPresent : Bool
    heartRateColumnPresentIsFalse : heartRateColumnPresent ≡ false
    bloodPressureColumnPresent : Bool
    bloodPressureColumnPresentIsFalse : bloodPressureColumnPresent ≡ false
    sleepColumnPresent : Bool
    sleepColumnPresentIsFalse : sleepColumnPresent ≡ false
    spo2ColumnPresent : Bool
    spo2ColumnPresentIsFalse : spo2ColumnPresent ≡ false
    hrvColumnPresent : Bool
    hrvColumnPresentIsFalse : hrvColumnPresent ≡ false

    exportCanBackfill2022 : Bool
    exportCanBackfill2022IsFalse : exportCanBackfill2022 ≡ false
    exportAutomaticallyEstablishesDiagnosis : Bool
    exportAutomaticallyEstablishesDiagnosisIsFalse :
      exportAutomaticallyEstablishesDiagnosis ≡ false
    exportAutomaticallyEstablishesHousingCausation : Bool
    exportAutomaticallyEstablishesHousingCausationIsFalse :
      exportAutomaticallyEstablishesHousingCausation ≡ false

canonicalGoogleHealthDaily2026SchemaBoundary :
  GoogleHealthDaily2026SchemaBoundary
canonicalGoogleHealthDaily2026SchemaBoundary =
  googleHealthDaily2026SchemaBoundary
    "30 daily rows"
    "filename: 2026-08-10 through 2026-09-09"
    "observed rows: 2026-08-10 through 2026-09-08"
    true refl
    true refl
    true refl
    "7 rows carry zone-minute values; 23 rows are missing all three zone-minute fields"
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Provider-neutral time-series projection witness.
------------------------------------------------------------------------

googleHealthDailyObservation :
  (metric : GoogleHealthDailyMetric) →
  (dateReference valueReference unitReference : String) →
  Observation.TimeSeriesObservation
googleHealthDailyObservation metric dateReference valueReference unitReference =
  Observation.timeSeriesObservation
    "user health-record subject"
    (metricReference metric)
    dateReference
    valueReference
    unitReference
    googleHealthDaily2026Source
    googleHealthDaily2026Provenance
    ⊤

------------------------------------------------------------------------
-- Historical-source boundary.
------------------------------------------------------------------------

record HistoricalPhysiologySeparationBoundary : Set where
  constructor historicalPhysiologySeparationBoundary
  field
    qcat2022PhysiologyAndGoogleHealth2026AreSameCarrier : Bool
    qcat2022PhysiologyAndGoogleHealth2026AreSameCarrierIsFalse :
      qcat2022PhysiologyAndGoogleHealth2026AreSameCarrier ≡ false
    qcat2022PhysiologyMayRemainHistoricalSource : Bool
    qcat2022PhysiologyMayRemainHistoricalSourceIsTrue :
      qcat2022PhysiologyMayRemainHistoricalSource ≡ true
    laterWearableExportMayServeAsProviderAdapterRegression : Bool
    laterWearableExportMayServeAsProviderAdapterRegressionIsTrue :
      laterWearableExportMayServeAsProviderAdapterRegression ≡ true

canonicalHistoricalPhysiologySeparationBoundary :
  HistoricalPhysiologySeparationBoundary
canonicalHistoricalPhysiologySeparationBoundary =
  historicalPhysiologySeparationBoundary
    false refl
    true refl
    true refl

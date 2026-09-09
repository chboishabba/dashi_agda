module DASHI.Law.SensibLawGoogleHealthPoints20260907_09FixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawHealthEvidenceProcessorParityExact as Processor

------------------------------------------------------------------------
-- PRIVACY-SAFE GOOGLE HEALTH / FITBIT POINT-LEVEL EXPORT FIXTURE
--
-- Source carrier:
--   google_health_points_2026-09-07_to_2026-09-09.tsv
--
-- This public fixture records carrier/schema/count receipts only.  Personal
-- physiological values, extrema, means, and timestamp-level samples remain
-- outside the public repository.
------------------------------------------------------------------------

sourceReference : String
sourceReference = "google_health_points_2026-09-07_to_2026-09-09.tsv"

sourceSha256 : String
sourceSha256 = "77886cf570bc55fc7958e4f3d980a1f1661729235d5732f668e7da2e5cb094db"

processorContract : String
processorContract = Processor.processorContractVersion

record GoogleHealthPointsSourceReceipt : Set₁ where
  constructor googleHealthPointsSourceReceipt
  field
    sourceReferenceField : String
    sourceDigestReference : String
    processorContractReference : String
    inputRowCountReference : String
    inputColumnCountReference : String
    heartRateSourceRowsReference : String
    oxygenSaturationSourceRowsReference : String
    hrvSourceRowsReference : String
    normalizedObservationCountReference : String
    heartRateNormalizedCountReference : String
    oxygenNormalizedCountReference : String
    hrvNormalizedCountReference : String
    dailyRestingHeartRateNormalizedCountReference : String
    stepsNormalizedCountReference : String
    distanceNormalizedCountReference : String
    activeEnergyNormalizedCountReference : String
    activeZoneMinutesNormalizedCountReference : String
    processorExecutionReceipt : Set

open GoogleHealthPointsSourceReceipt public

canonicalGoogleHealthPointsSourceReceipt :
  (processorExecutionReceipt : Set) → GoogleHealthPointsSourceReceipt
canonicalGoogleHealthPointsSourceReceipt processorExecutionReceipt =
  googleHealthPointsSourceReceipt
    sourceReference
    sourceSha256
    processorContract
    "42954 source rows"
    "264 source columns"
    "37935 heart-rate source rows"
    "322 oxygen-saturation source rows"
    "55 heart-rate-variability source rows"
    "40071 normalized supported observations"
    "37935 heart-rate observations"
    "322 oxygen-saturation observations"
    "55 HRV-RMSSD observations"
    "2 daily-resting-heart-rate observations"
    "272 steps observations"
    "272 distance observations"
    "972 active-energy-burned observations"
    "237 active-zone-minutes observations"
    processorExecutionReceipt

record GoogleHealthPointsBoundary : Set where
  constructor googleHealthPointsBoundary
  field
    publicFixturePublishesRawPersonalValues : Bool
    publicFixturePublishesRawPersonalValuesIsFalse :
      publicFixturePublishesRawPersonalValues ≡ false

    sourceRowCountEqualsIndependentClinicalEvidenceCount : Bool
    sourceRowCountEqualsIndependentClinicalEvidenceCountIsFalse :
      sourceRowCountEqualsIndependentClinicalEvidenceCount ≡ false

    unsupportedProviderRowsMayBeSilentlyPromoted : Bool
    unsupportedProviderRowsMayBeSilentlyPromotedIsFalse :
      unsupportedProviderRowsMayBeSilentlyPromoted ≡ false

    physiologicalPointAutomaticallyCreatesDiagnosis : Bool
    physiologicalPointAutomaticallyCreatesDiagnosisIsFalse :
      physiologicalPointAutomaticallyCreatesDiagnosis ≡ false

    physiologicalPointAutomaticallyCreatesLegalCausation : Bool
    physiologicalPointAutomaticallyCreatesLegalCausationIsFalse :
      physiologicalPointAutomaticallyCreatesLegalCausation ≡ false

    2026PointSeriesBackfillsHistorical2022Observation : Bool
    2026PointSeriesBackfillsHistorical2022ObservationIsFalse :
      2026PointSeriesBackfillsHistorical2022Observation ≡ false

canonicalGoogleHealthPointsBoundary : GoogleHealthPointsBoundary
canonicalGoogleHealthPointsBoundary =
  googleHealthPointsBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

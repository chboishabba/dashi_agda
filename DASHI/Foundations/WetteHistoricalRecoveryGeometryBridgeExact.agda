module DASHI.Foundations.WetteHistoricalRecoveryGeometryBridgeExact where

------------------------------------------------------------------------
-- WETTE HISTORICAL RECOVERY -> GENERIC FORMALIZATION RECOVERY GEOMETRY
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FormalizationRecoveryGeometryExact as Recovery
import DASHI.Core.FormalizationRecoverySourceRegistryExact as Calibration
import DASHI.Foundations.WetteHistoricalRecoveryFrontierExact as Frontier
import DASHI.Foundations.WetteHistoricalSourceAtlasExact as Source

------------------------------------------------------------------------
-- Programme-level recovery profile.
--
-- Wette 1969 and 1970 primary texts plus the 1972 Kreisel/Zucker review have
-- now been inspected directly.  Therefore primaryTextInspected is inhabited.
-- The next stages remain deliberately uninhabited: selected source facts and
-- rule surfaces have been extracted, but the complete historical rule system,
-- deduction-indexed interpretation, and late contradiction proof objects have
-- not yet been transcribed into exact Agda data and discharged.
------------------------------------------------------------------------

currentWetteRecoveryProfile : Recovery.RecoveryStageProfile
currentWetteRecoveryProfile =
  Recovery.recoveryStageProfile supports
  where
    supports : Recovery.RecoveryStage → Set
    supports Recovery.sourceLocated = ⊤
    supports Recovery.primaryTextInspected = ⊤
    supports Recovery.transcriptionExtracted = ⊥
    supports Recovery.formalObjectReconstructed = ⊥
    supports Recovery.theoremObligationDischarged = ⊥

wetteSourceCorpusLocated :
  Recovery.Supports currentWetteRecoveryProfile Recovery.sourceLocated
wetteSourceCorpusLocated = tt

wetteProgrammePrimaryTextInspected :
  Recovery.Supports currentWetteRecoveryProfile Recovery.primaryTextInspected
wetteProgrammePrimaryTextInspected = tt

wette1969PrimaryTextInspected : ⊤
wette1969PrimaryTextInspected = tt

wette1970PrimaryTextInspected : ⊤
wette1970PrimaryTextInspected = tt

kreiselZucker1972ReviewInspected : ⊤
kreiselZucker1972ReviewInspected = tt

criticalLate1974FormalObjectsStillUnrecovered : ⊤
criticalLate1974FormalObjectsStillUnrecovered = tt

wetteCompleteTranscriptionNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.transcriptionExtracted
wetteCompleteTranscriptionNotYetCertified impossible = impossible

wetteFormalObjectRecoveryNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.formalObjectReconstructed
wetteFormalObjectRecoveryNotYetCertified impossible = impossible

wetteTheoremDischargeNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.theoremObligationDischarged
wetteTheoremDischargeNotYetCertified impossible = impossible

formalizationRecoveryCalibrationSource : Calibration.CalibrationSource
formalizationRecoveryCalibrationSource =
  Calibration.aspertNaiboSacerdotiCoen2026

representationTranslationCalibrationSource : Calibration.CalibrationSource
representationTranslationCalibrationSource = Calibration.wagner2019

consistencyBoundaryCalibrationSource : Calibration.CalibrationSource
consistencyBoundaryCalibrationSource = Calibration.chow2018

historicalGrammarSource : Source.WetteSource
historicalGrammarSource = Frontier.preferredSource Frontier.grammarTarget

historicalConsistencyReductionSource : Source.WetteSource
historicalConsistencyReductionSource =
  Frontier.preferredSource Frontier.reductionTarget

historicalComparisonTranslationSource : Source.WetteSource
historicalComparisonTranslationSource =
  Frontier.preferredSource Frontier.comparisonTranslationTarget

record WetteHistoricalRecoveryGeometryBoundary : Set where
  constructor wetteHistoricalRecoveryGeometryBoundary
  field
    bibliographicLocationIsNotPrimaryTextInspection : Bool
    bibliographicLocationIsNotPrimaryTextInspectionIsTrue :
      bibliographicLocationIsNotPrimaryTextInspection ≡ true

    central1969And1970PrimarySourcesNowInspected : Bool
    central1969And1970PrimarySourcesNowInspectedIsTrue :
      central1969And1970PrimarySourcesNowInspected ≡ true

    primaryInspectionEqualsCompleteHistoricalTranscription : Bool
    primaryInspectionEqualsCompleteHistoricalTranscriptionIsFalse :
      primaryInspectionEqualsCompleteHistoricalTranscription ≡ false

    partialExtractionEqualsCriticalFormalObjectRecovery : Bool
    partialExtractionEqualsCriticalFormalObjectRecoveryIsFalse :
      partialExtractionEqualsCriticalFormalObjectRecovery ≡ false

    transcriptionAndReconstructionKeptSeparate : Bool
    transcriptionAndReconstructionKeptSeparateIsTrue :
      transcriptionAndReconstructionKeptSeparate ≡ true

    calibrationLiteratureReplacesWettePrimarySources : Bool
    calibrationLiteratureReplacesWettePrimarySourcesIsFalse :
      calibrationLiteratureReplacesWettePrimarySources ≡ false

    sourceLocationIsAlreadyTheoremDischarge : Bool
    sourceLocationIsAlreadyTheoremDischargeIsFalse :
      sourceLocationIsAlreadyTheoremDischarge ≡ false

canonicalWetteHistoricalRecoveryGeometryBoundary :
  WetteHistoricalRecoveryGeometryBoundary
canonicalWetteHistoricalRecoveryGeometryBoundary =
  wetteHistoricalRecoveryGeometryBoundary
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

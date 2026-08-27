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
-- now been inspected directly. Exact transcription has begun: the 1969
-- signature is typed with source arities; rules 0.1/0.2 have exact bodies; the
-- p.193 revision surface is represented; and the source-stated dependency,
-- substitution-order, and premise-judgement typing geometry of critical rules
-- 9.1.5 and 9.3.24/25 is now typed. The complete `transcriptionExtracted`
-- stage remains uninhabited.
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

partial1969HistoricalTranscriptionStarted : ⊤
partial1969HistoricalTranscriptionStarted = tt

critical915And9324x25DependencyStructureRecovered : ⊤
critical915And9324x25DependencyStructureRecovered = tt

critical915And9324x25SubstitutionOrderRecovered : ⊤
critical915And9324x25SubstitutionOrderRecovered = tt

critical915And9324x25PremiseKindsRecovered : ⊤
critical915And9324x25PremiseKindsRecovered = tt

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

    partialHistoricalTranscriptionNowStarted : Bool
    partialHistoricalTranscriptionNowStartedIsTrue :
      partialHistoricalTranscriptionNowStarted ≡ true

    criticalRuleDependencyGeometryNowRecovered : Bool
    criticalRuleDependencyGeometryNowRecoveredIsTrue :
      criticalRuleDependencyGeometryNowRecovered ≡ true

    criticalSubstitutionOrderGeometryNowRecovered : Bool
    criticalSubstitutionOrderGeometryNowRecoveredIsTrue :
      criticalSubstitutionOrderGeometryNowRecovered ≡ true

    criticalPremiseTypingGeometryNowRecovered : Bool
    criticalPremiseTypingGeometryNowRecoveredIsTrue :
      criticalPremiseTypingGeometryNowRecovered ≡ true

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
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

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
-- The 1970 Wette primary text and the 1972 Kreisel/Zucker contemporary review
-- have now been inspected and selected source facts extracted.  The programme
-- profile remains conservative because the critical 1969 formal-system pages
-- and the late 1974 contradiction / translation texts have not yet been
-- source-transcribed into the exact historical calculus and proof objects.
------------------------------------------------------------------------

currentWetteRecoveryProfile : Recovery.RecoveryStageProfile
currentWetteRecoveryProfile =
  Recovery.recoveryStageProfile supports
  where
    supports : Recovery.RecoveryStage → Set
    supports Recovery.sourceLocated = ⊤
    supports Recovery.primaryTextInspected = ⊥
    supports Recovery.transcriptionExtracted = ⊥
    supports Recovery.formalObjectReconstructed = ⊥
    supports Recovery.theoremObligationDischarged = ⊥

wetteSourceCorpusLocated :
  Recovery.Supports currentWetteRecoveryProfile Recovery.sourceLocated
wetteSourceCorpusLocated = tt

-- Source-specific receipts: partial corpus inspection is real progress, but it
-- is not promoted to programme-level formal-object recovery.
wette1970PrimaryTextInspected : ⊤
wette1970PrimaryTextInspected = tt

kreiselZucker1972ReviewInspected : ⊤
kreiselZucker1972ReviewInspected = tt

critical1969And1974FormalObjectsStillUnrecovered : ⊤
critical1969And1974FormalObjectsStillUnrecovered = tt

wetteProgrammePrimaryTextInspectionNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.primaryTextInspected
wetteProgrammePrimaryTextInspectionNotYetCertified impossible = impossible

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

    somePrimarySourcesNowInspected : Bool
    somePrimarySourcesNowInspectedIsTrue :
      somePrimarySourcesNowInspected ≡ true

    partialInspectionEqualsCriticalFormalObjectRecovery : Bool
    partialInspectionEqualsCriticalFormalObjectRecoveryIsFalse :
      partialInspectionEqualsCriticalFormalObjectRecovery ≡ false

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
    true refl
    false refl
    false refl

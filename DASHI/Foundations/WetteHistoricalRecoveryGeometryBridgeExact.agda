module DASHI.Foundations.WetteHistoricalRecoveryGeometryBridgeExact where

------------------------------------------------------------------------
-- WETTE HISTORICAL RECOVERY -> GENERIC FORMALIZATION RECOVERY GEOMETRY
--
-- Cross-pollination owner: the Wette reconstruction now uses the generic
-- distinction between translation/transcription and reconstruction rather than
-- treating bibliographic location, textual extraction, formal reconstruction,
-- and theorem discharge as one boolean notion of "recovered".
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FormalizationRecoveryGeometryExact as Recovery
import DASHI.Core.FormalizationRecoverySourceRegistryExact as Calibration
import DASHI.Foundations.WetteHistoricalRecoveryFrontierExact as Frontier
import DASHI.Foundations.WetteHistoricalSourceAtlasExact as Source

------------------------------------------------------------------------
-- Current programme-level recovery profile.
--
-- We have stable source locations / bibliographic handles for the main corpus,
-- but have not yet source-transcribed Wette's historical calculus into exact
-- syntax and proof objects.  Therefore only the first generic recovery stage is
-- inhabited here.  This is deliberately conservative.
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

wettePrimaryTextInspectionNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.primaryTextInspected
wettePrimaryTextInspectionNotYetCertified impossible = impossible

wetteFormalObjectRecoveryNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.formalObjectReconstructed
wetteFormalObjectRecoveryNotYetCertified impossible = impossible

wetteTheoremDischargeNotYetCertified :
  ¬ Recovery.Supports currentWetteRecoveryProfile Recovery.theoremObligationDischarged
wetteTheoremDischargeNotYetCertified impossible = impossible

------------------------------------------------------------------------
-- Source attribution bridge.
--
-- Asperti/Naibo/Sacerdoti Coen calibrate the distinction between translation
-- difficulty and mathematical reconstruction difficulty; Wagner calibrates
-- translation between presentations as partial/context-sensitive; Chow
-- calibrates the separation between finite syntactic consistency statements,
-- arithmetized Con(T), and stronger external metatheoretic commitments.
------------------------------------------------------------------------

formalizationRecoveryCalibrationSource : Calibration.CalibrationSource
formalizationRecoveryCalibrationSource =
  Calibration.aspertNaiboSacerdotiCoen2026

representationTranslationCalibrationSource : Calibration.CalibrationSource
representationTranslationCalibrationSource = Calibration.wagner2019

consistencyBoundaryCalibrationSource : Calibration.CalibrationSource
consistencyBoundaryCalibrationSource = Calibration.chow2018

------------------------------------------------------------------------
-- Historical recovery still points to Wette's own sources for theorem content.
-- Generic calibration literature does not replace primary-source extraction.
------------------------------------------------------------------------

historicalGrammarSource : Source.WetteSource
historicalGrammarSource = Frontier.preferredSource Frontier.grammarTarget

historicalConsistencyReductionSource : Source.WetteSource
historicalConsistencyReductionSource =
  Frontier.preferredSource Frontier.reductionTarget

historicalComparisonTranslationSource : Source.WetteSource
historicalComparisonTranslationSource =
  Frontier.preferredSource Frontier.comparisonTranslationTarget

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record WetteHistoricalRecoveryGeometryBoundary : Set where
  constructor wetteHistoricalRecoveryGeometryBoundary
  field
    bibliographicLocationIsNotPrimaryTextInspection : Bool
    bibliographicLocationIsNotPrimaryTextInspectionIsTrue :
      bibliographicLocationIsNotPrimaryTextInspection ≡ true

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

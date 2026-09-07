module DASHI.Culture.MaiwaldActionSpectroscopyProjectSuccessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- JPL SURP SAME-PROJECT SUCCESSION
--
-- JPL's SURP archive lists the same project title in 2023, 2024 and 2025.
-- 2023: Frank W. Maiwald (PI), Robert P. Hodyss, Mathias Weber, Lane Terry.
-- 2024/2025: Deacon J. Nemchick (PI), Robert P. Hodyss, Mathias Weber.
-- This closes project-level leadership succession and overlapping-team
-- continuity.  It does not prove transfer of every calibration, qualification,
-- apparatus, failure-history or tacit-execution carrier.
------------------------------------------------------------------------

record ProjectSuccessionReceipt : Set where
  constructor project-succession-receipt
  field
    projectTitle : String
    predecessorPI : String
    successorPI : String
    overlappingTeam : String
    predecessorReference : String
    successorReference : String
    sameProjectTitleOwned : Bool
    sameProjectTitleOwnedIsTrue : sameProjectTitleOwned ≡ true
    successorPIRecorded : Bool
    successorPIRecordedIsTrue : successorPIRecorded ≡ true
    overlappingTeamRecorded : Bool
    overlappingTeamRecordedIsTrue : overlappingTeamRecorded ≡ true

open ProjectSuccessionReceipt public

maiWaldActionSpectroscopySuccession : ProjectSuccessionReceipt
maiWaldActionSpectroscopySuccession = project-succession-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Frank W. Maiwald"
  "Deacon J. Nemchick"
  "Robert P. Hodyss and Mathias Weber continue from FY23 into FY24/FY25; Lane Terry appears in FY23 and as graduate participant in FY24 poster"
  "JPL FY23 SURP poster SP23012p and JPL SURP archive"
  "JPL FY24 poster SP23012p and JPL SURP archive; same project continues in FY25"
  true refl
  true refl
  true refl

record ProjectVsCarrierBoundary : Set where
  constructor project-vs-carrier-boundary
  field
    projectSuccessionImpliesCalibrationTransferred : Bool
    projectSuccessionImpliesCalibrationTransferredIsFalse :
      projectSuccessionImpliesCalibrationTransferred ≡ false
    successorPIImpliesSameTacitKnowledge : Bool
    successorPIImpliesSameTacitKnowledgeIsFalse :
      successorPIImpliesSameTacitKnowledge ≡ false
    overlappingTeamSupportsContinuitySearch : Bool
    overlappingTeamSupportsContinuitySearchIsTrue :
      overlappingTeamSupportsContinuitySearch ≡ true

canonicalProjectVsCarrierBoundary : ProjectVsCarrierBoundary
canonicalProjectVsCarrierBoundary = project-vs-carrier-boundary false refl false refl true refl

data MaiwaldSuccessionReverseTarget : Set where
  acquireApparatusConfigurationContinuity : MaiwaldSuccessionReverseTarget
  acquireCalibrationTransfer : MaiwaldSuccessionReverseTarget
  acquireTagResponseModelContinuity : MaiwaldSuccessionReverseTarget
  acquireFailureHistoryTransfer : MaiwaldSuccessionReverseTarget
  acquireQualificationTransfer : MaiwaldSuccessionReverseTarget
  acquireRepositoryOrNotebookContinuity : MaiwaldSuccessionReverseTarget

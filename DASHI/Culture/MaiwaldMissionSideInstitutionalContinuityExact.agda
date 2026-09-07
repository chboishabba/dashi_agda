module DASHI.Culture.MaiwaldMissionSideInstitutionalContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record MissionSideContinuityReceipt : Set where
  constructor mission-side-continuity-receipt
  field
    successorScientist : String
    currentInstitutionalRole : String
    currentLaboratorySurface : String
    missionUseSurface : String
    sourceReference : String
    boundedReading : String

open MissionSideContinuityReceipt public

maiwaldMissionSideContinuity : MissionSideContinuityReceipt
maiwaldMissionSideContinuity = mission-side-continuity-receipt
  "Deacon J. Nemchick"
  "JPL research scientist and instrument development"
  "JPL Spectroscopy Laboratory / Laboratory Studies and Atmospheric Observations"
  "JPL spectroscopy work supports instrument design and interpretation for NASA planetary, atmospheric and astrophysical missions"
  "JPL Science Deacon Nemchick profile; JPL Spectroscopy Laboratory current pages; JPL SURP 2024 project archive"
  "Institutional continuity on the JPL spectroscopy/instrument-development side is source-backed. This does not establish transfer of Frank Maiwald's exact calibration archive, qualification evidence, mission-specific configuration, failure history or tacit workflow."

record MissionSideBoundary : Set where
  constructor mission-side-boundary
  field
    successorPIImpliesExactCalibrationTransfer : Bool
    successorPIImpliesExactCalibrationTransferIsFalse : successorPIImpliesExactCalibrationTransfer ≡ false
    currentLabRoleImpliesSameMissionConfiguration : Bool
    currentLabRoleImpliesSameMissionConfigurationIsFalse : currentLabRoleImpliesSameMissionConfiguration ≡ false
    currentInstrumentDevelopmentImpliesMissionQualificationRedundant : Bool
    currentInstrumentDevelopmentImpliesMissionQualificationRedundantIsFalse : currentInstrumentDevelopmentImpliesMissionQualificationRedundant ≡ false

canonicalMissionSideBoundary : MissionSideBoundary
canonicalMissionSideBoundary = mission-side-boundary false refl false refl false refl

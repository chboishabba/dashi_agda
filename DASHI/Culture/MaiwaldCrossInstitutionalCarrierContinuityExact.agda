module DASHI.Culture.MaiwaldCrossInstitutionalCarrierContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C

weberApparatusCustody2023 : C.CapabilityCustodyReceipt
weberApparatusCustody2023 = C.capability-custody-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  C.physicalApparatus C.crossInstitutionalCustody
  "J. Mathias Weber research group, University of Colorado Boulder"
  "JPL FY23 SURP poster RPC#sp23012 / CL#23-5018"
  "FY23 explicitly describes the active Boulder/Weber-group cryogenic action-spectroscopy apparatus used by the collaboration."

weberApparatusCustody2024 : C.CapabilityCustodyReceipt
weberApparatusCustody2024 = C.capability-custody-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  C.physicalApparatus C.crossInstitutionalCustody
  "J. Mathias Weber research group, University of Colorado Boulder"
  "JPL FY24 SURP poster SP23012p"
  "FY24 successor-PI poster again states that the work heavily leverages the Weber-group cryogenic ion apparatus."

projectContinuity2023to2024 : C.AccessContinuityReceipt
projectContinuity2023to2024 = C.access-continuity-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "FY23 PI Frank W. Maiwald; co-investigators Robert P. Hodyss and Mathias Weber"
  "FY24 PI Deacon J. Nemchick; co-investigators Robert P. Hodyss and Mathias Weber"
  true
  "JPL SURP FY23 and FY24 exact same project title; FY24 publications retain Frank Maiwald as coauthor"
  "Project/scientific-lineage and external apparatus continuity are closed; exact JPL calibration, qualification, notebook, repository, mission-integration and tacit-execution transfer are not."

record MaiwaldCarrierContinuityAssessment : Set where
  constructor maiwald-carrier-continuity-assessment
  field
    sameProjectContinuationOwned : Bool
    sameProjectContinuationOwnedIsTrue : sameProjectContinuationOwned ≡ true
    overlappingTeamOwned : Bool
    overlappingTeamOwnedIsTrue : overlappingTeamOwned ≡ true
    sameExternalApparatusOwned : Bool
    sameExternalApparatusOwnedIsTrue : sameExternalApparatusOwned ≡ true
    successorPIOwned : Bool
    successorPIOwnedIsTrue : successorPIOwned ≡ true
    exactJPLCalibrationTransferOwned : Bool
    exactJPLCalibrationTransferOwnedIsFalse : exactJPLCalibrationTransferOwned ≡ false
    exactQualificationTransferOwned : Bool
    exactQualificationTransferOwnedIsFalse : exactQualificationTransferOwned ≡ false
    platformDisappearedWithMaiwald : Bool
    platformDisappearedWithMaiwaldIsFalse : platformDisappearedWithMaiwald ≡ false
canonicalMaiwaldCarrierContinuityAssessment : MaiwaldCarrierContinuityAssessment
canonicalMaiwaldCarrierContinuityAssessment = maiwald-carrier-continuity-assessment true refl true refl true refl true refl false refl false refl false refl

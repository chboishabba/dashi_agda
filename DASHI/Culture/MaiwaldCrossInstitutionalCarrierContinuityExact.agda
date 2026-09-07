module DASHI.Culture.MaiwaldCrossInstitutionalCarrierContinuityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ApplicationCapabilityCustodyBidiExact as C

------------------------------------------------------------------------
-- MAIWALD ACTION-SPECTROSCOPY CROSS-INSTITUTIONAL CONTINUITY
--
-- Primary sources:
-- JPL FY23 SURP poster, RPC#sp23012, CL#23-5018:
-- https://www.jpl.nasa.gov/site/research/media/posters/2023/SP23012p.pdf
-- JPL FY24 SURP poster, same project title:
-- https://www.jpl.nasa.gov/site/research/media/posters/2024/SP23012p.pdf
------------------------------------------------------------------------

weberApparatusCustody2023 : C.CapabilityCustodyReceipt
weberApparatusCustody2023 = C.capability-custody-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  C.physicalApparatus
  C.crossInstitutionalCustody
  "J. Mathias Weber research group, University of Colorado Boulder"
  "JPL FY23 SURP poster RPC#sp23012 / CL#23-5018"
  "The FY23 poster explicitly describes the active cryogenic action-spectroscopy apparatus used by the collaboration as the Boulder/Weber-group apparatus; this is a physical-apparatus custody receipt, not a complete calibration/IP ownership statement."

weberApparatusCustody2024 : C.CapabilityCustodyReceipt
weberApparatusCustody2024 = C.capability-custody-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  C.physicalApparatus
  C.crossInstitutionalCustody
  "J. Mathias Weber research group, University of Colorado Boulder"
  "JPL FY24 SURP poster SP23012p"
  "The FY24 successor-PI poster again states that the work heavily leverages the Weber-group cryogenic ion apparatus and labels Figure 1 as native to the Weber group."

projectContinuity2023to2024 : C.AccessContinuityReceipt
projectContinuity2023to2024 = C.access-continuity-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "FY23 PI Frank W. Maiwald; co-investigators Robert P. Hodyss and Mathias Weber"
  "FY24 PI Deacon J. Nemchick; co-investigators Robert P. Hodyss and Mathias Weber"
  true
  "JPL SURP FY23 and FY24 exact same project title; FY24 publications retain Frank Maiwald as coauthor"
  "This closes project/scientific-lineage continuity and external apparatus continuity. It does not prove that every JPL-specific calibration, qualification, notebook, repository, mission-integration or tacit-execution carrier transferred intact."

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
canonicalMaiwaldCarrierContinuityAssessment = maiwald-carrier-continuity-assessment
  true refl true refl true refl true refl false refl false refl false refl

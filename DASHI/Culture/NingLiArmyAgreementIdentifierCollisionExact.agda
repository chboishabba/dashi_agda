module DASHI.Culture.NingLiArmyAgreementIdentifierCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DAAH01-01-9-R001 IDENTIFIER COLLISION / ADMINISTRATIVE RESIDUE
--
-- A 2006 State of Texas statewide single-audit table exposes the exact string
-- DAAH01-01-9-R001 in a row described as a pass-through from Lockheed Martin,
-- while the FY2001 DoD Other Transactions source genealogy associates that
-- identifier with the reported AC Gravity prototype agreement.  The shared
-- identifier is a high-value acquisition coordinate, not a same-object weld.
------------------------------------------------------------------------

record AgreementIdentifierAppearance : Set where
  constructor agreement-identifier-appearance
  field
    identifier : String
    sourceAuthority : String
    sourceManifestation : String
    displayedRelationship : String
    displayedAmountOrValue : String
    sourceYear : String
    exactSameObjectPaid : Bool
    interpretation : String

open AgreementIdentifierAppearance public

reportedArmyACGravityAppearance : AgreementIdentifierAppearance
reportedArmyACGravityAppearance = agreement-identifier-appearance
  "DAAH01-01-9-R001"
  "U.S. Department of Defense FY2001 Other Transactions annual-report genealogy; original archived carrier remains the preferred authority"
  "reported p.66 transcription plus archived FY01RPT.doc locator"
  "Other Transaction for Prototype; reported awardee AC Gravity LLC; title Gravito-Electro Magnetic Superconductivity Experiment"
  "$448,970 reported U.S.-Government-dollar field"
  "FY2001; scheduled 2001-04-25 to 2002-09-25 in secondary transcriptions"
  false
  "The identifier and reported row remain acquisition coordinates until the original archived government row is inspected directly in this lane."

texasAuditAgreementNumberCollision : AgreementIdentifierAppearance
texasAuditAgreementNumberCollision = agreement-identifier-appearance
  "DAAH01-01-9-R001"
  "Texas State Auditor / Statewide Single Audit Report for fiscal year ended 2006-08-31"
  "State of Texas Federal Portion of the Statewide Single Audit Report, report 07-316"
  "table extraction displays the identifier immediately under a 'Pass-Through from Lockheed Martin Corp' relationship"
  "$477 in the extracted row/table alignment"
  "FY2006 audit manifestation"
  false
  "This is an independent administrative occurrence of the exact identifier. The table context must be inspected before deciding whether it is a pass-through reference to the same Army agreement, a subcontract/accounting relationship, an OCR/table-alignment issue, a typo, or identifier reuse."

record IdentifierCollisionBoundary : Set where
  constructor identifier-collision-boundary
  field
    exactIdentifierEqualityPaysSameObject : Bool
    lockheedPassThroughInterpretationPaid : Bool
    texasAuditRowPaysACGravityOutcome : Bool
    texasAuditRowPaysArmyClassification : Bool
    collisionNominatesPrimaryInspection : Bool
    sourceManifestationAndTableContextRequired : Bool

canonicalIdentifierCollisionBoundary : IdentifierCollisionBoundary
canonicalIdentifierCollisionBoundary = identifier-collision-boundary
  false false false false true true

agreementNumberCollisionDoesNotCreateSameObject : Bool
agreementNumberCollisionDoesNotCreateSameObject = true

lockheedPassThroughInterpretationPaid : Bool
lockheedPassThroughInterpretationPaid = false

texasAuditDoesNotPayArmyOutcome : Bool
texasAuditDoesNotPayArmyOutcome = true

collisionAcquisitionTarget : String
collisionAcquisitionTarget =
  "inspect the original Texas audit table around DAAH01-01-9-R001, identify the programme/subrecipient/prime columns and row alignment, then compare the exact administrative relationship against the original FY2001 DoD row and any Army payment/closeout/accounting records"

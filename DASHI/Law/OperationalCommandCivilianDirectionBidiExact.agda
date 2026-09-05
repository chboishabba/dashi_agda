module DASHI.Law.OperationalCommandCivilianDirectionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Two-channel direction fibre: command to police != lawful direction to civilian.
------------------------------------------------------------------------

data ReceiptState : Set where
  receiptClosed receiptOpen receiptConflict : ReceiptState

record OperationalCommand : Set where
  constructor operationalCommand
  field
    commandExists : ReceiptState
    commandIssuer : ReceiptState
    commandAuthority : ReceiptState
    commandContent : ReceiptState
    commandTemporalPriority : ReceiptState
    commandTransmission : ReceiptState
    fieldReceipt : ReceiptState
    commandReference : String

open OperationalCommand public

record CivilianDirection : Set where
  constructor civilianDirection
  field
    directionIssued : ReceiptState
    directionAuthority : ReceiptState
    directionContent : ReceiptState
    directionAudibleOrPerceivable : ReceiptState
    comprehensionOpportunity : ReceiptState
    complianceOpportunity : ReceiptState
    directionReference : String

open CivilianDirection public

record ForceAfterDirectionFibre : Set where
  constructor forceAfterDirectionFibre
  field
    operationalCommandChannel : OperationalCommand
    civilianDirectionChannel : CivilianDirection
    forceOccurred : ReceiptState
    arrestOccurred : ReceiptState
    eventReference : String

open ForceAfterDirectionFibre public

------------------------------------------------------------------------
-- BIDI consumer routing.
------------------------------------------------------------------------

data DirectionClaim : Set where
  officerWasOrderedToAdvance
  civilianWasLawfullyDirectedToMove
  forceFollowedLawfulNonCompliance
  fieldOfficerKnewLimitingAuthorisation : DirectionClaim

data DirectionProducer : Set where
  commandTransmissionReceipt
  civilianDirectionReceipt
  lawfulNonComplianceReceipt
  limitingAuthorisationFieldReceipt : DirectionProducer

reverseDirection : DirectionClaim → DirectionProducer
reverseDirection officerWasOrderedToAdvance = commandTransmissionReceipt
reverseDirection civilianWasLawfullyDirectedToMove = civilianDirectionReceipt
reverseDirection forceFollowedLawfulNonCompliance = lawfulNonComplianceReceipt
reverseDirection fieldOfficerKnewLimitingAuthorisation = limitingAuthorisationFieldReceipt

record DirectionBoundary : Set where
  constructor directionBoundary
  field
    commandToOfficerImpliesDirectionToCivilian : Bool
    commandToOfficerImpliesDirectionToCivilianIsFalse : commandToOfficerImpliesDirectionToCivilian ≡ false
    authorisedAtCommandLevelImpliesFieldReceipt : Bool
    authorisedAtCommandLevelImpliesFieldReceiptIsFalse : authorisedAtCommandLevelImpliesFieldReceipt ≡ false
    forceAfterCommandImpliesLawfulCivilianNonCompliance : Bool
    forceAfterCommandImpliesLawfulCivilianNonComplianceIsFalse : forceAfterCommandImpliesLawfulCivilianNonCompliance ≡ false

canonicalDirectionBoundary : DirectionBoundary
canonicalDirectionBoundary = directionBoundary false refl false refl false refl

------------------------------------------------------------------------
-- Synthetic Herzog-shaped fixtures.  These are theorem/regression carriers,
-- not assertions that any pleaded or reported fact has been judicially found.
------------------------------------------------------------------------

advanceCommandCivilianDirectionOpen : ForceAfterDirectionFibre
advanceCommandCivilianDirectionOpen = forceAfterDirectionFibre
  (operationalCommand
    receiptClosed receiptOpen receiptOpen receiptOpen
    receiptClosed receiptClosed receiptOpen
    "synthetic: field movement suggests an upstream command may exist; issuer/content/authority unresolved")
  (civilianDirection
    receiptOpen receiptOpen receiptOpen receiptOpen receiptOpen receiptOpen
    "synthetic: no civilian-direction receipt supplied")
  receiptClosed receiptOpen
  "synthetic command-vs-civilian-direction separation fixture"

limitingAuthorisationNotTransmitted : ForceAfterDirectionFibre
limitingAuthorisationNotTransmitted = forceAfterDirectionFibre
  (operationalCommand
    receiptClosed receiptClosed receiptClosed receiptClosed
    receiptClosed receiptOpen receiptOpen
    "synthetic: limiting authorisation exists at command level but transmission/field receipt remain open")
  (civilianDirection
    receiptOpen receiptOpen receiptOpen receiptOpen receiptOpen receiptOpen
    "synthetic: field-facing direction unresolved")
  receiptClosed receiptClosed
  "synthetic communication-failure fixture"

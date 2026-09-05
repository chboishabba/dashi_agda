module DASHI.Law.OperationalDirectionProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Operational-direction provenance.  A direction is not a single opaque fact:
-- issuer, legal authority, content, temporal priority, transmission, receipt,
-- field acknowledgement and supersession are separate proof coordinates.
------------------------------------------------------------------------

data DirectionState : Set where
  directionPresent directionAbsent directionUnresolved : DirectionState

data TransmissionState : Set where
  transmitted notTransmitted transmissionUnresolved : TransmissionState

data ReceiptState : Set where
  received notReceived receiptUnresolved : ReceiptState

data AuthorityStatus : Set where
  authorityClosed authorityOpen authorityUnresolved : AuthorityStatus

record OperationalDirectionFibre : Set where
  constructor operationalDirectionFibre
  field
    directionExistence : DirectionState
    issuerReference : String
    authorityStatus : AuthorityStatus
    authorityReference : String
    directionContentReference : String
    temporalPriorityClosed : Bool
    transmissionToField : TransmissionState
    fieldReceipt : ReceiptState
    fieldAcknowledgementClosed : Bool
    supersessionChecked : Bool
    sourceReference : String

open OperationalDirectionFibre public

------------------------------------------------------------------------
-- Key separation: command-level authorisation/content does not imply that the
-- relevant field officers received it.
------------------------------------------------------------------------

record CommandFieldCommunicationBoundary : Set where
  constructor commandFieldCommunicationBoundary
  field
    commandAuthorisationImpliesFieldReceipt : Bool
    commandAuthorisationImpliesFieldReceiptIsFalse :
      commandAuthorisationImpliesFieldReceipt ≡ false
    directionExistenceImpliesLawfulExecution : Bool
    directionExistenceImpliesLawfulExecutionIsFalse :
      directionExistenceImpliesLawfulExecution ≡ false
    laterDiscoveryOfDirectionRetroactivelySuppliesFieldReceipt : Bool
    laterDiscoveryOfDirectionRetroactivelySuppliesFieldReceiptIsFalse :
      laterDiscoveryOfDirectionRetroactivelySuppliesFieldReceipt ≡ false

canonicalCommandFieldBoundary : CommandFieldCommunicationBoundary
canonicalCommandFieldBoundary = commandFieldCommunicationBoundary
  false refl false refl false refl

------------------------------------------------------------------------
-- BIDI claims and minimal producer obligations.
------------------------------------------------------------------------

data DirectionClaim : Set where
  directionExisted
  directionWasLawfullyAuthorised
  directionGovernedFieldAction
  fieldOfficerReceivedDirection
  fieldActionLawfullyFollowedDirection : DirectionClaim

data DirectionProducer : Set where
  directionDocumentReceipt
  legalAuthorityReceipt
  transmissionReceipt
  fieldReceiptProducer
  lawfulExecutionReceipt : DirectionProducer

reverseDirection : DirectionClaim → DirectionProducer
reverseDirection directionExisted = directionDocumentReceipt
reverseDirection directionWasLawfullyAuthorised = legalAuthorityReceipt
reverseDirection directionGovernedFieldAction = transmissionReceipt
reverseDirection fieldOfficerReceivedDirection = fieldReceiptProducer
reverseDirection fieldActionLawfullyFollowedDirection = lawfulExecutionReceipt

record DirectionCutset : Set where
  constructor directionCutset
  field
    documentClosed : Bool
    authorityClosedCutset : Bool
    chronologyClosed : Bool
    transmissionClosed : Bool
    fieldReceiptClosed : Bool
    executionClosed : Bool
    cutsetReference : String

open DirectionCutset public

data DirectionResidual : Set where
  documentResidual authorityResidual chronologyResidual transmissionResidual fieldReceiptResidual executionResidual directionClosed : DirectionResidual

firstDirectionResidual : DirectionClaim → DirectionCutset → DirectionResidual
firstDirectionResidual directionExisted c with documentClosed c
... | false = documentResidual
... | true = directionClosed
firstDirectionResidual directionWasLawfullyAuthorised c with documentClosed c
... | false = documentResidual
... | true with authorityClosedCutset c
...   | false = authorityResidual
...   | true = directionClosed
firstDirectionResidual directionGovernedFieldAction c with documentClosed c
... | false = documentResidual
... | true with chronologyClosed c
...   | false = chronologyResidual
...   | true with transmissionClosed c
...     | false = transmissionResidual
...     | true = directionClosed
firstDirectionResidual fieldOfficerReceivedDirection c with transmissionClosed c
... | false = transmissionResidual
... | true with fieldReceiptClosed c
...   | false = fieldReceiptResidual
...   | true = directionClosed
firstDirectionResidual fieldActionLawfullyFollowedDirection c with documentClosed c
... | false = documentResidual
... | true with authorityClosedCutset c
...   | false = authorityResidual
...   | true with chronologyClosed c
...     | false = chronologyResidual
...     | true with transmissionClosed c
...       | false = transmissionResidual
...       | true with fieldReceiptClosed c
...         | false = fieldReceiptResidual
...         | true with executionClosed c
...           | false = executionResidual
...           | true = directionClosed

canonicalCommandKnownFieldReceiptOpen : DirectionCutset
canonicalCommandKnownFieldReceiptOpen = directionCutset
  true true true true false false
  "synthetic command direction known and transmitted; field receipt/execution unresolved"

fieldReceiptCannotBeSkipped :
  firstDirectionResidual fieldActionLawfullyFollowedDirection canonicalCommandKnownFieldReceiptOpen
  ≡ fieldReceiptResidual
fieldReceiptCannotBeSkipped = refl

------------------------------------------------------------------------
-- Public-source bounded fixtures for the Herzog protest litigation lane.
-- These encode what the cited public reporting establishes, not ultimate truth.
------------------------------------------------------------------------

record PublicDirectionLitigationReceipt : Set where
  constructor publicDirectionLitigationReceipt
  field
    propositionReference : String
    sourceType : String
    sourceReferencePublic : String
    worldTruthPromoted : Bool
    worldTruthPromotedIsFalse : worldTruthPromoted ≡ false

open PublicDirectionLitigationReceipt public

jonesRicketsonDirectionReviewReceipt : PublicDirectionLitigationReceipt
jonesRicketsonDirectionReviewReceipt = publicDirectionLitigationReceipt
  "Public reporting states Derek Jones and James Ricketson are seeking Supreme Court review of directions/orders governing police conduct at the 9 February 2026 Herzog protest"
  "contemporary public reporting / solicitor public statement"
  "XD Law public statement; Guardian reporting; September 2026 public posts reporting Supreme Court hearing"
  false refl

shadidPrayerTransmissionReceipt : PublicDirectionLitigationReceipt
shadidPrayerTransmissionReceipt = publicDirectionLitigationReceipt
  "Public reporting of Eyad Shadid's statement of claim says NSW Police later acknowledged the prayer was authorised but that message was not passed to officers"
  "reported statement of claim plus NSW Police public statement"
  "Guardian Australia 3 September 2026 and contemporaneous reporting"
  false refl

------------------------------------------------------------------------
-- The communication-gap theorem shape is deliberately generic.
------------------------------------------------------------------------

record AuthorisedButNotReceived : Set where
  constructor authorisedButNotReceived
  field
    commandAuthorisationKnown : Bool
    commandAuthorisationKnownIsTrue : commandAuthorisationKnown ≡ true
    fieldReceiptKnown : Bool
    fieldReceiptKnownIsFalse : fieldReceiptKnown ≡ false
    gapReference : String

canonicalAuthorisedButNotReceived : AuthorisedButNotReceived
canonicalAuthorisedButNotReceived = authorisedButNotReceived
  true refl false refl
  "synthetic analogue of command authorisation existing while field receipt is absent"

commandAuthorisationDoesNotCloseFieldReceipt :
  fieldReceiptKnown canonicalAuthorisedButNotReceived ≡ false
commandAuthorisationDoesNotCloseFieldReceipt = refl

module DASHI.Culture.MissingDeceasedTwentyScientistRound84NingExactIdentifierCollisionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- ROUND 84 / NING LI EXACT-IDENTIFIER COLLISION
--
-- Acquisition surfaced the literal string `DAAH01-01-9-R001` on two public
-- record surfaces with incompatible surrounding semantics:
--
--  * FY2001 DoD Other Transactions reporting: Army AMCOM prototype award to
--    AC Gravity LLC for the Gravito-Electro Magnetic Superconductivity
--    Experiment; and
--  * FY2006 State of Texas federal single-audit schedule: a Lockheed Martin
--    pass-through line under Military Medical Research and Development with a
--    $477 expenditure.
--
-- Literal identifier equality is retained, but it does not collapse these
-- records into one object.  Same-object promotion requires issuer/recipient,
-- programme, time, role and provenance semantics to weld independently.
------------------------------------------------------------------------

data IdentifierSurface : Set where
  dodFY2001OtherTransactionSurface : IdentifierSurface
  texasFY2006SingleAuditSurface : IdentifierSurface

record IdentifierOccurrence : Set where
  constructor identifierOccurrence
  field
    literalIdentifier : String
    surface : IdentifierSurface
    issuerOrPassThroughRef : String
    recipientOrCounterpartyRef : String
    programmeRef : String
    timeRef : String
    amountOrAccountingRef : String
    sourceRef : String

armyPrototypeOccurrence : IdentifierOccurrence
armyPrototypeOccurrence = identifierOccurrence
  "DAAH01-01-9-R001"
  dodFY2001OtherTransactionSurface
  "US Army Aviation and Missile Command / AMSAM-AC-RD-BA"
  "AC Gravity LLC"
  "Gravito-Electro Magnetic Superconductivity Experiment / Other Transaction for Prototype"
  "effective 2001-04-25; scheduled completion 2002-09-25"
  "FY2001 report states US Government Dollars 448970"
  "DoD FY2001 Annual Report on Cooperative Agreements and Other Transactions"

texasAuditOccurrence : IdentifierOccurrence
texasAuditOccurrence = identifierOccurrence
  "DAAH01-01-9-R001"
  texasFY2006SingleAuditSurface
  "Pass-Through from Lockheed Martin Corp"
  "State of Texas single-audit recipient surface"
  "Military Medical Research and Development / CFDA 12.420 accounting schedule"
  "fiscal year ended 2006-08-31"
  "reported expenditure 477"
  "State of Texas Federal Portion of the Statewide Single Audit Report FY2006"

literalIdentifierMatches : Bool
literalIdentifierMatches = true

sameIdentifierStringDoesNotPaySameObject : Bool
sameIdentifierStringDoesNotPaySameObject = true

semanticMismatchRequiresIdentityBridge : Bool
semanticMismatchRequiresIdentityBridge = true

texasAuditSurfaceDoesNotPayACGravityOutcome : Bool
texasAuditSurfaceDoesNotPayACGravityOutcome = true

texasAuditSurfaceDoesNotPayLockheedParticipationInACGravityPrototype : Bool
texasAuditSurfaceDoesNotPayLockheedParticipationInACGravityPrototype = true

texas477DoesNotModifyArmy448970AwardField : Bool
texas477DoesNotModifyArmy448970AwardField = true

laterAccountingOccurrenceDoesNotPayPrototypeCloseout : Bool
laterAccountingOccurrenceDoesNotPayPrototypeCloseout = true

identifierCollisionMaySignalReuseMiscodingOrDistinctAccountingObject : Bool
identifierCollisionMaySignalReuseMiscodingOrDistinctAccountingObject = true

collisionDoesNotSelectWhichExplanationIsTrue : Bool
collisionDoesNotSelectWhichExplanationIsTrue = true

primaryArmyBytesCustodyStillUnpaid : Bool
primaryArmyBytesCustodyStillUnpaid = true

armyOutcomeStillUnresolved : Bool
armyOutcomeStillUnresolved = true

universalNonParticipationStillUnproved : Bool
universalNonParticipationStillUnproved = true

h2Paid : Bool
h2Paid = false

h3Paid : Bool
h3Paid = false

record NingExactIdentifierCollisionBoundary : Set where
  constructor ningExactIdentifierCollisionBoundary
  field
    literalMatchIsReal : Bool
    literalMatchIsRealIsTrue : literalMatchIsReal ≡ true
    sameObjectNotPromoted : Bool
    sameObjectNotPromotedIsTrue : sameObjectNotPromoted ≡ true
    outcomeNotPromoted : Bool
    outcomeNotPromotedIsTrue : outcomeNotPromoted ≡ true
    h2StillUnpaid : Bool
    h2StillUnpaidIsFalse : h2StillUnpaid ≡ false
    h3StillUnpaid : Bool
    h3StillUnpaidIsFalse : h3StillUnpaid ≡ false

canonicalNingExactIdentifierCollisionBoundary : NingExactIdentifierCollisionBoundary
canonicalNingExactIdentifierCollisionBoundary =
  ningExactIdentifierCollisionBoundary true refl true refl true refl false refl false refl

module DASHI.Law.HerzogBodycamQuotedUtteranceProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.QuotedUtteranceContextProvenanceExact as Quote
import DASHI.Law.HerzogConcreteIncidentHypervoxelExact as Incident

------------------------------------------------------------------------
-- Exact body-worn-camera utterance provenance.
--
-- Source role is preserved carefully:
--   police-owned body-worn recording -> leaked/published footage -> media
--   transcription/reporting.
-- The recorded words are stronger evidence than a third-party recollection,
-- but they do not by themselves adjudicate lawfulness, motive, command cause,
-- or institutional policy.
------------------------------------------------------------------------

pumpedQuote : Quote.QuoteReceipt
pumpedQuote = Quote.quoteReceipt
  "NSW Police officer; identity not promoted by this owner"
  "I fucking pumped that cunt"
  "2026-02-09"
  "body-worn camera footage associated with the anti-Herzog Town Hall police operation"
  "Guardian video/article, 1 September 2026, publishing leaked NSW Police body-worn-camera footage"

punchedWhileDownQuote : Quote.QuoteReceipt
punchedWhileDownQuote = Quote.quoteReceipt
  "NSW Police officer; identity not promoted by this owner"
  "Then I punched him in the head when he was down"
  "2026-02-09"
  "same body-worn-camera sequence"
  "Guardian video/article, 1 September 2026, publishing leaked NSW Police body-worn-camera footage"

colleagueReactionQuote : Quote.QuoteReceipt
colleagueReactionQuote = Quote.quoteReceipt
  "second NSW Police officer; identity not promoted by this owner"
  "So funny"
  "2026-02-09"
  "same body-worn-camera sequence following first officer's account"
  "Guardian video/article, 1 September 2026, publishing leaked NSW Police body-worn-camera footage"

------------------------------------------------------------------------
-- Evidence coordinates.
------------------------------------------------------------------------

data BodycamCoordinate : Set where
  literalPumpedUtterance : BodycamCoordinate
  firstPersonPunchingClaim : BodycamCoordinate
  personDownClaim : BodycamCoordinate
  colleagueReaction : BodycamCoordinate
  forceOccurrence : BodycamCoordinate
  forceLawfulness : BodycamCoordinate
  officerMotive : BodycamCoordinate
  commandCausation : BodycamCoordinate
  unitCulture : BodycamCoordinate
  institutionalPolicy : BodycamCoordinate

data BodycamClosure : Set where
  recordingBacked : BodycamClosure
  mediaTranscriptionBacked : BodycamClosure
  incidentCorroborated : BodycamClosure
  independentlyInvestigated : BodycamClosure
  adjudicated : BodycamClosure
  openCoordinate : BodycamClosure

coordinateClosure : BodycamCoordinate → BodycamClosure
coordinateClosure literalPumpedUtterance = mediaTranscriptionBacked
coordinateClosure firstPersonPunchingClaim = mediaTranscriptionBacked
coordinateClosure personDownClaim = mediaTranscriptionBacked
coordinateClosure colleagueReaction = mediaTranscriptionBacked
coordinateClosure forceOccurrence = incidentCorroborated
coordinateClosure forceLawfulness = openCoordinate
coordinateClosure officerMotive = openCoordinate
coordinateClosure commandCausation = openCoordinate
coordinateClosure unitCulture = openCoordinate
coordinateClosure institutionalPolicy = openCoordinate

pumpedLiteralClosed : coordinateClosure literalPumpedUtterance ≡ mediaTranscriptionBacked
pumpedLiteralClosed = refl

lawfulnessStillOpen : coordinateClosure forceLawfulness ≡ openCoordinate
lawfulnessStillOpen = refl

commandStillOpen : coordinateClosure commandCausation ≡ openCoordinate
commandStillOpen = refl

------------------------------------------------------------------------
-- Relation to incident owner.
------------------------------------------------------------------------

bodycamIncident : Incident.HerzogIncidentHypervoxel
bodycamIncident = Incident.bodycamIncident

bodycamIncidentIsSourceBacked :
  Incident.occurrenceClosure bodycamIncident ≡ Incident.sourceBacked
bodycamIncidentIsSourceBacked = refl

------------------------------------------------------------------------
-- BIDI claim routing.
------------------------------------------------------------------------

data BodycamClaim : Set where
  officerUtteredPumpedPhrase : BodycamClaim
  officerSaidHePunchedDownedPerson : BodycamClaim
  forceWasUnlawful : BodycamClaim
  boastShowsOfficerMotive : BodycamClaim
  colleagueReactionShowsUnitCulture : BodycamClaim
  commandProducedForce : BodycamClaim
  institutionEndorsedConduct : BodycamClaim

data BodycamProducer : Set where
  bodycamVideoAndTranscriptProducer : BodycamProducer
  bodycamFirstPersonConductProducer : BodycamProducer
  forceLawfulnessProducer : BodycamProducer
  motiveProducer : BodycamProducer
  crossOfficerCultureCorpusProducer : BodycamProducer
  commandProvenanceProducer : BodycamProducer
  institutionalPolicyProducer : BodycamProducer

reverseBodycam : BodycamClaim → BodycamProducer
reverseBodycam officerUtteredPumpedPhrase = bodycamVideoAndTranscriptProducer
reverseBodycam officerSaidHePunchedDownedPerson = bodycamFirstPersonConductProducer
reverseBodycam forceWasUnlawful = forceLawfulnessProducer
reverseBodycam boastShowsOfficerMotive = motiveProducer
reverseBodycam colleagueReactionShowsUnitCulture = crossOfficerCultureCorpusProducer
reverseBodycam commandProducedForce = commandProvenanceProducer
reverseBodycam institutionEndorsedConduct = institutionalPolicyProducer

------------------------------------------------------------------------
-- Source-attribution and promotion firewalls.
------------------------------------------------------------------------

record BodycamAttributionBoundary : Set where
  constructor bodycamAttributionBoundary
  field
    mediaTranscriptEqualsCourtFinding : Bool
    mediaTranscriptEqualsCourtFindingIsFalse : mediaTranscriptEqualsCourtFinding ≡ false
    firstPersonConductClaimAutomaticallyProvesUnlawfulness : Bool
    firstPersonConductClaimAutomaticallyProvesUnlawfulnessIsFalse : firstPersonConductClaimAutomaticallyProvesUnlawfulness ≡ false
    colleagueReactionAutomaticallyProvesInstitutionalPolicy : Bool
    colleagueReactionAutomaticallyProvesInstitutionalPolicyIsFalse : colleagueReactionAutomaticallyProvesInstitutionalPolicy ≡ false
    recordedBoastAutomaticallyProvesCommandCausation : Bool
    recordedBoastAutomaticallyProvesCommandCausationIsFalse : recordedBoastAutomaticallyProvesCommandCausation ≡ false
    oneOfficerAutomaticallyRepresentsAllNSWPolice : Bool
    oneOfficerAutomaticallyRepresentsAllNSWPoliceIsFalse : oneOfficerAutomaticallyRepresentsAllNSWPolice ≡ false
    paraphraseMayEraseLiteralUtterance : Bool
    paraphraseMayEraseLiteralUtteranceIsFalse : paraphraseMayEraseLiteralUtterance ≡ false

canonicalBodycamAttributionBoundary : BodycamAttributionBoundary
canonicalBodycamAttributionBoundary =
  bodycamAttributionBoundary false refl false refl false refl false refl false refl false refl

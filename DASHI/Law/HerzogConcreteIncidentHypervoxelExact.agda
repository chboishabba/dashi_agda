module DASHI.Law.HerzogConcreteIncidentHypervoxelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Concrete incident layer for the 9 February 2026 anti-Herzog police operation.
-- Each event preserves source role and closure separately; no aggregate label
-- substitutes for the lawfulness/provenance audit of the individual incident.
------------------------------------------------------------------------

data IncidentKind : Set where
  authorisedPrayerInterruption
  whiteShirtPunching
  ricketsonArrest
  teenagerDetention
  grandmotherBackInjury
  disabledPersonForce
  firstNationsOrganiserArrest
  blockedExitOrCrowdCrushRisk
  ocSprayWithoutPriorDirection
  searchWithoutApparentBasis
  legalObserverForce
  bodycamBoastAfterPunching
  policeAssaultedOfficerCounterclaim : IncidentKind

data IncidentSourceRole : Set where
  policeAdmission
  abcVerifiedVideo
  abcWitnessReport
  legalObserversFinding
  civilPleading
  bodyWornVideo
  policePublicAccount
  leccInvestigationScope
  finalAdjudicatedFinding : IncidentSourceRole

data ClosureState : Set where
  sourceBacked
  reportedOrAlleged
  independentlyInvestigated
  adjudicated
  unresolved : ClosureState

record HerzogIncidentHypervoxel : Set where
  constructor herzogIncidentHypervoxel
  field
    incident : IncidentKind
    occurrenceClosure : ClosureState
    sourceRole : IncidentSourceRole
    civilianDirectionKnown : Bool
    policePermissionOrPriorAuthorisationKnown : Bool
    forceObservedOrReported : Bool
    arrestOrDetentionObservedOrReported : Bool
    injuryObservedOrReported : Bool
    legalAuthorityClosed : Bool
    necessityProportionalityClosed : Bool
    policeCounterNarrativeExists : Bool
    independentReviewOpen : Bool
    sourceReference : String
    boundedDescription : String

open HerzogIncidentHypervoxel public

prayerIncident : HerzogIncidentHypervoxel
prayerIncident = herzogIncidentHypervoxel
  authorisedPrayerInterruption sourceBacked policeAdmission
  false true true false false false false false true
  "ABC News 12 February 2026; NSW Police confirmed Muslim men had permission to pray before officers interrupted/removed them"
  "Command-level permission existed; field interruption occurred. Transmission, field knowledge and legal basis for intervention remain separate questions."

whiteShirtIncident : HerzogIncidentHypervoxel
whiteShirtIncident = herzogIncidentHypervoxel
  whiteShirtPunching sourceBacked abcVerifiedVideo
  false false true false false false false true true
  "ABC NEWS Verify 11 February 2026; fuller video of confrontation and multiple police punches"
  "Video establishes substantial parts of physical sequence; lawfulness, necessity and proportionality are not adjudicated by the footage alone."

ricketsonIncident : HerzogIncidentHypervoxel
ricketsonIncident = herzogIncidentHypervoxel
  ricketsonArrest sourceBacked abcVerifiedVideo
  false false true true true false false true true
  "ABC NEWS Verify 12 February 2026; footage of 76-year-old James Ricketson's arrest; released without charge after bodycam review"
  "Occurrence/arrest/injury surface is source-backed; arrest authority and force lawfulness remain separately auditable."

teenagerIncident : HerzogIncidentHypervoxel
teenagerIncident = herzogIncidentHypervoxel
  teenagerDetention reportedOrAlleged abcWitnessReport
  false false true true true false false false true
  "ABC News 11 February 2026; 16-year-old Nedal and mother allege pushing, kicking and dragging; ABC video shows apprehension but not full precursor"
  "Partial video plus witness allegation; do not promote unseen precursor or assault allegation to adjudicated fact."

grandmotherIncident : HerzogIncidentHypervoxel
grandmotherIncident = herzogIncidentHypervoxel
  grandmotherBackInjury reportedOrAlleged abcWitnessReport
  false false true false true false false false true
  "ABC News 10 February 2026; Jann Alhafny reported broken back after being pushed by riot squad officer"
  "Serious-injury allegation/witness report; causal and legal conclusions remain open absent adjudication/medical-provenance closure."

disabledPersonIncident : HerzogIncidentHypervoxel
disabledPersonIncident = herzogIncidentHypervoxel
  disabledPersonForce independentlyInvestigated legalObserversFinding
  false false true false true false false false true
  "Legal Observers NSW Final Report 3 July 2026; report describes force against visibly vulnerable people including person with MS"
  "Legal Observers finding based on corpus; independent statutory misconduct finding remains open."

firstNationsOrganiserIncident : HerzogIncidentHypervoxel
firstNationsOrganiserIncident = herzogIncidentHypervoxel
  firstNationsOrganiserArrest independentlyInvestigated legalObserversFinding
  true false true true false false false false true
  "Legal Observers NSW Final Report 3 July 2026"
  "Report says first arrests included Blak Caucus First Nations organisers acting as intermediaries and complying with directions, reducing communication capacity."

blockedExitIncident : HerzogIncidentHypervoxel
blockedExitIncident = herzogIncidentHypervoxel
  blockedExitOrCrowdCrushRisk independentlyInvestigated legalObserversFinding
  false false true false false false false false true
  "Legal Observers NSW Final Report 3 July 2026"
  "Report records denied exit access and crowd-crush-risk conditions; event geometry and command responsibility require incident-specific reconstruction."

ocSprayNoDirectionIncident : HerzogIncidentHypervoxel
ocSprayNoDirectionIncident = herzogIncidentHypervoxel
  ocSprayWithoutPriorDirection independentlyInvestigated legalObserversFinding
  false false true false true false false true true
  "Legal Observers NSW Final Report 3 July 2026; ABC reporting independently confirms pepper spray was deployed"
  "Report identifies OC-spray incidents without prior directions; exact officer-level authority/necessity remains open."

searchNoBasisIncident : HerzogIncidentHypervoxel
searchNoBasisIncident = herzogIncidentHypervoxel
  searchWithoutApparentBasis independentlyInvestigated legalObserversFinding
  false false false true false false false false true
  "Legal Observers NSW Final Report 3 July 2026"
  "Report alleges searches without apparent lawful basis; 'apparent' is preserved and does not become a judicial invalidity finding."

bodycamIncident : HerzogIncidentHypervoxel
bodycamIncident = herzogIncidentHypervoxel
  bodycamBoastAfterPunching sourceBacked bodyWornVideo
  false false true false false false false false true
  "ABC News 1 September 2026; leaked body-worn footage apparently records officer saying he punched a protester in the head while the person was down"
  "The officer statement is observable evidence of an utterance/conduct account; legal characterisation remains for LECC/court processes."

policeCounterclaimIncident : HerzogIncidentHypervoxel
policeCounterclaimIncident = herzogIncidentHypervoxel
  policeAssaultedOfficerCounterclaim sourceBacked policePublicAccount
  false false false false true false false true true
  "NSW Police/ABC 9-10 February 2026; police said officers were threatened, jostled and assaulted, including an officer allegedly bitten"
  "Police counter-narrative is retained as its own source proposition and does not erase incident-level civilian-force allegations."

------------------------------------------------------------------------
-- Event-level non-collapse boundaries.
------------------------------------------------------------------------

record HerzogIncidentBoundary : Set where
  constructor herzogIncidentBoundary
  field
    aggregateCoerciveRoutingProvesEveryIncidentUnlawful : Bool
    aggregateCoerciveRoutingProvesEveryIncidentUnlawfulIsFalse : aggregateCoerciveRoutingProvesEveryIncidentUnlawful ≡ false
    policeCrowdAggressionAccountDefeatsEveryForceComplaint : Bool
    policeCrowdAggressionAccountDefeatsEveryForceComplaintIsFalse : policeCrowdAggressionAccountDefeatsEveryForceComplaint ≡ false
    videoOccurrenceAutomaticallyProvesLegalExcess : Bool
    videoOccurrenceAutomaticallyProvesLegalExcessIsFalse : videoOccurrenceAutomaticallyProvesLegalExcess ≡ false
    authorisedPrayerImpliesFieldOfficersReceivedAuthorisation : Bool
    authorisedPrayerImpliesFieldOfficersReceivedAuthorisationIsFalse : authorisedPrayerImpliesFieldOfficersReceivedAuthorisation ≡ false
    leccInvestigationEqualsMisconductFinding : Bool
    leccInvestigationEqualsMisconductFindingIsFalse : leccInvestigationEqualsMisconductFinding ≡ false

canonicalHerzogIncidentBoundary : HerzogIncidentBoundary
canonicalHerzogIncidentBoundary =
  herzogIncidentBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI: aggregate routing claims reverse to incident-specific producers.
------------------------------------------------------------------------

data IncidentAuditClaim : Set where
  prayerInterventionLawful
  whiteShirtForceLawful
  ricketsonArrestLawful
  teenagerForceLawful
  elderlyInjuryForceLawful
  blockedExitOperationallyJustified
  ocSprayIncidentLawful
  searchIncidentLawful
  operationWideSystemicPattern : IncidentAuditClaim

data IncidentAuditProducer : Set where
  prayerCommandTransmissionAndAuthorityProducer
  whiteShirtFullSequenceAndForceAuthorityProducer
  ricketsonArrestGroundsAndForceProducer
  teenagerCompletePrecursorProducer
  elderlyIncidentMedicalAndForceProducer
  exitGeometryAndCommandProducer
  ocSprayDirectionAndForceAuthorityProducer
  searchGroundsProducer
  crossIncidentPatternProducer : IncidentAuditProducer

reverseIncidentAudit : IncidentAuditClaim → IncidentAuditProducer
reverseIncidentAudit prayerInterventionLawful = prayerCommandTransmissionAndAuthorityProducer
reverseIncidentAudit whiteShirtForceLawful = whiteShirtFullSequenceAndForceAuthorityProducer
reverseIncidentAudit ricketsonArrestLawful = ricketsonArrestGroundsAndForceProducer
reverseIncidentAudit teenagerForceLawful = teenagerCompletePrecursorProducer
reverseIncidentAudit elderlyInjuryForceLawful = elderlyIncidentMedicalAndForceProducer
reverseIncidentAudit blockedExitOperationallyJustified = exitGeometryAndCommandProducer
reverseIncidentAudit ocSprayIncidentLawful = ocSprayDirectionAndForceAuthorityProducer
reverseIncidentAudit searchIncidentLawful = searchGroundsProducer
reverseIncidentAudit operationWideSystemicPattern = crossIncidentPatternProducer

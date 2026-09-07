module DASHI.Law.HerzogRallyPoliceConductSourceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Broad source audit for NSW Police conduct at the Sydney Town Hall protest,
-- 9 February 2026.  Allegations, observed footage, police responses, civil
-- pleadings and independent oversight scope remain separately typed.
------------------------------------------------------------------------

data AuditSourceRole : Set where
  legalObserverReport : AuditSourceRole
  abcVideoVerification : AuditSourceRole
  abcReportedWitnessAccount : AuditSourceRole
  policeOfficialAccount : AuditSourceRole
  independentOversightInvestigation : AuditSourceRole
  civilPleadingReported : AuditSourceRole
  leakedBodyWornVideoReport : AuditSourceRole
  secondaryInvestigativeReport : AuditSourceRole
  dashiAnalyticBridge : AuditSourceRole

data ConductProposition : Set where
  policeEncircledAndRestrictedExits : ConductProposition
  mountedPoliceCreatedCrowdCrushRisk : ConductProposition
  protestersPushedTowardLightRail : ConductProposition
  policePursuedProtestersIntoCity : ConductProposition
  forceAgainstRestrainedOrComplyingPeople : ConductProposition
  forceAgainstDisabledOrElderlyPeople : ConductProposition
  pepperSprayUsedOnCrowd : ConductProposition
  gogglesRemovedBeforePepperSprayAllegation : ConductProposition
  inadequateMedicalAssistanceAllegation : ConductProposition
  legalObserversPunchedOrPepperSprayedAllegation : ConductProposition
  firstNationsIntermediariesArrested : ConductProposition
  noClearDirectionBeforeForceOrArrestAllegation : ConductProposition
  requestsToLeaveRefusedOrIgnoredAllegation : ConductProposition
  searchesWithoutApparentLawfulBasisAllegation : ConductProposition
  teenagerDraggedKickedOrPushedAllegation : ConductProposition
  prayerGroupHadPriorPolicePermission : ConductProposition
  prayerPermissionNotCommunicatedToField : ConductProposition
  shadidAssaultFalseImprisonmentMisfeasanceClaims : ConductProposition
  policeSaidCrowdThreatenedJostledAssaultedOfficers : ConductProposition
  policeSaidCrowdAggressiveVolatile : ConductProposition
  officerBoastedAboutPunchingDownedProtester : ConductProposition
  postEventHomeRaidsAndLaterArrestsChillingEffectAllegation : ConductProposition
  leccInvestigatingLawfulnessAndAppropriateness : ConductProposition
  leccLargestComplaintVolume : ConductProposition
  policeConductUltimatelyUnlawfulOrSystemic : ConductProposition

record ConductSourceReceipt : Set where
  constructor conductSourceReceipt
  field
    proposition : ConductProposition
    role : AuditSourceRole
    authorOrInstitution : String
    title : String
    stableIdentifier : String
    boundedDescription : String
    adjudicatedOrFinalFinding : Bool

open ConductSourceReceipt public

legalObserversFinalReport : ConductSourceReceipt
legalObserversFinalReport = conductSourceReceipt
  noClearDirectionBeforeForceOrArrestAllegation legalObserverReport
  "Legal Observers NSW"
  "Final Report: Police Operation at the Town Hall Protest 9 February 2026"
  "https://legalobserversnsw.org/2026/07/03/final-report-police-operation-at-the-town-hall-protest-9-february-2026/"
  "Based on more than 150 items of footage, witness statements and observer material; reports repeated force without clear directions, constrained exits, crowd-crush risk, searches/arrests and medical-assistance concerns"
  false

legalObserversInitialCrowdControlReceipt : ConductSourceReceipt
legalObserversInitialCrowdControlReceipt = conductSourceReceipt
  mountedPoliceCreatedCrowdCrushRisk legalObserverReport
  "Legal Observers NSW"
  "Initial Report: Policing of the PAG Town Hall rally 9 February 2026"
  "https://legalobserversnsw.org/2026/02/09/initial-report-policing-of-the-pag-town-hall-rally-9-february-2026/"
  "Observer report alleged encirclement, blocked entrances/exits, crowd crush involving mounted police, protesters pushed toward light rail, pepper spray, punches/kicks and obstruction of legal observers"
  false

abcWhiteShirtVideoReceipt : ConductSourceReceipt
abcWhiteShirtVideoReceipt = conductSourceReceipt
  forceAgainstRestrainedOrComplyingPeople abcVideoVerification
  "Lucy Carter, ABC NEWS Verify"
  "New video sheds light on beginning of altercation between police officers and Town Hall protester"
  "ABC News, 11 February 2026"
  "ABC reviewed a longer video showing the lead-up to officers repeatedly punching the white-shirt protester; context was fuller than the initial viral clip but did not itself adjudicate lawfulness"
  false

abcPepperSprayReceipt : ConductSourceReceipt
abcPepperSprayReceipt = conductSourceReceipt
  pepperSprayUsedOnCrowd abcVideoVerification
  "ABC News"
  "Police and protesters clash in Sydney rally against Israeli President Isaac Herzog's visit to Australia"
  "ABC News, 9 February 2026"
  "ABC footage/reporting confirms NSW Police used pepper spray during crowd dispersal"
  false

abcPrayerPermissionReceipt : ConductSourceReceipt
abcPrayerPermissionReceipt = conductSourceReceipt
  prayerGroupHadPriorPolicePermission policeOfficialAccount
  "ABC News reporting NSW Police confirmation"
  "Muslim men had permission to pray before officers removed them from Sydney protest, police say"
  "ABC News, 12 February 2026"
  "NSW Police confirmed the Muslim prayer group had permission to pray before officers later disrupted/removed them"
  false

abcBodyWornReceipt : ConductSourceReceipt
abcBodyWornReceipt = conductSourceReceipt
  officerBoastedAboutPunchingDownedProtester leakedBodyWornVideoReport
  "Amy Greenbank, ABC News"
  "New body-cam footage from Sydney Town Hall protest fuels scrutiny of police actions"
  "ABC News, 1 September 2026"
  "Body-worn camera footage shows an officer saying he punched a protester in the head while the protester was down, with another officer responding and laughing; LECC review remains pending"
  false

policeCrowdCharacterisationReceipt : ConductSourceReceipt
policeCrowdCharacterisationReceipt = conductSourceReceipt
  policeSaidCrowdThreatenedJostledAssaultedOfficers policeOfficialAccount
  "NSW Police / Assistant Commissioner Peter McKenna and Commissioner Mal Lanyon, as reported by ABC"
  "NSW Police defends officers' actions in violent clashes with Sydney protesters"
  "ABC News, 10 February 2026"
  "Police said officers were threatened, jostled and assaulted during melees/rolling fights and defended the force used"
  false

policeAggressiveVolatileReceipt : ConductSourceReceipt
policeAggressiveVolatileReceipt = conductSourceReceipt
  policeSaidCrowdAggressiveVolatile policeOfficialAccount
  "NSW Police Commissioner Mal Lanyon, ABC 7.30 transcript"
  "Police and protesters clash at Sydney rally"
  "ABC 7.30, 10 February 2026"
  "Commissioner characterised the crowd as significant, aggressive and volatile and praised officers' response"
  false

leccScopeReceipt : ConductSourceReceipt
leccScopeReceipt = conductSourceReceipt
  leccInvestigatingLawfulnessAndAppropriateness independentOversightInvestigation
  "Law Enforcement Conduct Commission"
  "Operation Makalu: LECC investigation into the police operation at the Sydney Town Hall Protest on 9 February 2026"
  "https://www.lecc.nsw.gov.au/publications/lecc-investigation-into-the-police-operation-at-the-sydney-town-hall-protest-on-9-february-2026"
  "LECC is investigating the lawfulness and appropriateness of NSW Police conduct and alleged misconduct against attendees"
  false

leccScaleReceipt : ConductSourceReceipt
leccScaleReceipt = conductSourceReceipt
  leccLargestComplaintVolume independentOversightInvestigation
  "Law Enforcement Conduct Commission"
  "Media Release - Operation Makalu: Investigation Update"
  "24 May 2026"
  "LECC said Operation Makalu involved the largest number of complaints it had ever received: more than 800 complaints, 450+ submitted items and 1000+ hours of CCTV under review"
  false

shadidPleadingReceipt : ConductSourceReceipt
shadidPleadingReceipt = conductSourceReceipt
  shadidAssaultFalseImprisonmentMisfeasanceClaims civilPleadingReported
  "Guardian Australia reporting Eyad Shadid's filed civil claim"
  "Palestinian Australian sues NSW police claiming he was punched at Herzog rally"
  "Guardian Australia, 3 September 2026"
  "Reported pleading alleges assault, false imprisonment, misfeasance in public office and malicious prosecution arising from intervention near the authorised prayer group; allegations are not findings"
  false

postEventChillingReceipt : ConductSourceReceipt
postEventChillingReceipt = conductSourceReceipt
  postEventHomeRaidsAndLaterArrestsChillingEffectAllegation legalObserverReport
  "Legal Observers NSW"
  "Statement of Concern: Police arrests of Herzog protestors post 9th February interfere with LECC investigation, use intimidatory home raid tactics"
  "2 June 2026"
  "Legal Observers NSW alleges later arrests and early-morning home raids chilled participation in the LECC process and protest activity"
  false

------------------------------------------------------------------------
-- BIDI: stronger systemic/lawfulness claims require independent adjudicative
-- or oversight closure, not accumulation of allegation sources alone.
------------------------------------------------------------------------

data PoliceAuditClaim : Set where
  specificForceEventOccurred : PoliceAuditClaim
  policeOperationalPatternAlleged : PoliceAuditClaim
  policeOperationalPatternCorroborated : PoliceAuditClaim
  systemicUnlawfulPoliceStrategy : PoliceAuditClaim
  commandLevelProvocationIntent : PoliceAuditClaim

data PoliceAuditProducer : Set where
  eventVideoOrDirectObservationProducer : PoliceAuditProducer
  multiIncidentSourceBundleProducer : PoliceAuditProducer
  independentOversightCorroborationProducer : PoliceAuditProducer
  finalLawfulnessFindingProducer : PoliceAuditProducer
  commandIntentDocumentProducer : PoliceAuditProducer

reversePoliceAudit : PoliceAuditClaim → PoliceAuditProducer
reversePoliceAudit specificForceEventOccurred = eventVideoOrDirectObservationProducer
reversePoliceAudit policeOperationalPatternAlleged = multiIncidentSourceBundleProducer
reversePoliceAudit policeOperationalPatternCorroborated = independentOversightCorroborationProducer
reversePoliceAudit systemicUnlawfulPoliceStrategy = finalLawfulnessFindingProducer
reversePoliceAudit commandLevelProvocationIntent = commandIntentDocumentProducer

record PoliceAuditBoundary : Set where
  constructor policeAuditBoundary
  field
    legalObserverReportEqualsLECCFinalFinding : Bool
    legalObserverReportEqualsLECCFinalFindingIsFalse : legalObserverReportEqualsLECCFinalFinding ≡ false
    bodyWornBoastAloneProvesWholeOperationIntent : Bool
    bodyWornBoastAloneProvesWholeOperationIntentIsFalse : bodyWornBoastAloneProvesWholeOperationIntent ≡ false
    policeSelfDefenceAccountDisprovesEveryMisconductAllegation : Bool
    policeSelfDefenceAccountDisprovesEveryMisconductAllegationIsFalse : policeSelfDefenceAccountDisprovesEveryMisconductAllegation ≡ false
    complaintVolumeEqualsMisconductCount : Bool
    complaintVolumeEqualsMisconductCountIsFalse : complaintVolumeEqualsMisconductCount ≡ false

canonicalPoliceAuditBoundary : PoliceAuditBoundary
canonicalPoliceAuditBoundary = policeAuditBoundary false refl false refl false refl false refl

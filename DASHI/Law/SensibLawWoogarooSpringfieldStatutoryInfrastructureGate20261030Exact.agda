{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogarooDeveloperGasTemporalIdentityCut20261030Exact as Developer
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as Lobby
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim

------------------------------------------------------------------------
-- SPRINGFIELD PLANNING ACT ss 275T-275ZA (2024)
--
-- SOURCE-POSITIVE legal process, NOT another free-floating influence graph:
-- 275T expressly defines SCG as Springfield City Group Pty Limited,
-- ACN 055 714 531. For a non-SCG plan application, 275X/Y require
-- notice, disclosure to SCG and applicant response to timely submissions.
-- 275Z calls for a statement covering area effects, infrastructure
-- servicing and remedies. Council must have regard to that statement;
-- 275Z(3) explicitly prevents non-compliance alone stopping decision.
-- 275W separately restricts approval to specified infrastructure routes.
--
-- The indexed 6243/2023/LAP s275Z comment proves a DOCUMENT TITLE ONLY.
-- Its letter, contents, timing, applicable agreement, actual satisfaction,
-- gas provision and any response/approval reasoning are NOT acquired.
-- A statutory review right is neither a 2025 lobbying instruction nor a
-- Commonwealth EPBC 2019/8575 approval role.
------------------------------------------------------------------------

queenslandPlanningAct2024 : Source.AttributedSource
queenslandPlanningAct2024 = Source.mkNoDOISource
  "Queensland Parliament"
  "Planning Act 2016, Chapter 7 Part 4C, sections 275T-275ZA"
  "Queensland legislation, in-force 6 June 2024 (provisions enacted 2020)"
  "6 June 2024"
  "https://www.legislation.qld.gov.au/view/whole/html/inforce/2024-06-06/act-2016-025"
  Source.governmentSource
  "Original statute defines SCG by ACN; 275V owner consent; 275W infrastructure threshold; 275X/Y notice and materials; 275Z statement on adverse impact, servicing and options plus council regard and no automatic decision bar; 275ZAA Urban Utilities representation; 275ZA decision notice. Does not name a gas servicing contract or prove particular case compliance."
  Source.publicAttribution

councilSpringviewIndex : Source.AttributedSource
councilSpringviewIndex = Developer.springfieldCityGroupCouncilCommentIndex2024

statutorySourceAtlas : Source.AttributedSourceAtlas
statutorySourceAtlas = Source.mkSourceAtlas
  "Springfield statutory planning and infrastructure statement route"
  "DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact"
  (queenslandPlanningAct2024 ∷ councilSpringviewIndex ∷ [])
  "Statute and the Council index are distinct original producers. No signed comment document or agreement imported."

-- A dated, literal corporate ID, not a guessed QID or title inference.
scgACN : String
scgACN = "055714531"

data ParticipationRole : Set where
  statutorySCGRecipientAndCommenter : ParticipationRole
  stateRegisteredLobbyistContact : ParticipationRole

roleDistinct :
  statutorySCGRecipientAndCommenter ≡ stateRegisteredLobbyistContact → ⊥
roleDistinct ()

data RequiredSection : Set where
  s275V : RequiredSection
  s275W : RequiredSection
  s275X : RequiredSection
  s275Y : RequiredSection
  s275Z : RequiredSection
  s275ZAA : RequiredSection
  s275ZA : RequiredSection

data StatutoryFunction : Set where
  ownerConsentOrException : StatutoryFunction
  infrastructureServicingSatisfaction : StatutoryFunction
  preApplicationNoticeToSCG : StatutoryFunction
  disclosureAndResponsesToSCG : StatutoryFunction
  scgWrittenStatement : StatutoryFunction
  urbanUtilitiesRepresentations : StatutoryFunction
  noticeOfDecision : StatutoryFunction

sectionFunction : RequiredSection → StatutoryFunction
sectionFunction s275V = ownerConsentOrException
sectionFunction s275W = infrastructureServicingSatisfaction
sectionFunction s275X = preApplicationNoticeToSCG
sectionFunction s275Y = disclosureAndResponsesToSCG
sectionFunction s275Z = scgWrittenStatement
sectionFunction s275ZAA = urbanUtilitiesRepresentations
sectionFunction s275ZA = noticeOfDecision

-- The statutory roles themselves are source-described. Their satisfaction
-- in any particular Council case is an independent empirical/legal question.
data Section275ZTopic : Set where
  adverseStructurePlanImpact : Section275ZTopic
  agreementIndexedInfrastructureServicing : Section275ZTopic
  optionsToAddressEitherIssue : Section275ZTopic

section275ZRequiredTopics : List Section275ZTopic
section275ZRequiredTopics =
  adverseStructurePlanImpact ∷
  agreementIndexedInfrastructureServicing ∷
  optionsToAddressEitherIssue ∷ []

section275ZContainsInfrastructureSlot :
  section275ZRequiredTopics ≡
  (adverseStructurePlanImpact ∷ agreementIndexedInfrastructureServicing ∷
   optionsToAddressEitherIssue ∷ [])
section275ZContainsInfrastructureSlot = refl

data InfrastructureApprovalAlternative : Set where
  agreementServicingPresent : InfrastructureApprovalAlternative
  agreementServicingExpected : InfrastructureApprovalAlternative
  consistentInterimServicingPresent : InfrastructureApprovalAlternative
  consistentInterimServicingExpected : InfrastructureApprovalAlternative

data EvidenceSlot : Set where
  planApplicationNonSCGStatus : EvidenceSlot
  section275XPrelodgementService : EvidenceSlot
  section275YPlanAndAmendments : EvidenceSlot
  actual275ZStatementFace : EvidenceSlot
  councilAssessmentAndRegard : EvidenceSlot
  currentInfrastructureAgreementFace : EvidenceSlot
  infrastructureCategoryAndScope : EvidenceSlot
  applicableParcelAndAssets : EvidenceSlot
  specificGasReticulationContract : EvidenceSlot
  2025LobbyMeetingActualSubject : EvidenceSlot
  commonwealth20198575DecisionFile : EvidenceSlot

record IndexedCasePayment : Set where
  constructor indexed-case-payment
  field
    applicationId : String
    index : Source.AttributedSource
    scgCommentDocumentIndexed : Bool
    signedCommentFacePaid : Bool
    nonSCGQualificationIndependentlyPaid : Bool
    specificInfrastructureAgreementPaid : Bool
    gasTopicPaid : Bool

springviewIndexState : IndexedCasePayment
springviewIndexState = indexed-case-payment
  "6243/2023/LAP"
  councilSpringviewIndex
  true false false false false

-- The Council's statutory satisfaction may occur under different serviced
-- infrastructure schedules.  Section 275W does not itself specify gas.
data ServicingWorld : Set where
  nonGasAgreementOnly : ServicingWorld
  agreementAlsoSpecifiesGas : ServicingWorld

data StatutorySatisfactionObservation : Set where
  listedInfrastructurePathSufficient : StatutorySatisfactionObservation

data GasInAgreement : Set where
  gasNotEstablished : GasInAgreement
  gasSpecificallyDocumented : GasInAgreement

observedInfrastructure : ServicingWorld → StatutorySatisfactionObservation
observedInfrastructure nonGasAgreementOnly = listedInfrastructurePathSufficient
observedInfrastructure agreementAlsoSpecifiesGas = listedInfrastructurePathSufficient

gasScope : ServicingWorld → GasInAgreement
gasScope nonGasAgreementOnly = gasNotEstablished
gasScope agreementAlsoSpecifiesGas = gasSpecificallyDocumented

differentGasScope :
  gasScope nonGasAgreementOnly ≡ gasScope agreementAlsoSpecifiesGas → ⊥
differentGasScope ()

statutoryInfrastructurePathDoesNotProveGas :
  INF.FactorsThrough observedInfrastructure gasScope → ⊥
statutoryInfrastructurePathDoesNotProveGas =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness nonGasAgreementOnly
      agreementAlsoSpecifiesGas refl differentGasScope)

-- SCG's statutory locus is a positive role in a local plan process;
-- the same observed statutory locus is compatible with either outcome
-- of a wholly separate 2025 Queensland lobbyist meeting.
data LobbyWorld : Set where
  statutoryRoleNoGasLobbyRequest : LobbyWorld
  statutoryRoleWithSeparatelyPaidGasRequest : LobbyWorld

data StatutoryRoleObserved : Set where
  namedSCGRightsInPlanningAct : StatutoryRoleObserved

data LobbySubjectRecord : Set where
  actualGasSubjectUnpaid : LobbySubjectRecord
  actualGasSubjectPaid : LobbySubjectRecord

statutoryRole : LobbyWorld → StatutoryRoleObserved
statutoryRole statutoryRoleNoGasLobbyRequest = namedSCGRightsInPlanningAct
statutoryRole statutoryRoleWithSeparatelyPaidGasRequest = namedSCGRightsInPlanningAct

lobbySubject : LobbyWorld → LobbySubjectRecord
lobbySubject statutoryRoleNoGasLobbyRequest = actualGasSubjectUnpaid
lobbySubject statutoryRoleWithSeparatelyPaidGasRequest = actualGasSubjectPaid

distinctLobbySubject :
  lobbySubject statutoryRoleNoGasLobbyRequest ≡
  lobbySubject statutoryRoleWithSeparatelyPaidGasRequest → ⊥
distinctLobbySubject ()

statutoryRoleDoesNotDetermineSantoroRequest :
  INF.FactorsThrough statutoryRole lobbySubject → ⊥
statutoryRoleDoesNotDetermineSantoroRequest =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness statutoryRoleNoGasLobbyRequest
      statutoryRoleWithSeparatelyPaidGasRequest refl distinctLobbySubject)

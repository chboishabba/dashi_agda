{-# OPTIONS --safe #-}
module DASHI.Law.SensibLawWoogarooSpringfield2020CompetitivePlanningTransmission20261030Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogarooSpringfieldStatutoryInfrastructureGate20261030Exact as Law
import DASHI.Law.SensibLawWoogarooDeveloperGasTemporalIdentityCut20261030Exact as Developer
import DASHI.Wikimedia.IdentifierExact as Identifier
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Ibrahim

------------------------------------------------------------------------
-- SOURCE-ORIGINAL AUSTRALIAN SPRINGFIELD PLANNING POLICY TRANSMISSION, 2020
-- Cherish and SCG are documented conflicting planning stakeholders, rather
-- than assumed collaborators.  A documented proposed legislation amendment
-- does not pay a future Santoro gas meeting, financial transfer, or federal
-- EPBC 2019/8575 decision.  Historical Forest Wind is a separate project;
-- the 2020 Bill also amended *Springfield* planning legislation.
------------------------------------------------------------------------

scgOriginalSubmission10 : Source.AttributedSource
scgOriginalSubmission10 = Source.mkNoDOISource
  "Bob Sharpless / Springfield City Group Pty Ltd"
  "Submission 010, Forest Wind Farm Development Bill 2020"
  "Original SCG signed first-party submission to Queensland parliamentary committee"
  "5 June 2020"
  "https://documents.parliament.qld.gov.au/com/SDTIMC-C65A/RN156PFWFD-45DA/submissions/00000010.pdf"
  Source.practitionerSource
  "Signed by Bob Sharpless as Deputy Chairman. SCG advocates for legally structured planning participation and adjusting proposed s275W to preserve existing infrastructure-agreement timing and interim servicing. States SIA signed 26 March 1998. An advocacy argument is not proof of gas inclusion or a private transfer."
  Source.publicAttribution

cherishOriginalSubmission12 : Source.AttributedSource
cherishOriginalSubmission12 = Source.mkNoDOISource
  "Samuel Lin / Cherish Enterprises Pty Ltd, assisted by Johnson Lin and Stephen Fynes-Clinton"
  "Submission 012, Forest Wind Farm Development Bill 2020"
  "Original Cherish first-party submission to Queensland parliamentary committee"
  "June 2020"
  "https://documents.parliament.qld.gov.au/com/SDTIMC-C65A/RN156PFWFD-45DA/submissions/00000012.pdf"
  Source.practitionerSource
  "Original indexed submission excerpts: Cherish says SCG is its direct commercial competitor, that Cherish purchased its land from SCG about 1992 and that Stockland was developing part of Cherish's approved land. Allegations/claims and dates are source-authored, not independently authenticated deed, corporate control, tribunal finding or current site contract. Full 12 MB original PDF face not inspected."
  Source.publicAttribution

parliamentaryCommitteeReport2020 : Source.AttributedSource
parliamentaryCommitteeReport2020 = Source.mkNoDOISource
  "Queensland Parliament, State Development Tourism Innovation and Manufacturing Committee"
  "Report No. 1, 56th Parliament, Forest Wind Farm Development Bill 2020"
  "Original parliamentary committee report tabled 3 July 2020"
  "3 July 2020"
  "https://www.parliament.qld.gov.au/Work-of-the-Assembly/Tabled-Papers/docs/5620t1004/5620t1004.pdf"
  Source.governmentSource
  "Original committee report carries quoted 12 June 2020 Treasury response: historic SCG exclusive precinct-plan application approach created effective veto; the Bill did not seek to reinstate that veto, and non-SCG developers may apply while council considers SCG infrastructure submissions. Reports Cherish objection, SCG support and committee assessment. It is one parliamentary report, not an independently acquired Treasury letter."
  Source.publicAttribution

queenslandGovernmentFinalExplanation2020 : Source.AttributedSource
queenslandGovernmentFinalExplanation2020 = Source.mkNoDOISource
  "Kate Jones MP / Queensland Government"
  "Explanatory Notes, amendments during consideration in detail, Forest Wind Farm Development Bill 2020"
  "Original Queensland legislation bill explanatory notes, 12 August 2020"
  "12 August 2020"
  "https://www.legislation.qld.gov.au/view/html/bill.third.exp/bill-2019-006"
  Source.governmentSource
  "Source-original governmental amendment note explicitly credits SCG submission as reason for refining proposed s275W(1): preserve existing infrastructure agreement scope and accept interim infrastructure. Distinguishes stated authorial policy rationale from a proved private tasking or specific 2019/8575 outcome."
  Source.publicAttribution

governmentHumanRightsStatement2020 : Source.AttributedSource
governmentHumanRightsStatement2020 = Source.mkNoDOISource
  "Queensland Government"
  "Human Rights Statement of Compatibility, Forest Wind Farm Development Bill 2020"
  "Official government bill documentation, Springfield Planning Act amendment pages"
  "2020"
  "https://cabinet.qld.gov.au/documents/2020/May/ForWinBill/Attachments/SoC.pdf"
  Source.governmentSource
  "Government says SCG has an advice role and broader applicants gain access; the 2018 QCA 266 court case precipitated planning clarification. Not a judicial holding or any approval of a gas infrastructure schedule."
  Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas = Source.mkSourceAtlas
  "Springfield 2020 original first-party political submissions, committee assessment and government adoption"
  "DASHI.Law.SensibLawWoogarooSpringfield2020CompetitivePlanningTransmission20261030Exact"
  (scgOriginalSubmission10 ∷ cherishOriginalSubmission12 ∷
   parliamentaryCommitteeReport2020 ∷ queenslandGovernmentFinalExplanation2020 ∷
   governmentHumanRightsStatement2020 ∷ [])
  "Keep original submitters, legislative author and parliamentary report separate. Reproduction in committee report does not become second independent Cherish or SCG testimony."

-- The source-authored first-party propositions remain attributed assertions.
data ProvenanceGrade : Set where
  firstPartyPublishedArgument : ProvenanceGrade
  committeeOriginalCarrierOfReply : ProvenanceGrade
  governmentOriginalAmendmentExplanation : ProvenanceGrade
  enactedStatutoryRule : ProvenanceGrade

data Relationship : Set where
  competitorClaim : Relationship
  oldOwnerSaleClaim : Relationship
  developerAgreementClaim : Relationship
  policySubmission : Relationship
  legislativeResponse : Relationship
  gasServicingTransaction : Relationship

record BoundedClaim : Set where
  constructor bounded-claim
  field
    relationship : Relationship
    grade : ProvenanceGrade
    source : Source.AttributedSource
    exactScope : String
    underlyingTransactionAcquired : Bool
open BoundedClaim public

cherishCompetitorAssertion : BoundedClaim
cherishCompetitorAssertion = bounded-claim
  competitorClaim firstPartyPublishedArgument cherishOriginalSubmission12
  "Cherish says SCG competes with it in greenfield residential development and that statutory influence raises concerns."
  false

cherish1992LandSaleAssertion : BoundedClaim
cherish1992LandSaleAssertion = bounded-claim
  oldOwnerSaleClaim firstPartyPublishedArgument cherishOriginalSubmission12
  "Cherish says it purchased the relevant land from SCG about 1992; no historical signed deed, title or parcel ID acquired."
  false

cherishStockland2020DevelopmentAssertion : BoundedClaim
cherishStockland2020DevelopmentAssertion = bounded-claim
  developerAgreementClaim firstPartyPublishedArgument cherishOriginalSubmission12
  "Cherish says part of its then-approved Springfield land was being developed by Stockland; original contract or exact 2019/8575 same-parcel join unpaid."
  false

record PolicyTransmission : Set where
  constructor policy-transmission
  field
    originalRequest : Source.AttributedSource
    officialResponse : Source.AttributedSource
    enactedRule : Source.AttributedSource
    originalSubmissionPaid : Bool
    governmentCreditedSpecificAmendment : Bool
    affectedSection : String
    originalGasClausePaid : Bool
    confidentialTaskingEstablished : Bool
    federalEPBC20198575ConnectionProved : Bool
open PolicyTransmission public

scgInfrastructureAmendmentChain : PolicyTransmission
scgInfrastructureAmendmentChain = policy-transmission
  scgOriginalSubmission10
  queenslandGovernmentFinalExplanation2020
  Law.queenslandPlanningAct2024
  true true
  "Planning Act 2016 s275W(1), as amended 2020: infrastructure-agreement and interim infrastructure choices"
  false false false

-- This is a *positive* same-policy-source transmission, not an assumed
-- influence-on-any-policy theorem or a gas project decision.
policyReceiptIsAttributedToGovernment : 
  governmentCreditedSpecificAmendment scgInfrastructureAmendmentChain ≡ true
policyReceiptIsAttributedToGovernment = refl

data RegulatoryWorld : Set where
  documented2020ChangeNoGasProject : RegulatoryWorld
  documented2020ChangeWithSeparateGasContract : RegulatoryWorld

data CommonPolicyRecord : Set where
  publicSCGSubmissionAndAmendment : CommonPolicyRecord

data PrivateGasTransaction : Set where
  noAuthenticatedGasDeal : PrivateGasTransaction
  independentlyAuthenticatedGasDeal : PrivateGasTransaction

observed2020Policy : RegulatoryWorld → CommonPolicyRecord
observed2020Policy documented2020ChangeNoGasProject = publicSCGSubmissionAndAmendment
observed2020Policy documented2020ChangeWithSeparateGasContract = publicSCGSubmissionAndAmendment

actualGasTransaction : RegulatoryWorld → PrivateGasTransaction
actualGasTransaction documented2020ChangeNoGasProject = noAuthenticatedGasDeal
actualGasTransaction documented2020ChangeWithSeparateGasContract = independentlyAuthenticatedGasDeal

differentPrivateTransaction :
  actualGasTransaction documented2020ChangeNoGasProject ≡
  actualGasTransaction documented2020ChangeWithSeparateGasContract → ⊥
differentPrivateTransaction ()

publicPlanningAmendmentDoesNotDetermineGasContract :
  INF.FactorsThrough observed2020Policy actualGasTransaction → ⊥
publicPlanningAmendmentDoesNotDetermineGasContract =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness documented2020ChangeNoGasProject
      documented2020ChangeWithSeparateGasContract refl differentPrivateTransaction)

data PlanningAuthority : Set where
  priorEffectivePrecinctApplicationControl : PlanningAuthority
  nonSCGApplicationWithSCGAdvice : PlanningAuthority

data StateInstitutionalRole : Set where
  statePlanningActSCGStatement : StateInstitutionalRole
  stateOfficeSantoroMeeting : StateInstitutionalRole
  commonwealthEPBCApproval : StateInstitutionalRole

roleDistinction1 :
  statePlanningActSCGStatement ≡ stateOfficeSantoroMeeting → ⊥
roleDistinction1 ()

roleDistinction2 :
  stateOfficeSantoroMeeting ≡ commonwealthEPBCApproval → ⊥
roleDistinction2 ()

-- Reuse QID as general statutory navigation only; no guessed person QIDs.
legalNavigationCoordinate : Identifier.ItemId
legalNavigationCoordinate = Ibrahim.environmentalLawQid

-- The commercial competitor claim cannot be promoted into an official court
-- finding of competitive harm or a 2026 title/transfer receipt. Similarly,
-- original first-party 1992 sale testimony must be checked against title.
data CompetingHistoryWorld : Set where
  salesNarrativeWithoutAuthenticatedDeed : CompetingHistoryWorld
  salesNarrativeWithAuthenticatedDeed : CompetingHistoryWorld

data SamePublishedCherishSubmission : Set where
  cherishNarrative : SamePublishedCherishSubmission

data OriginalParcelDeed : Set where
  originalDeedOpen : OriginalParcelDeed
  originalDeedPaid : OriginalParcelDeed

recordedClaim : CompetingHistoryWorld → SamePublishedCherishSubmission
recordedClaim salesNarrativeWithoutAuthenticatedDeed = cherishNarrative
recordedClaim salesNarrativeWithAuthenticatedDeed = cherishNarrative

historicalDeed : CompetingHistoryWorld → OriginalParcelDeed
historicalDeed salesNarrativeWithoutAuthenticatedDeed = originalDeedOpen
historicalDeed salesNarrativeWithAuthenticatedDeed = originalDeedPaid

deedDiffers :
  historicalDeed salesNarrativeWithoutAuthenticatedDeed ≡
  historicalDeed salesNarrativeWithAuthenticatedDeed → ⊥
deedDiffers ()

firstPartyHistoryDoesNotSupplyOriginalDeed :
  INF.FactorsThrough recordedClaim historicalDeed → ⊥
firstPartyHistoryDoesNotSupplyOriginalDeed =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness salesNarrativeWithoutAuthenticatedDeed
      salesNarrativeWithAuthenticatedDeed refl deedDiffers)

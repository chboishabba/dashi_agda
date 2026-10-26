module DASHI.Law.SensibLawWoogarooEPBC95C135ADecisionFileMaxCut20261027Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawWoogarooPostApprovalPoliticalGasBenefit20261027Exact as Post
import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact as Cumulative

------------------------------------------------------------------------
-- EPBC 2019/8575 OCTOBER 2026 DECISION FILE: EXACT STATUTORY CUT
--
-- Correct document sequence: s95B comment/response delivery, then s95C
-- Secretary recommendation, then Part 9 approval, then s135A(2) report
-- request. s136 requires protected environmental and economic/social
-- considerations; the existence of a housing narrative is not evidence
-- that it displaced mandatory environmental consideration.
--
-- The four 19 Aug 2026 National Environmental Standards were registered
-- but, per 22 Oct DCCEEW commencement guidance, were NOT yet applicable
-- to individual approval decisions on 15 Oct. Other EPBC reforms may
-- have commenced: this is not a blanket "no reform applies" statement.
-- No new universal judicial-review limitation date is asserted.
------------------------------------------------------------------------

epbcActAsAtDecision : Source.AttributedSource
epbcActAsAtDecision = Source.mkNoDOISource
  "Parliament of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 — compilation C2026C00369"
  "Federal Register of Legislation: law in force 24 August 2026"
  "24 August 2026"
  "https://www.legislation.gov.au/C2004A00485/2026-08-24/2026-08-24/text/original/epub/OEBPS/document_1/document_1.html"
  Source.governmentSource
  "Original compilation current on 15 October: 95B(1) requires revised/augmented information, summary response AND copies of public comments to Minister; 95C(1)-(2) requires a Secretary recommendation on approval/conditions after 95B; 135A(2) permits a person to ask the Secretary for that report AFTER decision subject to limited withholding; 136(1)-(2) requires protected-matters AND economic/social consideration, ESD, the 95B/95C material and other relevant information."
  Source.publicAttribution

epbcApproval15Oct : Source.AttributedSource
epbcApproval15Oct = Source.mkNoDOISource
  "Australian Government — National Environmental Protection Agency"
  "EPBC all-notices register: Springfield Residential Development (2019/8575)"
  "Commonwealth original public decision notice listing"
  "15 October 2026"
  "https://epbcpublicportal.environment.gov.au/all-notices/"
  Source.governmentSource
  "Original notices listing records 'Decision on approval of action: Approved with conditions', not the full signed approval, exact approving officer or binding conditions."
  Source.publicAttribution

nationalEPAAgencyDelegation : Source.AttributedSource
nationalEPAAgencyDelegation = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "Greater accountability and transparency in decision-making"
  "Official government reform commencement guidance"
  "22 October 2026"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/greater-accountability-transparency-decision-making"
  Source.governmentSource
  "The National EPA commenced 1 July 2026 and assesses projects/sets conditions under delegation from the Environment Minister. Portfolio ministerial accountability does not establish whether Murray Watt or a particular delegate personally signed EPBC 2019/8575."
  Source.publicAttribution

nationalStandardsTiming : Source.AttributedSource
nationalStandardsTiming = Source.mkNoDOISource
  "Department of Climate Change, Energy, the Environment and Water"
  "National Environmental Standards: registered but individual approval test uncommenced"
  "Original official implementation guidance, last updated 17 September 2026"
  "17 September 2026"
  "https://www.dcceew.gov.au/environment/epbc/epbc-act-reform/standards"
  Source.governmentSource
  "Four new standards made 19 August 2026 apply to individual assessments/approvals only after new approval tests begin on or before 1 December 2026; they do not automatically govern the 15 October 2026 decision. Confirm any relevant other transitional instrument separately."
  Source.publicAttribution

data FileAtom : Set where
  publicApprovalListing : FileAtom
  signedFinalDecision : FileAtom
  section95BRevisedPreliminaryDocumentation : FileAtom
  section95BPublicCommentCopies : FileAtom
  section95CSectyRecommendation : FileAtom
  section135AReportRequest : FileAtom
  statutoryDelegateAndReasons : FileAtom
  section136ProtectedMattersMatrix : FileAtom
  section136SocialEconomicMatrix : FileAtom
  section139SpeciesAdviceTreatment : FileAtom
  operativeApprovalConditions : FileAtom

data VerificationState : Set where
  primarySourceIdentified : VerificationState
  statutoryDemandIdentified : VerificationState
  decisionFileOriginalMissing : VerificationState
  comparisonNotExecuted : VerificationState

record DecisionFileReceipt : Set where
  constructor decision-file-receipt
  field
    atom : FileAtom
    authority : Source.AttributedSource
    state : VerificationState
    sourcePaidScope : String
    neededForLiveConsumer : String
    contentsOfActual2019_8575DecisionFilePaid : Bool
    noFalsePayment : contentsOfActual2019_8575DecisionFilePaid ≡ false

open DecisionFileReceipt public

originalListing : DecisionFileReceipt
originalListing = decision-file-receipt publicApprovalListing epbcApproval15Oct
  primarySourceIdentified
  "15 Oct 2026 decision listing says approved with conditions."
  "Obtain signed exact notice; do not infer signature, conditions or review grounds."
  false refl

signedApprovalMissing : DecisionFileReceipt
signedApprovalMissing = decision-file-receipt signedFinalDecision epbcApproval15Oct
  decisionFileOriginalMissing
  "The listing does not contain authenticated signed Part 9 final decision in materials inspected."
  "Acquire original signatory, approved footprint, conditions, expiry and decision service/notification timestamps."
  false refl

section95BResponse : DecisionFileReceipt
section95BResponse = decision-file-receipt section95BRevisedPreliminaryDocumentation epbcActAsAtDecision
  statutoryDemandIdentified
  "s95B(1)(a) requires amended proponent material and a summary of comments and response."
  "Actual final proponent document, file versions, attachment list, cumulative-impact Item 4.6(c) answer and receipt to Minister."
  false refl

section95BActualComments : DecisionFileReceipt
section95BActualComments = decision-file-receipt section95BPublicCommentCopies epbcActAsAtDecision
  statutoryDemandIdentified
  "s95B(1)(b)(ii) requires copies of public comments received by the designated proponent to be given to the Minister."
  "Actual set of comment copies and transmission/receipt record; notice count alone is not the complete file."
  false refl

section95CRecommendation : DecisionFileReceipt
section95CRecommendation = decision-file-receipt section95CSectyRecommendation epbcActAsAtDecision
  statutoryDemandIdentified
  "s95C names the Secretary's mandatory recommendation on whether to approve and, if approved, the recommended conditions."
  "Obtain original same-action recommendation report, any permissible withheld portions, and compare recommendation with final signed conditions."
  false refl

section135AStatutoryRequest : DecisionFileReceipt
section135AStatutoryRequest = decision-file-receipt section135AReportRequest epbcActAsAtDecision
  statutoryDemandIdentified
  "s135A(2) requires Secretary to provide requested s95C report after decision, subject to listed exclusions."
  "Submit targeted s135A(2) request, log acknowledgment/date and any exact statutory withholding grounds."
  false refl

section136Factors : DecisionFileReceipt
section136Factors = decision-file-receipt section136ProtectedMattersMatrix epbcActAsAtDecision
  statutoryDemandIdentified
  "s136(1)(a) requires relevant protected matters; s136(2)(bc) specifically points to the s95B material and s95C report."
  "Signed reasons/material-consideration matrix for controlled threatened fauna, cumulative habitat/connectivity and offsets."
  false refl

section136Housing : DecisionFileReceipt
section136Housing = decision-file-receipt section136SocialEconomicMatrix epbcActAsAtDecision
  statutoryDemandIdentified
  "s136(1)(b) explicitly includes economic and social matters; mere inclusion of housing interests is lawful subject to other mandatory obligations."
  "Exact final recommendation/reasons reliance on projected dwelling numbers, housing provision, employment and comparative alternatives."
  false refl

delegateReceipt : DecisionFileReceipt
delegateReceipt = decision-file-receipt statutoryDelegateAndReasons nationalEPAAgencyDelegation
  decisionFileOriginalMissing
  "National EPA institutional delegated role is documented at agency level, not case signatory."
  "Signed final notice, delegation instrument as effective 15 October, personal authorisation and reasons."
  false refl

section139SpeciesAdvice : DecisionFileReceipt
section139SpeciesAdvice = decision-file-receipt section139SpeciesAdviceTreatment epbcActAsAtDecision
  statutoryDemandIdentified
  "The EPBC Act's section 139 addresses approval requirements for threatened species and ecological communities, including relevant conservation advice/recovery-plan consideration according to the controlling provision."
  "Specific threatened-fauna statutory advice, critical habitat/ecological information and any decision-specific treatment of conservation and recovery requirements."
  false refl

signedConditions : DecisionFileReceipt
signedConditions = decision-file-receipt operativeApprovalConditions epbcApproval15Oct
  decisionFileOriginalMissing
  "The dated notices listing only says approved with conditions, without the full condition text or discharge obligations."
  "Actual operative preclearance, staged ecological management, offset schedule, monitoring requirements and any variations."
  false refl

operativeStandardsDistinction : Source.AttributedSource
operativeStandardsDistinction = nationalStandardsTiming

postApprovalFileCut : List DecisionFileReceipt
postApprovalFileCut =
  originalListing ∷
  signedApprovalMissing ∷
  section95BResponse ∷
  section95BActualComments ∷
  section95CRecommendation ∷
  section135AStatutoryRequest ∷
  section136Factors ∷
  section136Housing ∷
  delegateReceipt ∷
  section139SpeciesAdvice ∷
  signedConditions ∷ []

data ApprovalListingPaysSignedConditions : Set where
data AugustStandardsApplyToOctoberApprovalByRegistrationAlone : Set where
data RecommendationReportEqualsFinalSignedDecision : Set where
data PublicCommentCountEqualsActualTransmissionToMinister : Set where
data MinisterPortfolioEqualsPersonalApprovalSignature : Set where
data HousingAsSocialFactorEqualsImproperInfluence : Set where
data SourceExistenceProvesProceduralReviewGround : Set where
data LaterGuidanceWithoutCommencementAppliesRetrospectively : Set where

listingDoesNotPaySignedNotice : ApprovalListingPaysSignedConditions → ⊥
listingDoesNotPaySignedNotice ()

registeredStandardsNotAutomaticallyOperative :
  AugustStandardsApplyToOctoberApprovalByRegistrationAlone → ⊥
registeredStandardsNotAutomaticallyOperative ()

section95CNotApprovalNotice : RecommendationReportEqualsFinalSignedDecision → ⊥
section95CNotApprovalNotice ()

commentCountNotTransmissionReceipt :
  PublicCommentCountEqualsActualTransmissionToMinister → ⊥
commentCountNotTransmissionReceipt ()

portfolioNotPersonalSignature :
  MinisterPortfolioEqualsPersonalApprovalSignature → ⊥
portfolioNotPersonalSignature ()

socialFactorNotCorruption :
  HousingAsSocialFactorEqualsImproperInfluence → ⊥
socialFactorNotCorruption ()

existenceNotReviewGround : SourceExistenceProvesProceduralReviewGround → ⊥
existenceNotReviewGround ()

futureRuleNotPastRule :
  LaterGuidanceWithoutCommencementAppliesRetrospectively → ⊥
futureRuleNotPastRule ()

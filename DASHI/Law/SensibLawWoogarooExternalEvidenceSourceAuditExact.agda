module DASHI.Law.SensibLawWoogarooExternalEvidenceSourceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EXTERNAL EVIDENCE SOURCE AUDIT
--
-- This module records source-classification results from the current Woogaroo
-- legal-evidence tranche. It is deliberately conservative: a useful map,
-- register, metadata record, portal label, council index or submission does
-- not silently become the statutory conclusion sought by another consumer.
------------------------------------------------------------------------

data EvidenceSourceClass : Set where
  primaryFederalProceduralNotice : EvidenceSourceClass
  primaryFederalPublicCommentInvitation : EvidenceSourceClass
  primaryFederalPublicationNotice : EvidenceSourceClass
  primaryFederalPortalStatus : EvidenceSourceClass
  primaryFederalFOIAdministrativeContext : EvidenceSourceClass
  primaryCouncilApplicationDocumentIndex : EvidenceSourceClass
  primaryCouncilWorksProgression : EvidenceSourceClass
  primaryLibraryLegalDepositMetadata : EvidenceSourceClass
  primaryQueenslandSpatialDataset : EvidenceSourceClass
  primaryFederalCriticalHabitatRegister : EvidenceSourceClass
  primaryQueenslandFishHabitatRegime : EvidenceSourceClass
  foreignJurisdictionBiodiversityDataset : EvidenceSourceClass
  campaignOrSubmissionEvidence : EvidenceSourceClass
  portalUiStatus : EvidenceSourceClass

data AuditDisposition : Set where
  sourcePaid : AuditDisposition
  relevantButConsumerOpen : AuditDisposition
  wrongJurisdiction : AuditDisposition
  wrongStatutoryType : AuditDisposition
  secondaryOnly : AuditDisposition
  ambiguousUiOnly : AuditDisposition

record SourceAuditReceipt : Set where
  constructor source-audit-receipt
  field
    sourceClass : EvidenceSourceClass
    title : String
    boundedFinding : String
    disposition : AuditDisposition
    exactConsumer : String
    residual : String
    createsLegalConclusion : Bool
    createsLegalConclusionIsFalse : createsLegalConclusion ≡ false

open SourceAuditReceipt public

extensionNoticeAudit : SourceAuditReceipt
extensionNoticeAudit = source-audit-receipt
  primaryFederalProceduralNotice
  "EPBC 2019/8575 notification of extension to time in which to make a decision"
  "The delegate decision period was extended by 20 business days to 1 October 2026 under EPBC Act s 130(1A), and Declan O'Connor-Cox is named as the authorised decision-maker."
  sourcePaid
  "EPBC 2019/8575 procedural timing and delegate identity"
  "does not establish approval, refusal or environmental merits"
  false refl

publicCommentInvitationAudit : SourceAuditReceipt
publicCommentInvitationAudit = source-audit-receipt
  primaryFederalPublicCommentInvitation
  "2019-8575-Draft-PD.pdf"
  "The uploaded file is a one-page invitation for public comment. It confirms controlled-action status, Preliminary Documentation assessment and ss 18/18A controlling species/community, and points to the Saunders Havill documentation location. It is not itself the substantive Preliminary Documentation habitat bundle."
  sourcePaid
  "EPBC project identity / assessment pathway / controlling provisions"
  "recover the actual Preliminary Documentation and final habitat maps/tables/appendices"
  false refl

finalPDPublicationNoticeAudit : SourceAuditReceipt
finalPDPublicationNoticeAudit = source-audit-receipt
  primaryFederalPublicationNotice
  "2019-8575-Final-PD.pdf"
  "Despite its filename, the uploaded carrier is a one-page s 95B(2) publication/information notice. It records 1,786 comments and states that the Preliminary Documentation plus a summary of comments were made available from 23 July to 20 August 2026. It is not the substantive final Preliminary Documentation."
  sourcePaid
  "EPBC 2019/8575 publication chronology / comment-count existence / existence of comments-summary carrier"
  "acquire the substantive 2026 Preliminary Documentation volumes/attachments and the actual summary/response to comments"
  false refl

currentPortalStatusAudit : SourceAuditReceipt
currentPortalStatusAudit = source-audit-receipt
  primaryFederalPortalStatus
  "EPBC Act Public Portal current project page for 2019/8575"
  "Fresh web retrieval on 10 September 2026 shows Project Status 'Final Preliminary Documentation Published' and Decision Status 'Published'. The same page currently fails to expose project files, returning a SharePoint-integration/permissions error. This UI/status text is not sufficient to identify an approval/refusal instrument, especially while the separately dated s 130(1A) notice gives a decision period ending 1 October 2026."
  ambiguousUiOnly
  "current federal project/publication status and acquisition routing"
  "obtain an actual approval/refusal decision instrument before asserting that 'Decision Status: Published' means a final Part 9 merits decision; use the dated extension notice for the known statutory timing unless superseded by a later exact decision instrument"
  false refl

federalFOIHousingContextAudit : SourceAuditReceipt
federalFOIHousingContextAudit = source-audit-receipt
  primaryFederalFOIAdministrativeContext
  "DCCEEW FOI LEX 82498 — documents regarding housing projects under the existing EPBC Act"
  "A 2026 FOI release places EPBC 2019/8575 in departmental housing-project status tables. One table records Springfield Residential Development as with DCCEEW and 'Considering Further Information' with a 2,000-home figure; another historical/status extract records Stockland - Cherish Enterprises Pty Ltd, 'Draft documentation published - Open for Pu', 821 and 'No active key decisions'. The same FOI corpus separately documents a Housing Strike Team intended to accelerate assessment of housing projects generally. The retrieved material does not prove that 2019/8575 itself was selected for strike-team fast-tracking, nor any improper influence on its merits."
  relevantButConsumerOpen
  "administrative/development-pressure context only; possible chronology and record-acquisition lead"
  "preserve snapshot dates/version differences; do not infer motive, predetermined approval, strike-team membership or legal merits from housing-program context. If counsel considers it material, acquire the exact dated source table and any 2019/8575-specific internal administrative record."
  false refl

council9281DocumentIndexAudit : SourceAuditReceipt
council9281DocumentIndexAudit = source-audit-receipt
  primaryCouncilApplicationDocumentIndex
  "Ipswich City Council application-document index for 9281/2024/OW"
  "Fresh web retrieval locates 21 public application-document carriers for 9281/2024/OW. The index includes the 20 March 2026 'DA Approved Plans - Negotiated Decision' (21.55 MB), 20 March 2026 Negotiated Decision Notice, 29 August 2025 DA Approved Plans, 21 July 2025 updated drawings/information response, and the 21 August 2024 Tree Retention and Removal Plan, lodged DA plans, desktop assessment and rehabilitation plan. Development.i separately records the application as 'Approved - Negotiated Decision Approved', for Kalina Village 2 Stages 1 to 16, with Earthworks, Clearing Vegetation and Stormwater over properties including 7001 Mur Boulevard."
  sourcePaid
  "acquisition identity and current approval-state carrier for the NCA ss 102-107 / exact-clearing-footprint consumer"
  "download/read the 20 March 2026 negotiated approved plans and decision notice, then extract the exact vegetation-clearing polygon, retained-tree/open-space geometry, conditions and any commencement prerequisites. The index proves the exact carriers exist but does not itself reveal their plan geometry."
  false refl

council9281ExactObjectIdsAudit : SourceAuditReceipt
council9281ExactObjectIdsAudit = source-audit-receipt
  primaryCouncilApplicationDocumentIndex
  "Objective document-object identifiers for 9281/2024/OW"
  "Following the Council index download links exposes stable Objective object IDs even though automated retrieval is blocked: A12705838 = 20 March 2026 DA Approved Plans - Negotiated Decision; A12705835 = 20 March 2026 Negotiated Decision Notice; A11954489 = 29 August 2025 DA Approved Plans; A11816663 = 21 July 2025 Response to Information Request; A11816668 = 21 July 2025 Updated Drawings; A10552668 = 21 August 2024 Tree Retention and Removal Plan; A10552665 = 21 August 2024 Desktop Assessment; A10552664 = 21 August 2024 Rehabilitation to Bulk Earthworks Areas Plan."
  sourcePaid
  "exact carrier identity / acquisition routing for 9281 works geometry and environmental conditions"
  "the Council download endpoint returns 403/cache/timeout failures to automated retrieval. Human/browser acquisition can now target exact object IDs instead of rediscovering documents; contents and geometry remain unpaid until the PDFs are actually acquired."
  false refl

council9293WorksAudit : SourceAuditReceipt
council9293WorksAudit = source-audit-receipt
  primaryCouncilWorksProgression
  "Ipswich City Council 9293/2024/OW — Kalina Village 2 Stages 1 to 4A"
  "Development.i records 9293/2024/OW as decided/approved operational works for road work, drainage, stormwater, earthworks and signage over the same associated Springview/Kalina properties. The Council document index exposes 24 carriers, including 20 March 2026 DA Approved Plans (16.81 MB; Objective object A12705434) and Decision Notice (A12705429), plus 21 July 2025 updated civil drawings."
  relevantButConsumerOpen
  "works-progression / timing-risk context for the s 102 and evidence-preservation consumers"
  "acquire the approved plans only where their geometry/timing helps identify the physical implementation sequence. Approval of civil works is not proof of commencement and does not substitute for the 9281 vegetation-clearing plan."
  false refl

council2082LandscapingAudit : SourceAuditReceipt
council2082LandscapingAudit = source-audit-receipt
  primaryCouncilWorksProgression
  "Ipswich City Council 2082/2025/OW — Kalina Village 2 Stage 1-4A landscaping"
  "Current Development.i records this landscaping operational-works application as decided/approved over 7001 Mur Boulevard and 7006 Panorama Drive. Its document index exposes approved plans (22.18 MB; Objective object A11503353) and decision notice (A11503372). An older generated Development.i snapshot displayed 'In Progress' while also recording an approval/date, so current live status should control unless a primary decision instrument says otherwise."
  relevantButConsumerOpen
  "implementation-progression / chronology context"
  "landscaping approval is downstream-context evidence only. It does not prove vegetation clearing commenced, that Stage 1-4A equals the full 9281 footprint, or that any threatened legal trigger has occurred."
  false refl

slqLegalDepositMetadataAudit : SourceAuditReceipt
slqLegalDepositMetadataAudit = source-audit-receipt
  primaryLibraryLegalDepositMetadata
  "State Library of Queensland record 99184900524002061 — Springfield residential development Mur Boulevard, Springfield Qld : preliminary documentation report"
  "The SLQ catalogue identifies a 2026 four-volume legal-deposit set prepared by Saunders Havill Group for Cherish Enterprises, comprising Part Ai preliminary documentation report; Part Aii vegetation clearing & fauna management plan - clearing directions; Part Aiii attachment A15; and Part B referral material. The catalogue establishes carrier identity/existence and an onsite John Oxley Collection holding, not the contents of the unseen volumes."
  relevantButConsumerOpen
  "acquisition/provenance of the substantive EPBC 2019/8575 Preliminary Documentation corpus"
  "obtain the volume contents from the proponent/agency or inspect/copy the SLQ legal-deposit set; catalogue metadata alone does not pay final-PD merits atoms"
  false refl

qldStatewideCorridorsAudit : SourceAuditReceipt
qldStatewideCorridorsAudit = source-audit-receipt
  primaryQueenslandSpatialDataset
  "Queensland Statewide Biodiversity Corridors"
  "The official Queensland spatial service maps terrestrial and riparian corridor centrelines and state/regional corridor buffers. User-supplied map imagery shows corridor mapping in the broader Springfield/Opossum/Woogaroo landscape."
  relevantButConsumerOpen
  "landscape connectivity evidence for EPBC impact analysis and NCA s 13 essentiality analysis"
  "perform an exact parcel/project-footprint spatial join; mapped corridor status is not itself NCA s 13 critical habitat"
  false refl

federalCriticalHabitatRegisterAudit : SourceAuditReceipt
federalCriticalHabitatRegisterAudit = source-audit-receipt
  primaryFederalCriticalHabitatRegister
  "Commonwealth Register of Critical Habitat"
  "The federal SPRAT register is a separate EPBC critical-habitat register. The supplied screenshot does not show a Woogaroo/koala entry."
  wrongStatutoryType
  "Commonwealth EPBC register only"
  "must not be used as a proxy for Queensland Nature Conservation Act s 13 critical habitat"
  false refl

fishHabitatAreaAudit : SourceAuditReceipt
fishHabitatAreaAudit = source-audit-receipt
  primaryQueenslandFishHabitatRegime
  "Queensland declared Fish Habitat Areas"
  "Declared Fish Habitat Areas are a fisheries/coastal habitat protection regime with their own statutory boundaries and declaration process."
  wrongStatutoryType
  "Queensland fisheries habitat regulation"
  "do not promote to terrestrial NCA s 13 habitat without a separately proven legal/spatial relation"
  false refl

southAustraliaRdfAudit : SourceAuditReceipt
southAustraliaRdfAudit = source-audit-receipt
  foreignJurisdictionBiodiversityDataset
  "data.gov.au dataset 55cbfe04-71bb-4a97-956d-a594ecb6ce4b — Biodiversity mapping (interim)"
  "The supplied RDF identifies a South Australian Department for Environment and Water dataset delivered by Landscape SA regions."
  wrongJurisdiction
  "none for Woogaroo, Queensland"
  "exclude from Queensland parcel/critical-habitat evidence"
  false refl

------------------------------------------------------------------------
-- Explicit no-collapse / WrongType firewalls.
------------------------------------------------------------------------

data StatewideCorridorEqualsNCAS13CriticalHabitat : Set where
data FederalCriticalHabitatRegisterEqualsNCAS13CriticalHabitat : Set where
data FishHabitatAreaEqualsTerrestrialNCACriticalHabitat : Set where
data PublicCommentInvitationEqualsFinalPD : Set where
data PublicationNoticeEqualsSubstantiveFinalPD : Set where
data PortalPublishedStatusEqualsFinalPart9Decision : Set where
data HousingProgramContextEqualsPredeterminedApproval : Set where
data HousingProgramContextEqualsStrikeTeamMembership : Set where
data CouncilDocumentIndexEqualsApprovedPlanGeometry : Set where
data CouncilObjectIdEqualsDocumentContents : Set where
data RelatedWorksApprovalEqualsClearingCommencement : Set where
data LandscapingApprovalEqualsClearingCommencement : Set where
data LegalDepositMetadataEqualsSubstantiveVolumeContents : Set where
data CommentCountEqualsResponseAdequacy : Set where
data ForeignJurisdictionDatasetEqualsQueenslandEvidence : Set where
data PortalExpiredLabelOverridesDatedExtensionNotice : Set where

statewideCorridorDoesNotAutoPayS13 : StatewideCorridorEqualsNCAS13CriticalHabitat → ⊥
statewideCorridorDoesNotAutoPayS13 ()

federalRegisterDoesNotAutoPayQldS13 : FederalCriticalHabitatRegisterEqualsNCAS13CriticalHabitat → ⊥
federalRegisterDoesNotAutoPayQldS13 ()

fishHabitatAreaDoesNotAutoPayTerrestrialS13 : FishHabitatAreaEqualsTerrestrialNCACriticalHabitat → ⊥
fishHabitatAreaDoesNotAutoPayTerrestrialS13 ()

commentInvitationIsNotFinalPD : PublicCommentInvitationEqualsFinalPD → ⊥
commentInvitationIsNotFinalPD ()

publicationNoticeIsNotSubstantiveFinalPD : PublicationNoticeEqualsSubstantiveFinalPD → ⊥
publicationNoticeIsNotSubstantiveFinalPD ()

portalPublishedStatusDoesNotCreateFinalDecision : PortalPublishedStatusEqualsFinalPart9Decision → ⊥
portalPublishedStatusDoesNotCreateFinalDecision ()

housingContextDoesNotCreatePredeterminedApproval : HousingProgramContextEqualsPredeterminedApproval → ⊥
housingContextDoesNotCreatePredeterminedApproval ()

housingContextDoesNotCreateStrikeTeamMembership : HousingProgramContextEqualsStrikeTeamMembership → ⊥
housingContextDoesNotCreateStrikeTeamMembership ()

councilDocumentIndexDoesNotCreatePlanGeometry : CouncilDocumentIndexEqualsApprovedPlanGeometry → ⊥
councilDocumentIndexDoesNotCreatePlanGeometry ()

councilObjectIdDoesNotCreateDocumentContents : CouncilObjectIdEqualsDocumentContents → ⊥
councilObjectIdDoesNotCreateDocumentContents ()

relatedWorksApprovalDoesNotCreateCommencement : RelatedWorksApprovalEqualsClearingCommencement → ⊥
relatedWorksApprovalDoesNotCreateCommencement ()

landscapingApprovalDoesNotCreateClearingCommencement : LandscapingApprovalEqualsClearingCommencement → ⊥
landscapingApprovalDoesNotCreateClearingCommencement ()

legalDepositMetadataDoesNotCreateContents : LegalDepositMetadataEqualsSubstantiveVolumeContents → ⊥
legalDepositMetadataDoesNotCreateContents ()

commentCountDoesNotCreateResponseAdequacy : CommentCountEqualsResponseAdequacy → ⊥
commentCountDoesNotCreateResponseAdequacy ()

southAustralianDatasetDoesNotBecomeQueenslandEvidence : ForeignJurisdictionDatasetEqualsQueenslandEvidence → ⊥
southAustralianDatasetDoesNotBecomeQueenslandEvidence ()

portalLabelDoesNotOverridePrimaryExtensionNotice : PortalExpiredLabelOverridesDatedExtensionNotice → ⊥
portalLabelDoesNotOverridePrimaryExtensionNotice ()

------------------------------------------------------------------------
-- Current acquisition conclusion.
------------------------------------------------------------------------

record CurrentExternalWall : Set where
  constructor current-external-wall
  field
    substantiveFinalPDVolumesStillMissing : Bool
    substantiveFinalPDVolumesStillMissingIsTrue : substantiveFinalPDVolumesStillMissing ≡ true
    actualCommentSummaryResponseStillMissing : Bool
    actualCommentSummaryResponseStillMissingIsTrue : actualCommentSummaryResponseStillMissing ≡ true
    exactFinalPart9DecisionInstrumentStillMissing : Bool
    exactFinalPart9DecisionInstrumentStillMissingIsTrue : exactFinalPart9DecisionInstrumentStillMissing ≡ true
    exact9281ApprovedPlanCarrierLocated : Bool
    exact9281ApprovedPlanCarrierLocatedIsTrue : exact9281ApprovedPlanCarrierLocated ≡ true
    exact9281ApprovedPlanObjectIdKnown : Bool
    exact9281ApprovedPlanObjectIdKnownIsTrue : exact9281ApprovedPlanObjectIdKnown ≡ true
    exact9281ClearingPolygonStillMissing : Bool
    exact9281ClearingPolygonStillMissingIsTrue : exact9281ClearingPolygonStillMissing ≡ true
    relatedStage1to4AWorksCarriersLocated : Bool
    relatedStage1to4AWorksCarriersLocatedIsTrue : relatedStage1to4AWorksCarriersLocated ≡ true
    worksCommencementStillNotProved : Bool
    worksCommencementStillNotProvedIsTrue : worksCommencementStillNotProved ≡ true
    exactParcelCorridorJoinStillMissing : Bool
    exactParcelCorridorJoinStillMissingIsTrue : exactParcelCorridorJoinStillMissing ≡ true
    exactOffsetParcelsStillMissing : Bool
    exactOffsetParcelsStillMissingIsTrue : exactOffsetParcelsStillMissing ≡ true

currentExternalWall : CurrentExternalWall
currentExternalWall = current-external-wall
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl

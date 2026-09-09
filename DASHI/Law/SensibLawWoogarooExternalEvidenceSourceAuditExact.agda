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
-- legal-evidence tranche.  It is deliberately conservative: a useful map,
-- register, metadata record, portal label or submission does not silently
-- become the statutory conclusion sought by a different consumer.
------------------------------------------------------------------------

data EvidenceSourceClass : Set where
  primaryFederalProceduralNotice : EvidenceSourceClass
  primaryFederalPublicCommentInvitation : EvidenceSourceClass
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
  "The uploaded file is a one-page invitation for public comment. It confirms controlled-action status, Preliminary Documentation assessment and ss 18/18A controlling species/community, and points to the Saunders Havill documentation location. It is not itself the Final Preliminary Documentation habitat bundle."
  sourcePaid
  "EPBC project identity / assessment pathway / controlling provisions"
  "recover the actual Preliminary Documentation and final habitat maps/tables/appendices"
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
    finalPDHabitatBundleStillMissing : Bool
    finalPDHabitatBundleStillMissingIsTrue : finalPDHabitatBundleStillMissing ≡ true
    exactParcelCorridorJoinStillMissing : Bool
    exactParcelCorridorJoinStillMissingIsTrue : exactParcelCorridorJoinStillMissing ≡ true
    unverified128HaAndOffsetMetricsMustNotPromote : Bool
    unverified128HaAndOffsetMetricsMustNotPromoteIsTrue : unverified128HaAndOffsetMetricsMustNotPromote ≡ true

currentExternalWall : CurrentExternalWall
currentExternalWall = current-external-wall true refl true refl true refl

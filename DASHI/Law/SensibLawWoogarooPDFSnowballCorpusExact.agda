module DASHI.Law.SensibLawWoogarooPDFSnowballCorpusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WOOGAROO PDF SNOWBALL CORPUS
--
-- This owner records the acquisition discipline for the conversation-scale
-- Woogaroo PDF corpus.  It is deliberately carrier-aware: multiple uploaded
-- PDFs can be duplicates, mirrors, attachments of one referral, or genuinely
-- independent sources.  Carrier count therefore never stands in for source
-- independence or proposition support.
------------------------------------------------------------------------

data SnowballProject : Set where
  epbc20188350 : SnowballProject
  epbc20198575 : SnowballProject
  epbc20208629 : SnowballProject
  epbc20208651 : SnowballProject
  epbc202410082 : SnowballProject
  localPlanning : SnowballProject
  crossProjectLandscape : SnowballProject


data SnowballSourceRole : Set where
  proponentReferral : SnowballSourceRole
  proponentTechnicalAttachment : SnowballSourceRole
  commonwealthDecision : SnowballSourceRole
  stateMapping : SnowballSourceRole
  localPlanningRecord : SnowballSourceRole
  publicCommentNotice : SnowballSourceRole
  campaignOrSubmission : SnowballSourceRole
  sourceOfSourceLead : SnowballSourceRole


data SnowballAtom : Set where
  projectIdentity : SnowballAtom
  lotPlanIdentity : SnowballAtom
  footprint : SnowballAtom
  threatenedSpecies : SnowballAtom
  habitatQuality : SnowballAtom
  koalaUse : SnowballAtom
  corridorConnectivity : SnowballAtom
  remnantStatus : SnowballAtom
  restorationLag : SnowballAtom
  significantResidualImpact : SnowballAtom
  offsetRequirement : SnowballAtom
  localDAIdentity : SnowballAtom
  clearingEntitlement : SnowballAtom
  publicParticipation : SnowballAtom
  cumulativeDevelopment : SnowballAtom
  protectedAreaAdjacency : SnowballAtom

record SnowballCarrierReceipt : Set where
  constructor snowball-carrier-receipt
  field
    carrierLabel : String
    project : SnowballProject
    sourceRole : SnowballSourceRole
    nativeReference : String
    acquisitionReference : String
    boundedReading : String

open SnowballCarrierReceipt public

record SnowballClaimReceipt : Set where
  constructor snowball-claim-receipt
  field
    carrier : SnowballCarrierReceipt
    atom : SnowballAtom
    proposition : String
    attribution : String
    legalConsumer : String
    residual : String

open SnowballClaimReceipt public

------------------------------------------------------------------------
-- Initial cross-project receipts paid by the uploaded corpus.
------------------------------------------------------------------------

bellevueReferral : SnowballCarrierReceipt
bellevueReferral = snowball-carrier-receipt
  "2018-8350 referral.pdf"
  epbc20188350
  proponentReferral
  "EPBC 2018/8350 / Eugene Street Residential Development"
  "uploaded conversation PDF"
  "Primary proponent referral; claims remain attributable to CB Developments / 28 South material rather than Commonwealth findings."

bellevueSurroundingReferrals : SnowballClaimReceipt
bellevueSurroundingReferrals = snowball-claim-receipt
  (snowball-carrier-receipt
    "2018-8350 Attachment 22 - EPBC Referrals in the Surrounding Locality"
    epbc20188350
    proponentTechnicalAttachment
    "28 South Project Ref 2016-022, Attachment 22"
    "uploaded conversation PDF"
    "Map compiled from EPBC Referral Portal 2018 plus cadastral, road and waterway data.")
  cumulativeDevelopment
  "The attachment maps multiple surrounding EPBC-referred developments, including Springview Village One and other residential projects."
  "28 South Environmental attachment / source data identified in attachment legend"
  "EPBC cumulative-impact and landscape-fragmentation discovery"
  "Exact referral IDs and later project continuity must be acquired separately; map adjacency does not establish cumulative legal effect."

peninsulaEcology : SnowballCarrierReceipt
peninsulaEcology = snowball-carrier-receipt
  "2020-8629 7399_EPBC_REFERRAL_PENINSULA_PRECINCT"
  epbc20208629
  proponentTechnicalAttachment
  "7399 Peninsula Precinct Ecological Assessment - MNES"
  "uploaded conversation PDF"
  "Saunders Havill Group technical assessment for Springfield City Group; proponent-side evidence, not agency finding."

peninsulaCorridor : SnowballClaimReceipt
peninsulaCorridor = snowball-claim-receipt
  peninsulaEcology
  corridorConnectivity
  "Opossum Creek is described as a 100-150 m fauna-movement corridor toward the Flinders-Karawatha corridor; the site is described as connected to about 675 ha."
  "Saunders Havill Group"
  "EPBC connectivity / cumulative fragmentation; cross-project landscape comparison"
  "Exact geometry and relation to Springview/Scenic/Bellevue must be spatially joined rather than inferred from names alone."

peninsulaResidualImpact : SnowballClaimReceipt
peninsulaResidualImpact = snowball-claim-receipt
  peninsulaEcology
  significantResidualImpact
  "The ecological assessment identifies a significant residual impact on 17.08 ha of critical koala habitat, scored 7/10, and 17.08 ha of Grey-headed Flying-fox foraging habitat."
  "Saunders Havill Group"
  "EPBC significant-impact / offset consumer"
  "Later Preliminary Documentation and Commonwealth decision record may refine or supersede the referral-stage assessment."

peninsulaOffset : SnowballClaimReceipt
peninsulaOffset = snowball-claim-receipt
  peninsulaEcology
  offsetRequirement
  "The assessment states an EPBC environmental offset is necessary and should compensate for 100 percent of the identified impact."
  "Saunders Havill Group"
  "EPBC offset adequacy comparison"
  "This does not source-pay the exact eventual offset parcel, calculator assumptions, legal security or Commonwealth acceptance."

abadiDecision : SnowballCarrierReceipt
abadiDecision = snowball-carrier-receipt
  "2024-10082 Referral Decision / Assessment Approach"
  epbc202410082
  commonwealthDecision
  "EPBC 2024/10082 Abadi Gaia Adult Residential Village, Goodna"
  "uploaded conversation PDF"
  "Commonwealth controlled-action and assessment-approach decision."

------------------------------------------------------------------------
-- Snowball firewalls.
------------------------------------------------------------------------

data DuplicateCarrierCreatesIndependentCorroboration : Set where

data AttachmentReferenceAutomaticallyPaysReferencedSource : Set where

data ProjectAEvidenceAutomaticallyPaysProjectB : Set where

data ProponentTechnicalClaimIsCommonwealthFinding : Set where

data SameLandscapeAutomaticallyMeansSamePolygon : Set where

data SourceCountAutomaticallyMeansEvidenceWeight : Set where

data SnowballDiscoveryAutomaticallyPaysLegalElement : Set where

noDuplicatePromotion : DuplicateCarrierCreatesIndependentCorroboration → ⊥
noDuplicatePromotion ()

noSourceOfSourcePromotion : AttachmentReferenceAutomaticallyPaysReferencedSource → ⊥
noSourceOfSourcePromotion ()

noCrossProjectPromotion : ProjectAEvidenceAutomaticallyPaysProjectB → ⊥
noCrossProjectPromotion ()

noProponentAgencyCollapse : ProponentTechnicalClaimIsCommonwealthFinding → ⊥
noProponentAgencyCollapse ()

noLandscapePolygonCollapse : SameLandscapeAutomaticallyMeansSamePolygon → ⊥
noLandscapePolygonCollapse ()

noCountWeightCollapse : SourceCountAutomaticallyMeansEvidenceWeight → ⊥
noCountWeightCollapse ()

noDiscoveryLegalPaymentCollapse : SnowballDiscoveryAutomaticallyPaysLegalElement → ⊥
noDiscoveryLegalPaymentCollapse ()

record PDFSnowballPolicy : Set where
  constructor pdf-snowball-policy
  field
    preserveNativeCarrier : Bool
    preserveProjectIndex : Bool
    preserveSourceRole : Bool
    preserveAttribution : Bool
    followSourceOfSourceEdges : Bool
    deduplicateBeforeCorroboration : Bool
    allowOutOfDependencyOrderAcquisition : Bool
    requireExactConsumerPayment : Bool

canonicalPDFSnowballPolicy : PDFSnowballPolicy
canonicalPDFSnowballPolicy = pdf-snowball-policy
  true true true true true true true true

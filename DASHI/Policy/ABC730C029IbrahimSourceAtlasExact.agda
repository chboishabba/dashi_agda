module DASHI.Policy.ABC730C029IbrahimSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Policy.ABC730IbrahimSnowballAttributionExact as ABC
import DASHI.Policy.ABC730UnintendedConsequencesSnowballEvidenceExact as UK
import DASHI.Policy.ABC730PalestinianIncidenceSnowballExact as Palestine
import DASHI.Policy.ABC730AustralianImplementationSnowballExact as Australia
import DASHI.Policy.ABC730AustralianOriginBaselineExact as Origin
import DASHI.Policy.ABC730SettlementTradeMeasurementGapExact as Measurement
import DASHI.Policy.ABC730FirmDestinationExposureSnowballExact as Firms

------------------------------------------------------------------------
-- Single Ibrahim/Snowball atlas for the C029 evidence chain.
--
-- Each coordinate keeps these independent:
--   * source object and canonical link,
--   * claim-relative primary/secondary role,
--   * Dewey retrieval coordinate,
--   * QID identity coordinate,
--   * DOI or stable non-DOI identifier,
--   * downstream claim-payment scope.
-- Missing identifiers remain unresolved rather than inferred.
------------------------------------------------------------------------

data QidPayment : Set where
  qidPaid : String → QidPayment
  qidUnresolved : String → QidPayment

data StableIdKind : Set where
  doiId : String → StableIdKind
  urlObjectId : String → StableIdKind
  documentSymbolId : String → StableIdKind
  datasetId : String → StableIdKind

data ClaimRelativeRole : Set where
  primaryForUtterance : ClaimRelativeRole
  primaryForPolicyInstrument : ClaimRelativeRole
  primaryForImplementationGuidance : ClaimRelativeRole
  primaryForOfficialStatistic : ClaimRelativeRole
  primaryForDatasetStructure : ClaimRelativeRole
  primaryForBusinessUniverse : ClaimRelativeRole
  primaryForRegulatoryBaseline : ClaimRelativeRole
  secondaryForMechanismContext : ClaimRelativeRole
  secondaryForMeasurementSynthesis : ClaimRelativeRole
  unresolvedRole : ClaimRelativeRole

data PaymentScope : Set where
  paysSpeakerAndWording : PaymentScope
  paysStatedRationale : PaymentScope
  paysInstrumentIdentity : PaymentScope
  paysOriginDifferentiationMechanism : PaymentScope
  paysTargetedAlternativeIdentity : PaymentScope
  paysExistingComplianceBurden : PaymentScope
  paysCountryOriginBaseline : PaymentScope
  paysPalestinianWorkerExposure : PaymentScope
  paysStructuralLabourContext : PaymentScope
  paysSettlementBusinessCandidates : PaymentScope
  paysMeasurementLimitation : PaymentScope
  paysNothingBeyondAcquisition : PaymentScope

record SnowballSourceCoordinate : Set where
  constructor snowballSourceCoordinate
  field
    coordinateId : String
    source : Source.AttributedSource
    canonicalLink : String
    role : ClaimRelativeRole
    deweyParent : String
    qid : QidPayment
    stableId : StableIdKind
    claimReference : String
    paymentScope : PaymentScope
    paymentBoundary : String
    primaryRoleCreatesWorldTruth : Bool
    qidCreatesClaimTruth : Bool
    deweyCreatesClaimTruth : Bool
    linkCreatesClaimTruth : Bool

open SnowballSourceCoordinate public

abcTranscriptCoordinate : SnowballSourceCoordinate
abcTranscriptCoordinate = snowballSourceCoordinate
  "C029-atlas:abc-primary-transcript"
  ABC.abcAttributedSource
  "https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268"
  primaryForUtterance
  "327"
  (qidPaid "Q4642897")
  (urlObjectId "abc730-2026-09-09:61c86754d9cb2ca6e540d522ebfa8056a42291afa257dd6c7e54f12374408383")
  "C028-C033"
  paysSpeakerAndWording
  "primary for labelled transcript wording/stated positions; not causal truth"
  false false false false

ukOriginCoordinate : SnowballSourceCoordinate
ukOriginCoordinate = snowballSourceCoordinate
  "C029-atlas:uk-origin-guidance"
  UK.ukSettlementOriginNoticeSource
  "https://www.gov.uk/government/publications/notice-to-importers-treatment-of-goods-from-israeli-settlements/notice-to-importers-imports-from-israel-into-the-united-kingdom"
  primaryForImplementationGuidance
  "382.7"
  (qidUnresolved "document/institution QID not paid in this atlas")
  (urlObjectId "govuk:notice-to-importers-israel-settlements:updated-2025-08-22")
  "C029 implementation mechanism comparator"
  paysOriginDifferentiationMechanism
  "pays existence of UK settlement-origin differentiation; not Australian cost/effect"
  false false false false

pcbsWorkersCoordinate : SnowballSourceCoordinate
pcbsWorkersCoordinate = snowballSourceCoordinate
  "C029-atlas:pcbs-workers"
  Palestine.pcbsQ4Source
  "https://pcbs.gov.ps/en/post-details/?postId=23457"
  primaryForOfficialStatistic
  "331"
  (qidPaid "Q2895680")
  (urlObjectId "PCBS:Q4-2025:postId-23457")
  "C029 Palestinians affected-class mechanism"
  paysPalestinianWorkerExposure
  "pays settlement-employment exposure population; not ban effect sign"
  false false false false

pcbsMicrodataCoordinate : SnowballSourceCoordinate
pcbsMicrodataCoordinate = snowballSourceCoordinate
  "C029-atlas:pcbs-lfs-microdata"
  Palestine.pcbsMicrodataSource
  "https://microdata.pcbs.gov.ps/PCBS-Metadata-en-v5.2/index.php/catalog/746"
  primaryForDatasetStructure
  "331"
  (qidPaid "Q2895680")
  (datasetId "PSE-PCBS-LFS-2025-V1.0")
  "C029 Palestinian incidence decomposition"
  paysNothingBeyondAcquisition
  "pays existence/shape of a microdata carrier; analysis outputs remain unpaid"
  false false false false

maharmehCoordinate : SnowballSourceCoordinate
maharmehCoordinate = snowballSourceCoordinate
  "C029-atlas:maharmeh-labour"
  Palestine.maharmeh2026Source
  "https://doi.org/10.1080/2158379X.2025.2612489"
  secondaryForMechanismContext
  "331"
  (qidUnresolved "article/person QID not required for mechanism payment")
  (doiId "10.1080/2158379X.2025.2612489")
  "C029 Palestinian labour dependence context"
  paysStructuralLabourContext
  "qualitative/structural mechanism context only; no 2026 policy counterfactual"
  false false false false

hacklCoordinate : SnowballSourceCoordinate
hacklCoordinate = snowballSourceCoordinate
  "C029-atlas:hackl-labour"
  Palestine.hackl2022Source
  "https://doi.org/10.1080/2201473X.2022.2032545"
  secondaryForMechanismContext
  "331"
  (qidUnresolved "article/person QID not required for mechanism payment")
  (doiId "10.1080/2201473X.2022.2032545")
  "C029 Palestinian labour incorporation context"
  paysStructuralLabourContext
  "structural context only; predates policy and does not estimate effect"
  false false false false

wongRationaleCoordinate : SnowballSourceCoordinate
wongRationaleCoordinate = snowballSourceCoordinate
  "C029-atlas:wong-rationale"
  Australia.wongSenateSource
  "https://www.foreignminister.gov.au/minister/penny-wong/speech/palestine-speech-senate"
  primaryForUtterance
  "327"
  (qidPaid "Q456759")
  (urlObjectId "foreignminister:palestine-speech-senate:2026-09-08")
  "C029"
  paysStatedRationale
  "pays what rationale was publicly stated; not mechanism/materiality/probability"
  false false false false

dfatConsolidatedListCoordinate : SnowballSourceCoordinate
dfatConsolidatedListCoordinate = snowballSourceCoordinate
  "C029-atlas:dfat-consolidated-list"
  Australia.consolidatedListSource
  "https://www.dfat.gov.au/international-relations/security/sanctions/consolidated-list"
  primaryForImplementationGuidance
  "382.7"
  (qidUnresolved "DFAT QID not confidently paid; source identity is URL/institution label")
  (urlObjectId "DFAT-ASO:consolidated-list:2026-09-08")
  "C029 targeted alternative"
  paysExistingComplianceBurden
  "pays named-entity due-diligence mechanism; not origin-classification equivalence"
  false false false false

abfDeclarationCoordinate : SnowballSourceCoordinate
abfDeclarationCoordinate = snowballSourceCoordinate
  "C029-atlas:abf-import-declaration"
  Origin.abfImportDeclarationSource
  "https://www.abf.gov.au/imports/Pages/How-to-import/Import-declarations.aspx"
  primaryForRegulatoryBaseline
  "382.7"
  (qidPaid "Q17000879")
  (urlObjectId "abf:import-declarations:2026")
  "C029 Australian implementation baseline"
  paysCountryOriginBaseline
  "pays existing import-declaration infrastructure only"
  false false false false

abfOriginAdviceCoordinate : SnowballSourceCoordinate
abfOriginAdviceCoordinate = snowballSourceCoordinate
  "C029-atlas:abf-origin-advice"
  Origin.abfOriginAdviceSource
  "https://www.abf.gov.au/importing-exporting-and-manufacturing/fta/origin-advice"
  primaryForRegulatoryBaseline
  "382.7"
  (qidPaid "Q17000879")
  (urlObjectId "abf:origin-advice:2026")
  "C029 Australian implementation baseline"
  paysCountryOriginBaseline
  "pays existence of origin adjudication; settlement-place rule remains unpaid"
  false false false false

acccOriginCoordinate : SnowballSourceCoordinate
acccOriginCoordinate = snowballSourceCoordinate
  "C029-atlas:accc-origin-labelling"
  Origin.acccOriginSource
  "https://www.accc.gov.au/business/advertising-and-promotions/country-of-origin-food-labelling"
  primaryForRegulatoryBaseline
  "381.3"
  (qidPaid "Q4056089")
  (urlObjectId "accc:country-origin-food-labelling:2026")
  "C029 Australian implementation baseline"
  paysCountryOriginBaseline
  "pays country-level retail food origin labelling; not settlement-place classification"
  false false false false

ohchrBusinessCoordinate : SnowballSourceCoordinate
ohchrBusinessCoordinate = snowballSourceCoordinate
  "C029-atlas:ohchr-business-database"
  Firms.ohchrBusinessDatabaseSource
  "https://www.ohchr.org/en/press-releases/2026/09/un-human-rights-office-updates-database-business-enterprises-involved-certain"
  primaryForBusinessUniverse
  "338.8"
  (qidPaid "Q656812")
  (documentSymbolId "OHCHR:settlement-business-database:2026")
  "C029 firm/destination exposure candidates"
  paysSettlementBusinessCandidates
  "pays candidate firm/activity universe; not destination/export/worker linkage"
  false false false false

ukMeasurementCoordinate : SnowballSourceCoordinate
ukMeasurementCoordinate = snowballSourceCoordinate
  "C029-atlas:uk-settlement-measurement-gap"
  Measurement.ukParliament2025Source
  "https://questions-statements.parliament.uk/written-questions/detail/2025-04-17/45543/"
  primaryForImplementationGuidance
  "382.7"
  (qidUnresolved "document QID not paid")
  (documentSymbolId "UKParliament:written-question:45543:2025-04-24")
  "C029 settlement trade magnitude"
  paysMeasurementLimitation
  "pays non-identifiability in ordinary published partner-country aggregates"
  false false false false

allC029SourceCoordinates : List SnowballSourceCoordinate
allC029SourceCoordinates =
  abcTranscriptCoordinate ∷ ukOriginCoordinate ∷ pcbsWorkersCoordinate ∷
  pcbsMicrodataCoordinate ∷ maharmehCoordinate ∷ hacklCoordinate ∷
  wongRationaleCoordinate ∷ dfatConsolidatedListCoordinate ∷
  abfDeclarationCoordinate ∷ abfOriginAdviceCoordinate ∷ acccOriginCoordinate ∷
  ohchrBusinessCoordinate ∷ ukMeasurementCoordinate ∷ []

------------------------------------------------------------------------
-- Ibrahim graph surface.
------------------------------------------------------------------------

c029Node : Ibrahim.DashiKnowledgeCoordinate
c029Node = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Policy/ABC730UnintendedConsequencesEvidenceObligationExact.agda"
  "DASHI.Policy.ABC730UnintendedConsequencesEvidenceObligationExact"
  "327"
  "Q456759"
  "ABC730-2026-09-09-C029"

originBaselineNode : Ibrahim.DashiKnowledgeCoordinate
originBaselineNode = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Policy/ABC730AustralianOriginBaselineExact.agda"
  "DASHI.Policy.ABC730AustralianOriginBaselineExact"
  "382.7"
  "Q17000879"
  "ABF+ACCC-origin-baseline"

originBaselineSupportsC029 : Ibrahim.DashiFirstLinkEdge
originBaselineSupportsC029 = Ibrahim.dashi-first-link-edge
  c029Node originBaselineNode Ibrahim.supportedBy Ibrahim.canonicalDashiFirstLinkPolicy
  "Australian origin/compliance infrastructure pays the baseline capability comparison, while settlement-specific fields/costs remain residual."
  true

record AtlasBoundary : Set where
  constructor atlasBoundary
  field
    acquisitionMayFollowLinks : Bool
    missingDoiMayBeInvented : Bool
    unresolvedQidMayBeGuessed : Bool
    deweyAdjacencyPaysClaim : Bool
    canonicalLinkPaysClaim : Bool
    primaryRolePaysBeyondRole : Bool
    laterSourceMayRewriteEarlierSourceState : Bool
    paymentMustRespectClaimScope : Bool

canonicalAtlasBoundary : AtlasBoundary
canonicalAtlasBoundary = atlasBoundary true false false false false false false true

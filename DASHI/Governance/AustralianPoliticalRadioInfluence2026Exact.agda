module DASHI.Governance.AustralianPoliticalRadioInfluence2026Exact where

-- Source-bounded second/third-order case, 24 October 2026.
-- Source authors own facts and accounts; DASHI owns only the distinct
-- relationship types and formal nonpromotion. No agency or intent is inferred
-- from reachability of a political-media graph.
open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.TypedGenealogyEdgeExact as Typed
import DASHI.Governance.BOMFordhamMediaClaimAuditExact as BOM

data PoliticalRelation : Set where
  broadcasterOwnership : PoliticalRelation
  legalOperatorRegistration : PoliticalRelation
  historicEquityHolding : PoliticalRelation
  productionSupply : PoliticalRelation
  announcedStrategicPartnership : PoliticalRelation
  proposedUncompletedAcquisition : PoliticalRelation
  audiencePrepaymentSelfReport : PoliticalRelation
  prospectiveSponsorOffer : PoliticalRelation
  externalPlatformSupplier : PoliticalRelation
  financialEntitlement : PoliticalRelation
  securedStakeFinancing : PoliticalRelation
  reportedUnverifiedFunding : PoliticalRelation
  mediaRedistribution : PoliticalRelation
  reportedMeeting : PoliticalRelation
  publishedCorrespondence : PoliticalRelation
  politicalDonation : PoliticalRelation
  inKindTransportSupport : PoliticalRelation
  policyConsultation : PoliticalRelation
  selfReportedMessagingHelp : PoliticalRelation
  spokespersonQualifiedRelationship : PoliticalRelation
  professionalAffiliation : PoliticalRelation
  conferenceCoAttendance : PoliticalRelation
  editorialPublication : PoliticalRelation
  enforcementFinding : PoliticalRelation
  disputedAuthorshipClaim : PoliticalRelation

data SourceStatus : Set where
  institutionRecord : SourceStatus
  journalistCorroboration : SourceStatus
  namedActorSelfReport : SourceStatus
  namedActorDenial : SourceStatus
  regulatoryDetermination : SourceStatus
  disputedDocumentClaim : SourceStatus

record RelationshipReceipt : Set where
  constructor relationship-receipt
  field
    origin : String
    target : String
    kind : PoliticalRelation
    evidence : SourceStatus
    title : String
    locator : String
    boundedDescription : String
    provesEditorialControl : Bool
    provesHiddenCoordination : Bool
    provesPolicyCausation : Bool
open RelationshipReceipt public

-- Actual radio owner, 2026: 2GB sold from Nine to Tapt; unrelated to
-- KIIS's owner ARN. Historical ownership cannot be projected forward.
fordhamTapt : RelationshipReceipt
fordhamTapt = relationship-receipt
  "2GB" "Tapt Media / Laundy Family Office"
  broadcasterOwnership institutionRecord
  "Tapt Media launch, 1 May 2026"
  "https://taptmedia.com.au/tapt-media-launches-as-australias-premier-independent-audio-powerhouse/"
  "2GB/3AW/4BC/6PR ownership transferred from Nine to Laundy Family Office. Ex-Liberal MP Craig Laundy is Arthur Laundy's son, not evidence of editorial orders." false false false

-- The legal operator, shareholder and distribution financier are
-- separate concepts. ABR confirms an entity but does NOT publish its
-- private member register or ultimate beneficial owner.
newShowLegalOperator : RelationshipReceipt
newShowLegalOperator = relationship-receipt
  "Kyle Sandilands Live programme" "Kyle Sandilands Live Pty Ltd (ABN 24 699 610 261)"
  legalOperatorRegistration institutionRecord
  "Australian Business Register, active since 29 June 2026"
  "https://abr.business.gov.au/ABN/View?id=24699610261"
  "Public ABR register confirms company identity, active date and GST status; no current shareholding extract available from this source." false false false

sandilandsSelfReportedOwnership : RelationshipReceipt
sandilandsSelfReportedOwnership = relationship-receipt
  "Kyle Sandilands" "Kyle Sandilands Live business"
  broadcasterOwnership namedActorSelfReport
  "RadioInfo first-person interview, August 2026"
  "https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/"
  "Kyle said interested billionaires approached but team chose to keep ownership; Guardian independently described his stake as 100 percent as of August 7. ASIC member register not obtained; this does not license naming secret investors." false false false

aiimsProduction : RelationshipReceipt
aiimsProduction = relationship-receipt
  "AIIMS Creator Hub" "At Home With Kyle / Kyle Sandilands Live"
  productionSupply institutionRecord
  "AIIMS Creator Hub direct production announcement, 24 July 2026"
  "https://aiims.group/aiims-creator-hub-kyle-sandilands-live/"
  "AIIMS says it filmed, directed and produced At Home With Kyle. A paid contractor or co-production role is not a disclosed equity investment." false false false

nineTaptStrategicPartnership : RelationshipReceipt
nineTaptStrategicPartnership = relationship-receipt
  "Nine Entertainment" "Laundy Family Office / Tapt Media"
  announcedStrategicPartnership institutionRecord
  "Nine January 2026 radio divestiture statement"
  "https://newmedia.com.au/nine-announces-sale-of-radio-assets/"
  "Despite divestiture, parties announced continuing 9News radio journalism, ad-sales, marketing, Stan Sport and pub promotion collaborations. Not proof Nine still owns Tapt." false false false

kyleProposedARNBuyout : RelationshipReceipt
kyleProposedARNBuyout = relationship-receipt
  "Kyle Sandilands" "Proposed ARN takeover / $90m outside capital"
  proposedUncompletedAcquisition journalistCorroboration
  "News.com.au reported April 2026 take-private concept"
  "https://www.news.com.au/entertainment/tv/radio/kyle-sandilands-plots-arn-takeover-but-still-needs-90-million-investor/news-story/ee29d7ba21ef87a7af1cbfb7987f07a5"
  "Reported proposal sought about AUD 90m in investors plus AUD 10m personal contribution, with Laundy discussions/speculation. No identified committed external backer or completed ARN acquisition." false false false

-- 2025 annual report, register date 3 February 2026; historic
-- shares should not be carried as a current ownership percentage without
-- new substantial holder notices / revised registry extracts.
quasarARNHistoricalEquity : RelationshipReceipt
quasarARNHistoricalEquity = relationship-receipt
  "Quasar Media Services Pty Ltd" "ARN Media Limited"
  historicEquityHolding institutionRecord
  "ARN Media 2025 annual report, share register 3 February 2026"
  "https://financialfilings.com/filings/arn-media-limited/annual-report/2026/37381126/"
  "ARN's published top-twenty register lists 3,161,166 Quasar shares (1.01%). ARN's 18 March company announcement separately says Quasar was Sandilands' broadcaster service contractor; ownership, custody, beneficial control, vesting and subsequent disposition require share-ledger/contract detail." false false false

quasarKyleService : RelationshipReceipt
quasarKyleService = relationship-receipt
  "Quasar Media Services Pty Ltd" "Kyle Sandilands / ARN broadcaster services"
  productionSupply institutionRecord
  "ARN first-party termination of contract with Quasar Media, 18 March 2026"
  "https://arn.com.au/market-announcement-termination-of-contract-with-quasar-media-and-mr-sandilands/"
  "ARN says Quasar provided contracted broadcasting services for Kyle. The service relationship ends March 2026; existence of old ARN shares does not establish continued control or a KSL investment." false false false

hendersonARNHistoricalEquity : RelationshipReceipt
hendersonARNHistoricalEquity = relationship-receipt
  "Henderson Media Pty Ltd" "ARN Media Limited"
  historicEquityHolding institutionRecord
  "ARN 2025 annual report 3 February 2026"
  "https://financialfilings.com/filings/arn-media-limited/annual-report/2026/37381126/"
  "Top-twenty register lists 3,161,166 shares (1.01%) for Henderson Media, former Jackie O service counterparty. This is not a share in KSL and not automatically her personal beneficial ownership." false false false

southernCrossARNIndirect : RelationshipReceipt
southernCrossARNIndirect = relationship-receipt
  "Southern Cross Media Group (after Seven West merger)" "ARN Media"
  historicEquityHolding institutionRecord
  "ACMA Media Interests snapshot, February 2026"
  "https://www.acma.gov.au/updates-media-interests-snapshot"
  "ACMA records Southern Cross acquired 14.54% ARN through Jan 2026 Seven West merger; distinct from a station licence transfer, and does not prove Southern Cross or Kerry Stokes directs Kyle's new platform." false false false

stokesSouthernCrossStake : RelationshipReceipt
stokesSouthernCrossStake = relationship-receipt
  "SGH / Kerry Stokes" "Southern Cross Media Group"
  historicEquityHolding institutionRecord
  "ACMA Media Interests snapshot, February 2026"
  "https://www.acma.gov.au/updates-media-interests-snapshot"
  "ACMA attributes approximately 20.06% Southern Cross interest to SGH and Kerry Stokes after merger. Path to ARN is two distinct equity edges, not a claim of controlling every radio presenter." false false false

stokesSouthernCrossSeptemberUpdate : RelationshipReceipt
stokesSouthernCrossSeptemberUpdate = relationship-receipt
  "SGH Ltd / Kerry Stokes" "Southern Cross Media Group"
  historicEquityHolding institutionRecord
  "ACMA media interests update, 11 September 2026"
  "https://www.acma.gov.au/updates-media-interests-snapshot"
  "ACMA upgraded the stated SGH/Southern Cross interest from 20.06 percent to 23.19 percent in September; this is a dated revision of the February snapshot, NOT a second independent holding to sum." false false false

kiisARN : RelationshipReceipt
kiisARN = relationship-receipt
  "KIIS 106.5" "ARN Media"
  broadcasterOwnership institutionRecord
  "ARN Media 2025 Annual Report, issued 31 March 2026"
  "https://investors.arn.com.au/announcements/gao5Z3-annual-report-2025"
  "ARN owned KIIS when Kyle and Jackie O hosted; presenter contract ended in March 2026, so this is no longer Kyle's direct employment relationship." false false false

arnSandilandsRevenue : RelationshipReceipt
arnSandilandsRevenue = relationship-receipt
  "ARN Media" "Kyle Sandilands Live"
  financialEntitlement institutionRecord
  "ARN Media ASX announcement, 17 June 2026"
  ""https://www.marketindex.com.au/asx/a1n/announcements/settlement-of-legal-proceedings-with-mr-sandilands-2A1677721"
  "ARN's 17 June ASX original notice grants a 19.9% share of NET revenue for at most 3 years, subject to agreed thresholds/caps, in return for AUD 1.5m promotional advertising; not an equity share, with noncompete to March 2027 and AUD 12.09m settlement." false false false

arnNewsCorpExit : RelationshipReceipt
arnNewsCorpExit = relationship-receipt
  "News Corp Australia" "ARN Media"
  broadcasterOwnership institutionRecord
  "ACMA updates to Media Interests, December 2025"
  "https://www.acma.gov.au/updates-media-interests-snapshot"
  "ACMA records News Corp ceased substantial-holder status December 2025. ARN annual report nevertheless lists 43.7m News shares on its 3 February 2026 substantial-holder notice table; the incompatible dates/notices demand reconciliation, not categorical assertion of zero beneficial shares." false false false

hancockAdvance : RelationshipReceipt
hancockAdvance = relationship-receipt
  "Hancock Prospecting / Gina Rinehart" "Advance Australia"
  politicalDonation journalistCorroboration
  "SBS 2026-02 election-disclosures overview"
  "https://www.sbs.com.au/news/article/political-donations-2025-federal-election-leadup/pi0lbzm5h"
  "AEC-derived receipts report 895000 AUD in 2024-25 donations to Advance. Funding organisation does not establish direction of one speaker at one later conference." false false false

advanceBannonAssociate : RelationshipReceipt
advanceBannonAssociate = relationship-receipt
  "Advance Australia 2026 conference" "Benjamin Harnwell"
  conferenceCoAttendance journalistCorroboration
  "ABC News 2026-02-23 leaked-recording report"
  "https://www.abc.net.au/news/2026-02-23/advance-lobby-group-conference-centre-right-mass-immigration/106371720"
  "Bannon War Room international editor Harnwell spoke at Advance event; Abbott, Price and Antic also participated. This is verified professional affiliation and event participation, not Bannon-authored instruction to those MPs." false false false

harnwellBannon : RelationshipReceipt
harnwellBannon = relationship-receipt
  "Benjamin Harnwell" "Steve Bannon War Room podcast"
  professionalAffiliation journalistCorroboration
  "ABC News 2026-02-23"
  "https://www.abc.net.au/news/2026-02-23/advance-lobby-group-conference-centre-right-mass-immigration/106371720"
  "ABC identifies Harnwell as War Room international editor. Does not imply that Bannon commissioned a specific Advance speech." false false false

rinehartOneNationTransport : RelationshipReceipt
rinehartOneNationTransport = relationship-receipt
  "Rinehart company" "One Nation"
  inKindTransportSupport journalistCorroboration
  "ABC News 2026-04-29 plane handover"
  "https://www.abc.net.au/news/2026-04-29/gina-rinehart-gifts-plane-to-pauline-hanson-one-nation/106620808"
  "Hancock spokesperson acknowledged aircraft donation; first party-owned plane for One Nation campaign travel. Value reported above 1m AUD." false false false

rinehartHansonPolicy : RelationshipReceipt
rinehartHansonPolicy = relationship-receipt
  "Gina Rinehart" "Pauline Hanson"
  policyConsultation namedActorSelfReport
  "ABC News 2026-06-11 interview with Hanson"
  "https://www.abc.net.au/news/2026-06-11/one-nation-pauline-hanson-gina-rinehart/106787540"
  "Hanson explicitly attributes her pensioner-work-hours policy idea to Rinehart. This is a bounded first-person policy input, not a global policy-capture finding." false false false

plimerOneNation : RelationshipReceipt
plimerOneNation = relationship-receipt
  "Ian Plimer / Hancock Energy executive" "One Nation"
  politicalDonation journalistCorroboration
  "ABC News 2026-04-29"
  "https://www.abc.net.au/news/2026-04-29/gina-rinehart-gifts-plane-to-pauline-hanson-one-nation/106620808"
  "Plimer individually donated 500000 AUD; employed as Hancock Energy executive. These links do not prove Rinehart funded his donation or endorsed each climate assertion." false false false

kyleHansonMessaging : RelationshipReceipt
kyleHansonMessaging = relationship-receipt
  "Kyle Sandilands" "Pauline Hanson / One Nation camp"
  selfReportedMessagingHelp namedActorSelfReport
  "Game Changers Radio June 2026; ABC report 2026-06-19"
  "https://www.abc.net.au/news/2026-06-19/kyle-sandilands-new-show-after-arn-radio-contract-settlement/106815596"
  "Sandilands says he spent days with Hanson camp working on getting its messaging across. One Nation's James Ashby contested employment/capacity characterisation; exact employment and campaign deliverables unresolved." false false false

ashbyKyleQualification : RelationshipReceipt
ashbyKyleQualification = relationship-receipt
  "James Ashby / One Nation" "Kyle Sandilands"
  spokespersonQualifiedRelationship namedActorDenial
  "ABC report 2026-06-19, citing Ashby SMH statement"
  "https://www.abc.net.au/news/2026-06-19/kyle-sandilands-new-show-after-arn-radio-contract-settlement/106815596"
  "Ashby denied Kyle was working for One Nation formally or informally. A denial of employment does not logically negate brief social or informal advice described by Kyle." false false false

acmaMpoxFinding : RelationshipReceipt
acmaMpoxFinding = relationship-receipt
  "ACMA" "Kyle and Jackie O show / Sandilands"
  enforcementFinding regulatoryDetermination
  "ACMA 2023-08-10 mpox broadcasting ruling"
  "https://www.acma.gov.au/articles/2023-08/kiis-1065-mpox-comments-breach-decency-standards"
  "ACMA found 2022 mpox segment breach for disparaging stereotyping of gay men. This is a regulator determination, not an allegation or a general adjudication of political speech." false false false

acmaParalympicsFinding : RelationshipReceipt
acmaParalympicsFinding = relationship-receipt
  "ACMA" "Kyle and Jackie O show / Sandilands"
  enforcementFinding regulatoryDetermination
  "ACMA 2023-03-28 Paralympics broadcasts ruling"
  "https://www.acma.gov.au/articles/2023-03/kiis-1065-paralympics-comments-breach-decency-standards"
  "ACMA found decency breaches for disparaging Paralympic athletes and threats to a journalist in separate segment. These are distinct agency findings." false false false

-- Do not re-encode this source receipt here. PR #1131 already owns
-- EFTA01615861, the Bannon claim, direct phone-contact acknowledgement
-- and Palmer's denial, plus separate SMS/advertising deployment evidence.
-- Its unmerged source module remains an external cross-branch owner and is
-- deliberately not imported into this master-based case.
bannonPalmerCanonicalOwner : String
bannonPalmerCanonicalOwner =
  "PR#1131:DASHI/Cognition/BannonFaragePalmerAutomatedInfluenceReceiptsExact.agda#bannonPalmerReceipt"

bannonPalmerCanonicalDocument : String
bannonPalmerCanonicalDocument = "US DOJ EFTA01615861"

-- RadioInfo's original 28 July 2026 interview is a first-person
-- business-model disclosure, NOT a payment ledger or an independent audit.
kyleSubscriberFinanceSelfReport : RelationshipReceipt
kyleSubscriberFinanceSelfReport = relationship-receipt
  "Kyle Sandilands Live prospective subscribers" "Kyle Sandilands Live"
  audiencePrepaymentSelfReport namedActorSelfReport
  "Steve Ahern / RadioInfo, 2026-07-28: interview with Kyle Sandilands"
  "https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/"
  "Kyle reports tens of thousands of prepaid annual subscriptions, close to AUD 2m gross and enough to cover projected costs about 2.5 years. No independent subscriber ledger, refunds, retention or bank reconciliation was provided." false false false

harveyNormanProspectiveSponsorship : RelationshipReceipt
harveyNormanProspectiveSponsorship = relationship-receipt
  "Harvey Norman (as described by Kyle)" "Kyle Sandilands Live promotional prizes"
  prospectiveSponsorOffer namedActorSelfReport
  "Steve Ahern / RadioInfo, 2026-07-28"
  "https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/"
  "Kyle says Harvey Norman conveyed general willingness to help and that EV companies proposed prizes. This is an attributed approach, not verified provision, signed sponsorship or equity investment." false false false

kyleUscreenPlatform : RelationshipReceipt
kyleUscreenPlatform = relationship-receipt
  "Uscreen" "Kyle Sandilands Live app/video distribution"
  externalPlatformSupplier namedActorSelfReport
  "Steve Ahern / RadioInfo, 2026-07-28"
  "https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/"
  "Original reporter says KSL will use Uscreen.tv for multiscreen subscriber delivery. Platform/software supplier is not an identified shareholder or controller of editorial content." false false false

-- Financial categories remain orthogonal: prepaid audience revenue, a
-- contingent commercial offer, an ARN contractual share of net receipts,
-- inherited ARN equity and capital subscription in KSL.
data SubscriptionSelfReportEstablishesAuditedReceipts : Set where
data BrandOfferEstablishesEquityInvestment : Set where

reportedSubscriptionsNotAudited :
  SubscriptionSelfReportEstablishesAuditedReceipts → ⊥
reportedSubscriptionsNotAudited ()

advertiserOfferNotEquity :
  BrandOfferEstablishesEquityInvestment → ⊥
advertiserOfferNotEquity ()

-- Specifically ban transitive leaps of type funding→speaker→campaign
-- or access→ideology→editorial control. No self-reports are silently
-- promoted to an established contract.
data FundingImpliesEditorialControl : Set where
data SharedConferenceImpliesBannonCommand : Set where
data MessagingSelfReportImpliesPaidContract : Set where
data SimilarClimateFramingImpliesFordhamDirection : Set where
data RinehartRelationImpliesEntireOneNationPolicyCapture : Set where
data MediaRevenueShareImpliesEditorialOrders : Set where

noFundToEditorialLeap : FundingImpliesEditorialControl → ⊥
noFundToEditorialLeap ()
noCoattendanceCommandLeap : SharedConferenceImpliesBannonCommand → ⊥
noCoattendanceCommandLeap ()
noEmploymentLeap : MessagingSelfReportImpliesPaidContract → ⊥
noEmploymentLeap ()
noFordhamCommandLeap : SimilarClimateFramingImpliesFordhamDirection → ⊥
noFordhamCommandLeap ()
noUniversalPolicyCaptureLeap : RinehartRelationImpliesEntireOneNationPolicyCapture → ⊥
noUniversalPolicyCaptureLeap ()
noRevenueControlLeap : MediaRevenueShareImpliesEditorialOrders → ⊥
noRevenueControlLeap ()

-- Candidate indirect influences, not exact causation.
data IndirectEffect : Set where
  broadcasterAudienceFraming : IndirectEffect
  donorAgendaAccess : IndirectEffect
  socialMediaDistribution : IndirectEffect
  policyInformationPipeline : IndirectEffect
  institutionalTrustImpact : IndirectEffect
  fundingForFutureIndependentMedia : IndirectEffect

record BoundedEffectQuestion : Set where
  constructor bounded-effect-question
  field
    effect : IndirectEffect
    boundedQuestion : String
    observedCausalEffect : Bool
open BoundedEffectQuestion public

openSecondOrder : List BoundedEffectQuestion
openSecondOrder =
  bounded-effect-question broadcasterAudienceFraming
    "What was actually broadcast, to whom, and with what measurable exposure or correction?" false
  ∷ bounded-effect-question donorAgendaAccess
    "Did specific published policy or campaign artefacts originate with documented donors or advisers?" false
  ∷ bounded-effect-question fundingForFutureIndependentMedia
    "What editorial independence rules apply to ARN's 19.9%-revenue interest in Kyle's new show?" false
  ∷ bounded-effect-question institutionalTrustImpact
    "Can 2GB's BOM headline predict measured trust loss when listeners receive the full official correction?" false
  ∷ bounded-effect-question socialMediaDistribution
    "Which actual transcript chunks were clipped and syndicated, preserving source roots and timing?" false
  ∷ []

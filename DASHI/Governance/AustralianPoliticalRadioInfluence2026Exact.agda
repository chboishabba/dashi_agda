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
  epbcReconsiderationRequest : PoliticalRelation
  proceduralValidityDecision : PoliticalRelation
  citedScientificMethod : PoliticalRelation
  projectSpecificExpertModel : PoliticalRelation
  documentedFormLetterFamily : PoliticalRelation
  petitionSupportAggregation : PoliticalRelation
  reportedPrivateDocumentCustody : PoliticalRelation
  nativeAudioPublication : PoliticalRelation
  inferredNamedReferent : PoliticalRelation
  publicParliamentaryInquiry : PoliticalRelation
  historicalInstitutionalFunding : PoliticalRelation
  timedTargetedInformationRelease : PoliticalRelation
  originalOpinionProduction : PoliticalRelation
  traceableClaimAmplification : PoliticalRelation
  advertiserBoycottCampaign : PoliticalRelation
  commercialLeaseArrangement : PoliticalRelation
  ownershipBuyoutSettlement : PoliticalRelation
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
  "https://www.marketindex.com.au/asx/a1n/announcements/settlement-of-legal-proceedings-with-mr-sandilands-2A1677721"
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
  independentOriginalClaimConcentration : IndirectEffect
  donorAdjacentGasPolicyShift : IndirectEffect
  project2025PolicyProposalVersusEnactment : IndirectEffect
  springfieldResidentialGasDemandPersistence : IndirectEffect

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
  ∷ bounded-effect-question independentOriginalClaimConcentration
    "For BOM and GBR narratives, how many truly independent claim producers exist after deduplicating syndication, shared transcripts, and downstream copies? Compare original-versus-effective source diversity, not raw URL counts; ClimateGenealogyTypedCasesExact is the owner of tobacco/API method parallels." false
  ∷ bounded-effect-question donorAdjacentGasPolicyShift
    "HansonCapacityCriticismHyperformalismExact owns the June 2026 gas-reservation reversal. What contemporaneous industry consultation record, actual policy text and donor-beneficiary join (Senex 49% Hancock) distinguish alignment from influence?" false
  ∷ bounded-effect-question project2025PolicyProposalVersusEnactment
    "GodsEyeViewDiagnosisDrivenActivistRollupExact and GodsEyeViewWorldEpistemicSourceAtlasExact own the 2023 Heritage chapter packet. What chapter-author wording and dated US policy action match, and is Australian uptake an independent analogy or a proven transferred instruction?" false
  ∷ bounded-effect-question springfieldResidentialGasDemandPersistence
    "SensibLawSpringfieldGasLobbyingOwnershipSnowballExact and SensibLawAzureSpringfieldInducedGasDemandExact own source evidence and missing records for local network, developer, gas endpoints and fixed-charge demand; identify any true same-object policy-to-asset-to-household bridge before asserting lobbying causation." false
  ∷ []

-- Source joins first surfaced by user-provided Google AI Mode answer,
-- then checked against separately attributed publications. The AI answer
-- is NOT an evidentiary root; its URL, hash, locations and unresolved leads
-- are recorded in docs/bom_fordham_temperature_claim_audit_20261024.md.
-- Do not duplicate canonical DOJ EFTA01615861 (PR #1131).
rinehartBannonDevineEvent : RelationshipReceipt
rinehartBannonDevineEvent = relationship-receipt
  "Gina Rinehart and Steve Bannon" "Miranda Devine Manhattan book launch"
  conferenceCoAttendance journalistCorroboration
  "Daanyal Saeed, Crikey, 6 Nov 2024"
  "https://www.crikey.com.au/2024/11/06/australian-conservatives-normal-us-election/"
  "Crikey reports both Rinehart and Bannon attended Devine's Manhattan book launch. Co-attendance supports proximity, NOT sponsorship or political direction."
  false false false

advanceSheahanBannonConversation : RelationshipReceipt
advanceSheahanBannonConversation = relationship-receipt
  "Matthew Sheahan / Advance" "Steve Bannon"
  reportedMeeting journalistCorroboration
  "Mike Seccombe, The Saturday Paper, 7 Feb 2026"
  "https://www.thesaturdaypaper.com.au/news/politics/2026/02/07/did-steve-bannon-stop-labor-winning-2019"
  "Article says Sheahan had been spotted chatting with Bannon in Washington; supplies no verified meeting agenda, strategic instruction, formal contract or causal campaign join."
  false false false

rinehartMcWilliamSecuredMediaStake : RelationshipReceipt
rinehartMcWilliamSecuredMediaStake = relationship-receipt
  "Gina Rinehart / Hancock-related financing" "Bruce McWilliam Southern Cross Media shares"
  securedStakeFinancing journalistCorroboration
  "Guardian business 27 May 2026; ASX security deed reported"
  "https://www.theguardian.com/business/2026/may/27/gina-rinehart-pays-for-bruce-mcwilliam-purchase-southern-cross-media"
  "About AUD26m financing for near-10% stake in Seven/Hit/Triple M parent, with relevant interest and contingent security/voting rights. Not direct outright ownership, and not editorial control."
  false false false

rinehartStefanovicPodcastFundingClaim : RelationshipReceipt
rinehartStefanovicPodcastFundingClaim = relationship-receipt
  "The Australian / The Front reporting" "Rinehart financing of Stefanovic podcast"
  reportedUnverifiedFunding journalistCorroboration
  "The Australian, The Front, 29 Jun 2026 AEST"
  "https://podcasts.apple.com/za/podcast/did-the-ben-roberts-smith-drama-end-karl-stefanovics-career/id1614339406?i=1000774589371"
  "Publisher says Rinehart 'appears' to have bankrolled the podcast; contract, amount, funding route and editorial conditions not acquired. Repeating publisher wording does NOT verify completed funding."
  false false false

stefanovicRobinsonPublication : RelationshipReceipt
stefanovicRobinsonPublication = relationship-receipt
  "The Karl Stefanovic Show" "Tommy Robinson interview"
  editorialPublication journalistCorroboration
  "ABC 24-26 June 2026"
  "https://www.abc.net.au/news/2026-06-24/karl-stefanovic-tommy-robinson-podcast-interview-taken-offline/106834832"
  "Podcast interview published then removed from Stefanovic platforms. Nine confirmed his departure 26 June. A platforming act is not evidence of Bannon oversight."
  false false false

hansonRepublishedRobinson : RelationshipReceipt
hansonRepublishedRobinson = relationship-receipt
  "Pauline Hanson official video channel" "Stefanovic-Robinson interview"
  mediaRedistribution journalistCorroboration
  "ABC/Guardian reporting 24-25 June 2026"
  "https://www.abc.net.au/news/2026-06-24/karl-stefanovic-tommy-robinson-podcast-interview-taken-offline/106834832"
  "Hanson republished a recording. Platform redistribution is observable, but publisher permission, a business agreement or command chain was not established."
  false false false

mandelsonXstrataEpsteinTaxEmail : RelationshipReceipt
mandelsonXstrataEpsteinTaxEmail = relationship-receipt
  "Peter Mandelson" "Jeffrey Epstein / forwarded Xstrata mining-tax correspondence"
  publishedCorrespondence journalistCorroboration
  "Ben Butler, ABC, 2 Feb 2026, reporting on released DOJ emails from June 2010"
  "https://www.abc.net.au/news/2026-02-02/peter-mandelson-on-rudds-mining-super-profits-tax-epstein-files/106295236"
  "A concrete Australian resource-tax information path: Mandelson emailed Epstein campaign analysis enclosing material from Xstrata chief Mick Davis. Does NOT prove Epstein directed Australia's mining lobby or Rudd's removal."
  false false false

jonesGillardRecordedRemark : RelationshipReceipt
jonesGillardRecordedRemark = relationship-receipt
  "Alan Jones at Sydney University Liberal Club dinner" "Julia Gillard / her late father"
  editorialPublication journalistCorroboration
  "ABC, 30 Sep 2012, contemporaneous recording and apology"
  "https://www.abc.net.au/news/2012-09-30/jones-says-pms-dad-27died-of-shame27/4287770"
  "The offensive recorded comment, Jones's subsequent apology and advertiser backlash are independently reported. This 2012 source predates the 2019 Bannon-Palmer claims; similar rhetoric is not proof of shared command."
  false false false

rinehartOneNationHeadOffice : RelationshipReceipt
rinehartOneNationHeadOffice = relationship-receipt
  "Hanrine / Rinehart-owned property" "One Nation national headquarters premises"
  commercialLeaseArrangement journalistCorroboration
  "AAP, 5 Oct 2026, and One Nation/Hancock statements"
  "https://aapnews.aap.com.au/news/one-nation-to-shuffle-deck-rent-gina-rinehart-office"
  "Rinehart-linked entity purchased roughly AUD8m Brisbane premises. One Nation and Hancock say it rents space at commercial rate; lease terms and actual rent have not been independently audited. Building ownership is NOT donation of the title to party."
  false false false

stefanovicIbrahimOwnershipSettlement : RelationshipReceipt
stefanovicIbrahimOwnershipSettlement = relationship-receipt
  "Karl Stefanovic / Keshnee Ibrahim podcast partners" "123 Podcast Pty Ltd"
  ownershipBuyoutSettlement journalistCorroboration
  "AAP 9 Oct 2026; RadioInfo 11 Oct 2026"
  "https://radioinfo.com.au/podcast-info/karl-stefanovic-podcast-to-resume-unfettered/"
  "The company had 45% interests for Stefanovic and the Ibrahim side; reports say a court dispute ended in confidential buyout by Stefanovic. Payment amount and current ultimate register not obtained; this is NOT proof Rinehart was equity holder."
  false false false

mfwKyleAdvertiserCampaign : RelationshipReceipt
mfwKyleAdvertiserCampaign = relationship-receipt
  "Mad F***ing Witches / #VileKyle" "Advertisers on Kyle and Jackie O"
  advertiserBoycottCampaign journalistCorroboration
  "MFW first-party campaigns; Guardian 9 Oct 2024; Money Magazine 2026"
  "https://www.theguardian.com/media/2024/oct/09/kyle-and-jackie-o-show-advertisers-back-out-violent-misogyny-accusations-campaign-mfw-ntwnfb"
  "MFW explicitly targeted commercial sponsorship of broadcasts; some named advertisers withdrew or reviewed, and ARN acknowledged objectionable programming. MFW's larger asserted count/cost remains an attributed estimate with many alternative reasons for ad churn."
  false false false

-- The following impossible promotions are *typed distinctions*, not empirical theorems.
-- Their uninhabited types cannot establish real-world source facts.
data EpsteinDocumentMentionProvesMeeting : Set where
data ReportedPodcastBackerIsAuditedCapital : Set where
data OriginalInterviewFileAccessIsProvenInstruction : Set where

noMentionMeeting : EpsteinDocumentMentionProvesMeeting → ⊥
noMentionMeeting ()
noRumourToEquity : ReportedPodcastBackerIsAuditedCapital → ⊥
noRumourToEquity ()
noRepublishedFileCommand : OriginalInterviewFileAccessIsProvenInstruction → ⊥
noRepublishedFileCommand ()


-- Selected historical comparison from the independent 2021 Great Barrier
-- Reef literature. These are bounded joins, not a claim that 2021 actors
-- commissioned 2026 BOM radio content. The complete non-exhaustive
-- graph is in Docs/support/reference/australian_climate_claim_origin_edges_20261025.csv.
-- Other existing environmental / genealogy / gas owners remain canonical.

leyAimsTargetedMediaPreview : RelationshipReceipt
leyAimsTargetedMediaPreview = relationship-receipt
  "2021 federal environment minister's office / AIMS"
  "Selected News Corp newspapers: The Australian and Courier Mail"
  timedTargetedInformationRelease journalistCorroboration
  "Michael Slezak, ABC, 2 September 2021; FOI-derived correspondence"
  "https://www.abc.net.au/news/2021-09-02/government-told-science-agency-to-rush-reef-report-release/100422190"
  "FOI records show pressure to accelerate AIMS report publication and preparation for selected-media preview; government and agency characterised request as reasonable. Not proof the minister altered AIMS coral measurements or commissioned Ridd's separate column."
  false false false

riddIndependentReefOpinion : RelationshipReceipt
riddIndependentReefOpinion = relationship-receipt
  "Peter Ridd"
  "23 July 2021 The Australian reef-science commentary"
  originalOpinionProduction journalistCorroboration
  "Lubicz-Zaorski/Newlands/Petray, Public Understanding of Science; original Ridd article traced"
  "https://journals.sagepub.com/doi/10.1177/09636625231202117"
  "Peer-reviewed source genealogy separately attributes Ridd's newspaper interpretation of an AIMS 2021 report. The opinion is not the original AIMS scientific assessment."
  false false false

mooreAmplifiedRiddReefClaim : RelationshipReceipt
mooreAmplifiedRiddReefClaim = relationship-receipt
  "Peter Ridd's original The Australian reef interpretation"
  "Patrick Moore's Twitter sharing of Ridd opinion"
  traceableClaimAmplification journalistCorroboration
  "Lubicz-Zaorski/Newlands/Petray 2023 online / 2024 issue; Twitter network trace"
  "https://journals.sagepub.com/doi/10.1177/09636625231202117"
  "Peer-reviewed network analysis attributes sharing of Ridd content to Moore. This is evidence of amplification, not an independent coral measurement, a payment or a shared campaign command."
  false false false

acmaReefOutsidersFinding : RelationshipReceipt
acmaReefOutsidersFinding = relationship-receipt
  "ACMA"
  "Sky News Outsiders 2021 reef-report broadcasts / 2023 decisions"
  enforcementFinding regulatoryDetermination
  "ACMA television broadcaster investigations, 26 April 2023: BI-645, BI-646, BI-647"
  "https://www.acma.gov.au/investigations-tv-broadcasters"
  "ACMA found specific accuracy/misrepresentation and news-commentary distinction breaches for Outsiders across relevant regional and subscription licences. Do not generalise findings to every Sky programme or equate with 2026 BOM broadcast."
  false false false


-- Current source genealogy: the single October 18 Outsiders appearance is
-- a direct byline and audio clip join to the BOM audit's archival journalism.
-- Neither direct Lloyd broadcast reuse nor IPA distribution pays any other
-- broadcaster's editorial instruction or a specific donor-funded programme.
skyOutsidersLloydRiddSameProgramme : RelationshipReceipt
skyOutsidersLloydRiddSameProgramme = relationship-receipt
  "Sky News Outsiders / Rowan Dean"
  "Graham Lloyd audio excerpt and Peter Ridd interview, BOM, 18 Oct 2026"
  editorialPublication institutionRecord
  "IPA hosted first-party Outsiders episode transcript, 18 October 2026"
  "https://ipa.org.au/latest-news/peter-ridd-on-outsiders-news24-18-october-2026"
  "Host introduces Lloyd audio from original reporting then Ridd; transcribed named turns support broadcast presence and later publication. No evidence this broadcast instructed Fordham's different 19 Oct programme."
  false false false

ipaHostsBOMOutsidersTranscript : RelationshipReceipt
ipaHostsBOMOutsidersTranscript = relationship-receipt
  "Sky Outsiders 18 October 2026 discussion featuring Ridd and Lloyd"
  "Institute of Public Affairs own website transcript"
  traceableClaimAmplification institutionRecord
  "IPA first-party publication, 18 October 2026"
  "https://ipa.org.au/latest-news/peter-ridd-on-outsiders-news24-18-october-2026"
  "IPA transcribes and distributes programme content; publishing the interview does not generate independent evidence of the BOM observation or show who funded production."
  false false false

ipaRiddResearchFellowship : RelationshipReceipt
ipaRiddResearchFellowship = relationship-receipt
  "Peter Ridd"
  "Institute of Public Affairs Project for Real Science"
  professionalAffiliation institutionRecord
  "IPA announcement of Ridd's unpaid fellow role, 2021"
  "https://ipa.org.au/publications-ipa/peter-ridds-fight-for-real-science-is-not-over"
  "IPA itself announced Ridd's unpaid research fellowship and separate solicitation of donations. No source-derived attribution of any Hancock payment to the individual fellowship."
  false false false

hancockToIPAHistoricalFunding : RelationshipReceipt
hancockToIPAHistoricalFunding = relationship-receipt
  "Hancock Prospecting"
  "Institute of Public Affairs"
  historicalInstitutionalFunding journalistCorroboration
  "Christiane Barro, The New Daily, 24 July 2018, about 2016-17 receipts"
  "https://www.thenewdaily.com.au/news/national/2018/07/24/ipa-membership-donors"
  "Reporting identifies AUD4.5m historical IPA donations across two years. Neither current 2026 funding, nor an earmark for Ridd, Sky, Lloyd or Fordham, follows from this organizational record."
  false false false


-- Pareto snowball: direct public cross-site reproduction of an identifiable
-- article is a concrete transfer of CONTENT, not evidence of transferred
-- policy authorship or of an editorial commission. Reuses Ibrahim source
-- genealogy's independence/primary-carrier distinctions in the evidence
-- ledger rather than importing its large dependency graph here.
creightonIPAOriginalArticle : RelationshipReceipt
creightonIPAOriginalArticle = relationship-receipt
  "Adam Creighton, original The Australian opinion"
  "IPA web republication, 17 April 2026"
  traceableClaimAmplification institutionRecord
  "IPA original-source credit 17 April 2026"
  "https://ipa.org.au/research/australias-prosperity/our-energy-policy-is-in-the-hands-of-the-incompetent"
  "The IPA labels Adam Creighton author and links to The Australian as the original publisher. Same credited text is not a separate original institutional energy-system study."
  false false false

senexLinksIPACreighton : RelationshipReceipt
senexLinksIPACreighton = relationship-receipt
  "Institute of Public Affairs, Adam Creighton 17 April opinion"
  "Senex Energy company newsroom, 21 April 2026"
  traceableClaimAmplification institutionRecord
  "Senex directly credits IPA author and links hosted article"
  "https://senexenergy.com.au/news/our-energy-policy-is-in-the-hands-of-the-incompetent-the-australian/"
  "First-party gas producer promotes a named IPA opinion. There is no corporate donor payment, commissioned piece or policy instruction in this receipt."
  false false false

hancockReprintsJohnsonNightly : RelationshipReceipt
hancockReprintsJohnsonNightly = relationship-receipt
  "Stephen Johnson, The Nightly, 22 April 2026"
  "Hancock Energy website, 22 April 2026"
  traceableClaimAmplification institutionRecord
  "Hancock Energy explicit original-author credit"
  "https://www.hancockenergy.com.au/gas-tax-would-burn-everyday-australians/"
  "Hancock Energy reproduces Johnson's named article about a 25 percent gas-export tax, with attribution to The Nightly. Republishing is not independent modelling or authorship of the original article."
  false false false

senexLinksJohnsonNightly : RelationshipReceipt
senexLinksJohnsonNightly = relationship-receipt
  "Stephen Johnson, The Nightly, 22 April 2026"
  "Senex Energy newsroom, 27 April 2026"
  traceableClaimAmplification institutionRecord
  "Senex first-party article links to original The Nightly text"
  "https://senexenergy.com.au/news/why-a-25-per-cent-tax-on-gas-exports-would-hurt-everyday-australians/"
  "The corporate item sends readers to the same titled Johnson original. Shared publisher and policy stance cannot establish business-to-party consultation identity."
  false false false

senateGasTaxInquiryPublicComparator : RelationshipReceipt
senateGasTaxInquiryPublicComparator = relationship-receipt
  "Australian Senate Select Committee on the Taxation of Gas Resources"
  "Public debate on gas levy, 22 April hearings to 7 May report"
  publicParliamentaryInquiry institutionRecord
  "Australian Parliament 7 May report, hearings 21/22/24 April"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Taxation_of_Gas_Resources/TaxationofGasResources/Report/Chapter_1_-_Report"
  "Over 230 public submissions and competing evidence, no agreed committee recommendations on tax approach. Public common arguments are a competing explanatory channel; no proof Senex or IPA drafted One Nation's June policy."
  false false false

-- Explicit negative controls: content republication is real, while
-- consultation-party identity and downstream policy causal transfer are open.
data LinkedIndustryArticleProvesPartyDrafting : Set where
linkedIndustryArticleNotPartyDrafting : LinkedIndustryArticleProvesPartyDrafting → ⊥
linkedIndustryArticleNotPartyDrafting ()

data CommonPoliticalArgumentProvesSharedSponsor : Set where
commonArgumentDoesNotProveSponsor : CommonPoliticalArgumentProvesSharedSponsor → ⊥
commonArgumentDoesNotProveSponsor ()


-- Direct BOM -> gas-policy / reef rhetorical cross-pollination in a single
-- first-party-transcribed 18 October 2026 programme. The actor's statement
-- is owned by the actor; this transcript cannot prove the legal or scientific
-- accuracy of a referenced WA gas action, nor identify an unnamed project.
riddBOMGasLitigationArgument : RelationshipReceipt
riddBOMGasLitigationArgument = relationship-receipt
  "Peter Ridd, Sky Outsiders interview, 18 October 2026"
  "BOM data criticisms connected rhetorically to unspecified WA gas litigation and reef impacts"
  originalOpinionProduction namedActorSelfReport
  "IPA first-party hosting of Sky Outsiders speaker-labelled edited transcript"
  "https://ipa.org.au/latest-news/peter-ridd-on-outsiders-news24-18-october-2026"
  "Ridd himself draws connection from alleged BOM QA faults to conservation litigation against a WA gas project and disputed reef-impact claims. The transcript does not identify a case, prove litigation merits, or independently corroborate causal claims."
  false false false

rowanDeanBOMNetZeroArgument : RelationshipReceipt
rowanDeanBOMNetZeroArgument = relationship-receipt
  "Rowan Dean, Sky Outsiders host, 18 October 2026"
  "Claimed BOM raw-data errors linked rhetorically to net-zero policy"
  originalOpinionProduction namedActorSelfReport
  "IPA published first-party speaker-labelled edited interview transcript"
  "https://ipa.org.au/latest-news/peter-ridd-on-outsiders-news24-18-october-2026"
  "Dean's published remarks connect disputed temperature data and climate-policy credibility. An attributed broadcaster argument is not validation of the premise or evidence of coordinated instruction."
  false false false


-- Native identifiers establish a stronger referent than generic shared
-- ideology. Each carries its own author and authority status. This is
-- cross-case comparison, not a scientific fact proof or court judgment.

browseACFOriginalS78AApplication : RelationshipReceipt
browseACFOriginalS78AApplication = relationship-receipt
  "Australian Conservation Foundation through Environmental Justice Australia"
  "Environment Minister, Browse to North West Shelf Development EPBC 2018/8319"
  epbcReconsiderationRequest institutionRecord
  "ACF/EJA signed EPBC section 78A reconsideration request, 18 February 2026"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/dc7c83cd-ca6e-f111-ab0d-7ced8d33d5fd/2ab10dab-d681-4911-b881-cc99413f07b6?file=2018-8319-Reconsideration-Request.pdf"
  "13-page primary request seeks reconsideration of 2019 controlling provisions using new modelled GBR harm. This is an administrative reconsideration request, not a filed civil court lawsuit or final merit finding."
  false false false

browse2026ValidityDecisionOnly : RelationshipReceipt
browse2026ValidityDecisionOnly = relationship-receipt
  "Commonwealth ministerial statement, 23 June 2026"
  "Browse EPBC 2018/8319 reconsideration request"
  proceduralValidityDecision institutionRecord
  "Minister Murray Watt press statement, 23 June 2026"
  "https://minister.dcceew.gov.au/watt/media-releases/administrative-decisions-regarding-browse-projects"
  "Departmental delegate found ACF request procedurally valid and opened public-comment process. Minister expressly distinguishes this from any substantive decision on the reconsideration application."
  false false false

browseCitedAbramScienceMethod : RelationshipReceipt
browseCitedAbramScienceMethod = relationship-receipt
  "Nerilie Abram and coauthors, npj Climate Action, 13 October 2025"
  "Perkins-Kirkpatrick February 2026 Browse expert attribution report"
  citedScientificMethod institutionRecord
  "ACF/EJA original 18 February request paragraph 6; original peer-reviewed method"
  "https://doi.org/10.1038/s44168-025-00296-5"
  "ACF request explicitly cites Abram and coauthors as original published project-attribution methodology. A method is not identical to the expert's Browse-specific numeric estimate or independently tested input dataset."
  false false false

perkinsKirkpatrickBrowseExpertModel : RelationshipReceipt
perkinsKirkpatrickBrowseExpertModel = relationship-receipt
  "Sarah Perkins-Kirkpatrick expert report dated 12 February 2026"
  "ACF EPBC 2018/8319 application, 18 February"
  projectSpecificExpertModel institutionRecord
  "Original ACF/EJA s78A reconsideration request paragraphs 5 and 6; Annexure A cited"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/dc7c83cd-ca6e-f111-ab0d-7ced8d33d5fd/2ab10dab-d681-4911-b881-cc99413f07b6?file=2018-8319-Reconsideration-Request.pdf"
  "The request attributes to Perkins-Kirkpatrick a modelled increment of 29.35 million coral colonies lost per future mass-bleaching event from Browse lifetime emissions. This is a prediction in the proponent's legal evidence, not directly observed coral mortality or an adjudicated fact."
  false false false

riddSpecificBrowseReferentInference : RelationshipReceipt
riddSpecificBrowseReferentInference = relationship-receipt
  "Peter Ridd unnamed WA gas and approximately 30m GBR corals reference on 18 October Outsiders"
  "ACF original Browse EPBC 2018/8319 expert-reconsideration claim"
  inferredNamedReferent journalistCorroboration
  "Distinct comparison: IPA edited interview transcript versus ACF/EJA 18 February 2026 application"
  "https://ipa.org.au/latest-news/peter-ridd-on-outsiders-news24-18-october-2026"
  "High-specificity match of WA gas and approximately 30m corals supports Browse as referent; Ridd did not himself name Woodside or EPBC ID in the transcript. This does not mean Ridd quoted or inspected the primary request."
  false false false

fordhamOriginalFourMinutePodcastCarrier : RelationshipReceipt
fordhamOriginalFourMinutePodcastCarrier = relationship-receipt
  "2GB / Ben Fordham Live on 2GB Breakfast"
  "Dodgy data - Weather Bureau accused of climate conspiracy, dedicated episode"
  nativeAudioPublication institutionRecord
  "Apple Podcasts episode item 1000796975224, 18 Oct 2026 21:55 UTC = 19 Oct 07:55 Brisbane"
  "https://podcasts.apple.com/sg/podcast/dodgy-data-weather-bureau-accused-of-climate-conspiracy/id157670116?i=1000796975224"
  "Original 4-minute programme media identity is located but audio waveform and full speaker transcript not extracted. This is a publication receipt not proof of identical Sky audio, script source or headline authorship."
  false false false

data EPBCProcedureMeansFinalApprovalJudgment : Set where
noProceduralPromotion : EPBCProcedureMeansFinalApprovalJudgment → ⊥
noProceduralPromotion ()

data AudioEpisodeLocatorMeansVerifiedSpeech : Set where
noAudioLocatorSpeechPromotion : AudioEpisodeLocatorMeansVerifiedSpeech → ⊥
noAudioLocatorSpeechPromotion ()

data SameUnusualQuantityMeansDirectSourceConsulted : Set where
noReferentInferenceToConsultation : SameUnusualQuantityMeansDirectSourceConsulted → ⊥
noReferentInferenceToConsultation ()


-- The Senate publishes counts of submitted advocacy templates *supporting*
-- a gas export levy. This is a control case for the difference between
-- independent participants, independently authored texts, and independent
-- evidence. No implication that advocacy on this side is invalid or insincere.
gasTaxSenateFiveTemplateFamilies : RelationshipReceipt
gasTaxSenateFiveTemplateFamilies = relationship-receipt
  "Australian Senate Select Committee on the Taxation of Gas Resources"
  "Five gas export levy form-letter template categories (272, 13, 52, 15, 14 copies)"
  documentedFormLetterFamily institutionRecord
  "Senate final report, 7 May 2026, Chapter 1 paragraphs 1.5-1.8"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Taxation_of_Gas_Resources/TaxationofGasResources/Report/Chapter_1_-_Report"
  "Committee counted 366 submitted form letters in five template categories. Friends of the Earth Melbourne is the stated campaign route for the 13-copy type; DoGooder the platform for 52. Authors of three other templates are unknown. Template counts are not counts of independent arguments or evidence, nor a judgement of signatories."
  false false false

gasTaxGetUpPetitionAggregate : RelationshipReceipt
gasTaxGetUpPetitionAggregate = relationship-receipt
  "GetUp! petition submission to Australian gas taxation select committee"
  "Comments from approximately 50000 supporters appended to a submission"
  petitionSupportAggregation institutionRecord
  "Senate final report, 7 May 2026, paragraph 1.9"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Taxation_of_Gas_Resources/TaxationofGasResources/Report/Chapter_1_-_Report"
  "Committee reported the petition-attached comments supported a 25 percent export levy. Petition participation is not 50000 independently produced economic analyses; distinctness from any other submission group is unmeasured."
  false false false

novaClaimsFullBOMAuditCopy : RelationshipReceipt
novaClaimsFullBOMAuditCopy = relationship-receipt
  "Joanne Nova, 18 October 2026 CFACT article"
  "Unpublished Tom Berger / Geoff Sherrington forensic BOM audit"
  reportedPrivateDocumentCustody namedActorSelfReport
  "Jo Nova publicly claims copy held and conditioned publication on author permission"
  "https://www.cfact.org/2026/10/18/boms-scientific-scandal-the-raw-data-is-not-raw/"
  "A named journalist/commentator reports having the complete original audit and says she may publish once permission is obtained, possibly after edits. This is a claimed source-custody route, not an inspected original, a full methodological disclosure, or proof that all audit assertions are accurate."
  false false false

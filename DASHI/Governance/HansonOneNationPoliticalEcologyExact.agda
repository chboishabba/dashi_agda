module DASHI.Governance.HansonOneNationPoliticalEcologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonCapacityCriticismHyperformalismExact as Hanson

------------------------------------------------------------------------
-- HANSON / ONE NATION POLITICAL ECOLOGY
--
-- DASHI-original cross-source reconstruction.
--
-- This module extends the capacity/criticism owner into political ecology:
-- regional conservative inheritance, voter coalitions, media ecology,
-- personnel/party migration, policy bundle, elite-network relations and
-- performative cultural style remain separate coordinates.
--
-- Attribution discipline:
--   external sources own reported facts/interpretations;
--   DASHI owns the typed decomposition and non-collapse theorems;
--   no political or cultural source creates clinical authority.
------------------------------------------------------------------------

data PoliticalEcologySourceRole : Set where
  electoralHistory : PoliticalEcologySourceRole
  voterProfile : PoliticalEcologySourceRole
  mediaStudy : PoliticalEcologySourceRole
  culturalStudy : PoliticalEcologySourceRole
  partyPolicy : PoliticalEcologySourceRole
  personnelHistory : PoliticalEcologySourceRole
  eliteNetworkReporting : PoliticalEcologySourceRole
  regionalDevelopmentProposal : PoliticalEcologySourceRole

record PoliticalEcologySource : Set where
  constructor political-ecology-source
  field
    authorOrInstitution : String
    title : String
    publicationReference : String
    canonicalLocator : String
    sourceRole : PoliticalEcologySourceRole
    boundedClaim : String
    createsClinicalAuthority : Bool
    createsClinicalAuthorityIsFalse :
      createsClinicalAuthority ≡ false

open PoliticalEcologySource public

------------------------------------------------------------------------
-- GROOM / TOOWOOMBA: CONSERVATIVE INHERITANCE, NOT VOTER ESSENCE
------------------------------------------------------------------------

abcGroom2020 : PoliticalEcologySource
abcGroom2020 = political-ecology-source
  "ABC Southern Queensland"
  "The view from Groom, one of Queensland's 'ultra conservative' seats, as by-election looms"
  "2020-11-27"
  "https://www.abc.net.au/news/2020-11-27/groom-byelection-life-in-one-of-australias-safest-seats/12922764"
  electoralHistory
  "Groom had remained in Liberal, National or LNP hands since its creation in 1984; a USQ scholar described it as one of the few true safe seats then remaining in Australia"
  false refl

abcGroom2025 : PoliticalEcologySource
abcGroom2025 = political-ecology-source
  "ABC Elections / Antony Green"
  "Groom Federal Election 2025 Results"
  "2025 federal election guide, finalised 2025-06-08"
  "https://www.abc.net.au/news/elections/federal/2025/guide/groo"
  electoralHistory
  "Groom retained by the LNP; historical series places the Coalition vote consistently about 10-15 percentage points above the Queensland-wide Coalition result"
  false refl

abcToowoombaSouth2024 : PoliticalEcologySource
abcToowoombaSouth2024 = political-ecology-source
  "ABC Elections / Antony Green"
  "Toowoomba South - QLD Electorate, Candidates, Results"
  "2024 Queensland election guide"
  "https://www.abc.net.au/news/elections/qld/2024/guide/toso"
  electoralHistory
  "Toowoomba South has been held by the National Party/LNP continuously since 1974"
  false refl

data GroomHistoricalStatus : Set where
  longRunConservativeSeat : GroomHistoricalStatus
  historicallyCompetitiveSeat : GroomHistoricalStatus

groomHistoricalStatus : GroomHistoricalStatus
groomHistoricalStatus = longRunConservativeSeat

data LongRunSeatHistoryImpliesIndividualBelief : Set where

seatHistoryDoesNotDetermineIndividualVoter :
  LongRunSeatHistoryImpliesIndividualBelief → ⊥
seatHistoryDoesNotDetermineIndividualVoter ()

------------------------------------------------------------------------
-- ORIGINS / SUPPORT COALITION: ASPIRATIONAL-MIDDLE-CLASS HYPOTHESIS
------------------------------------------------------------------------

uneMiddleClassRoots : PoliticalEcologySource
uneMiddleClassRoots = political-ecology-source
  "University of New England / Tony Lynch"
  "One Nation?"
  "2018-11-08"
  "https://www.une.edu.au/about-une/news-and-events/news/2018/11/one-nation"
  voterProfile
  "reports an interpretive argument that One Nation has deep roots in Australian major-party traditions and has appealed to Australian-born voters associated with Menzies-style middle-class status politics"
  false refl

abcOuterSuburban2026 : PoliticalEcologySource
abcOuterSuburban2026 = political-ecology-source
  "ABC News"
  "The economy is strong yet consumer sentiment is rock bottom"
  "2026-07-06"
  "https://www.abc.net.au/news/2026-07-06/house-prices-household-debt-voter-sentiment/106881978"
  voterProfile
  "reports Kos Samaras's analysis of current One Nation support as strongly outer-suburban working-class, Anglo-skewed but with rising second-generation migrant support, organised more around anti-elite cultural register and economic pressure than one coherent ideology"
  false refl

uttingHawkerProfile2026 : PoliticalEcologySource
uttingHawkerProfile2026 = political-ecology-source
  "John Utting / Bruce Hawker survey, reported by Paul Sakkal"
  "1000 One Nation voters said why they were voting for Hanson - and what it would take to switch"
  "2026-08-25"
  "https://www.smh.com.au/politics/federal/1000-one-nation-voters-said-why-they-were-voting-for-hanson-and-what-it-would-take-to-switch-20260824-p5nz7x.html"
  voterProfile
  "survey distinguishes rusted-on and newer One Nation supporters; migration/cultural-change concerns and housing/infrastructure pressures are prominent and many newer supporters disagree with some Hanson positions"
  false refl

dyrenfurthWilliams2026 : PoliticalEcologySource
dyrenfurthWilliams2026 = political-ecology-source
  "Nick Dyrenfurth and Josh Williams"
  "Populist performance and the working class: the discursive and symbolic appeals of One Nation in the competition for 'Aussie Battlers'"
  "Australian Journal of Political Science, 2026; DOI 10.1080/10361146.2026.2680905"
  "https://doi.org/10.1080/10361146.2026.2680905"
  voterProfile
  "analyses Hanson/Roberts working-class performance and argues the party symbolically constructs an Aussie-battler identity; this interpretation is not promoted into a complete voter model"
  false refl

data ClassRegisterHypothesis : Set where
  workingClassPerformance : ClassRegisterHypothesis
  aspirationalMiddleClassStatus : ClassRegisterHypothesis
  outerSuburbanEconomicPressure : ClassRegisterHypothesis
  regionalConservativeInheritance : ClassRegisterHypothesis

canonicalClassRegisterHypotheses : List ClassRegisterHypothesis
canonicalClassRegisterHypotheses =
  workingClassPerformance
  ∷ aspirationalMiddleClassStatus
  ∷ outerSuburbanEconomicPressure
  ∷ regionalConservativeInheritance
  ∷ []

data OneClassRegisterExplainsAllSupport : Set where

classRegisterIsNonSovereign :
  OneClassRegisterExplainsAllSupport → ⊥
classRegisterIsNonSovereign ()

------------------------------------------------------------------------
-- MEDIA ECOLOGY: AMPLIFICATION / CELEBRITY / PLATFORM TRANSITION
------------------------------------------------------------------------

deutchmanEllison1999 : PoliticalEcologySource
deutchmanEllison1999 = political-ecology-source
  "Iva Ellen Deutchman and Anne Ellison"
  "A star is born: the roller coaster ride of Pauline Hanson in the news"
  "Media, Culture & Society 21(1), 1999; DOI 10.1177/016344399021001002"
  "https://doi.org/10.1177/016344399021001002"
  mediaStudy
  "analyses the role of news coverage in Hanson's dramatic escalation as a political figure and the news value created by controversial politics"
  false refl

turnerHansonEffect : PoliticalEcologySource
turnerHansonEffect = political-ecology-source
  "Graeme Turner"
  "Media governmentality, Howardism and the Hanson effect"
  "University of Canberra research record"
  "https://researchprofiles.canberra.edu.au/en/publications/media-governmentality-howardism-and-the-hanson-effect/"
  mediaStudy
  "argues mediated race debate helped propel Hanson into media celebrity and that journalistic practice was constitutive of the Hanson phenomenon"
  false refl

abcMasterTheMedia2026 : PoliticalEcologySource
abcMasterTheMedia2026 = political-ecology-source
  "ABC Radio National / The Conversation"
  "The Making of One Nation: Master the Media"
  "2026-07-17"
  "https://www.abc.net.au/listen/programs/sundayextra/the-making-of-one-nation-master-the-media/106868626"
  mediaStudy
  "2026 media-ecology discussion links historical mainstream-media amplification with shrinking traditional media, social-platform algorithms and newer digital channels"
  false refl

data MediaEcologyPhase : Set where
  massMediaCelebrity1990s : MediaEcologyPhase
  declineAndNegativeCoverage : MediaEcologyPhase
  socialPlatformReentry : MediaEcologyPhase
  fragmentedMediaResurgence2020s : MediaEcologyPhase

data CoverageAutomaticallyCausesSupport : Set where
data ControversyAutomaticallyCausesSupport : Set where
data SocialMediaAutomaticallyExplainsResurgence : Set where

coverageDoesNotAutoCauseSupport : CoverageAutomaticallyCausesSupport → ⊥
coverageDoesNotAutoCauseSupport ()

controversyDoesNotAutoCauseSupport : ControversyAutomaticallyCausesSupport → ⊥
controversyDoesNotAutoCauseSupport ()

socialMediaDoesNotAutoExplainResurgence :
  SocialMediaAutomaticallyExplainsResurgence → ⊥
socialMediaDoesNotAutoExplainResurgence ()

------------------------------------------------------------------------
-- PERSONNEL / PARTY MIGRATION
------------------------------------------------------------------------

abcBarnabyDefection2025 : PoliticalEcologySource
abcBarnabyDefection2025 = political-ecology-source
  "ABC News"
  "Barnaby Joyce joins One Nation, concluding defection from Nationals"
  "2025-12-08"
  "https://www.abc.net.au/news/2025-12-08/barnaby-joyce-joins-one-nation/106114758"
  personnelHistory
  "documents Joyce leaving the Nationals and joining One Nation, citing energy, immigration and cultural-policy alignment"
  false refl

abcBarnabyProfile2026 : PoliticalEcologySource
abcBarnabyProfile2026 = political-ecology-source
  "ABC Australian Story"
  "Barnaby Joyce has switched horses. But will this political gamble pay off?"
  "2026-08-23"
  "https://www.abc.net.au/news/2026-08-23/barnaby-joyce-one-nation-nationals-wife-vikki-campion/106898670"
  personnelHistory
  "documents Joyce's role inside One Nation and differences between his own public style and Hanson's"
  false refl

abcSeanBlack2026 : PoliticalEcologySource
abcSeanBlack2026 = political-ecology-source
  "ABC News"
  "Former One Nation candidates accuse Pauline Hanson, James Ashby of ignoring concerns about employment of Sean Black"
  "2026-04-14"
  "https://www.abc.net.au/news/2026-04-14/former-one-nation-candidates-say-hanson-ashby-ignored-concerns/106559022"
  personnelHistory
  "reports former candidates' allegations concerning internal responses to employment of Sean Black and records Black's criminal history; allegations remain attributed"
  false refl

guardianVictorianCandidates2026 : PoliticalEcologySource
guardianVictorianCandidates2026 = political-ecology-source
  "Guardian Australia"
  "Alleged underworld supporters and unfounded health claims: One Nation rolls out more Victorian election candidates"
  "2026-09-19"
  "https://www.theguardian.com/australia-news/2026/sep/19/one-nation-victorian-election-candidates-michael-piastrino-elita-dabrowski-ben-lucas-ntwnfb"
  personnelHistory
  "reports controversies and prior conduct surrounding several endorsed Victorian candidates; each candidate's facts remain individually sourced rather than becoming a party-wide essence"
  false refl

data PersonnelRelationKind : Set where
  defectionIntoParty : PersonnelRelationKind
  adviserRole : PersonnelRelationKind
  candidateEndorsement : PersonnelRelationKind
  formerMember : PersonnelRelationKind

record PersonnelRelation : Set where
  constructor personnel-relation
  field
    personReference : String
    relationKind : PersonnelRelationKind
    source : PoliticalEcologySource
    relationImpliesWholePartyIdentity : Bool
    relationImpliesWholePartyIdentityIsFalse :
      relationImpliesWholePartyIdentity ≡ false

open PersonnelRelation public

barnabyDefection : PersonnelRelation
barnabyDefection =
  personnel-relation
    "Barnaby Joyce"
    defectionIntoParty
    abcBarnabyDefection2025
    false refl

------------------------------------------------------------------------
-- CURRENT POLICY ATLAS: POLICY != RHETORIC != IMPLEMENTED OUTCOME
------------------------------------------------------------------------

oneNationNationalIssues2026 : PoliticalEcologySource
oneNationNationalIssues2026 = political-ecology-source
  "Pauline Hanson's One Nation"
  "One Nation Policies on Issues Affecting Australia"
  "retrieved 2026-09-19"
  "https://www.onenation.org.au/issues"
  partyPolicy
  "party-owned current policy index; records declared positions, not independent evidence that claimed effects will occur"
  false refl

oneNationImmigration2026 : PoliticalEcologySource
oneNationImmigration2026 = political-ecology-source
  "Pauline Hanson's One Nation"
  "Immigration Reform for a Stronger Australia"
  "retrieved 2026-09-19"
  "https://www.onenation.org.au/immigration"
  partyPolicy
  "declared immigration program including a 130,000 annual visa cap, deportation proposals, longer citizenship/welfare waiting periods, temporary protection visas and proposed withdrawal from the Refugee Convention"
  false refl

oneNationSuper2026 : PoliticalEcologySource
oneNationSuper2026 = political-ecology-source
  "Pauline Hanson's One Nation"
  "One Nation's 3% Super Pay Boost"
  "2026-09-07"
  "https://www.onenation.org.au/super-pay-boost"
  partyPolicy
  "declared optional diversion of one quarter of future compulsory super contributions for eligible renters/mortgage holders for up to three years"
  false refl

oneNationOilGas2026 : PoliticalEcologySource
oneNationOilGas2026 = political-ecology-source
  "Pauline Hanson's One Nation"
  "One Nation's Gas Policy: Australian people to take ownership of our Natural Resources"
  "2026-06-09"
  "https://www.onenation.org.au/gas-policy-ownership"
  partyPolicy
  "declared resource-investment/royalty/wealth-fund program coupled to expansion of oil and gas and opposition to net-zero policy"
  false refl

oneNationJobs : PoliticalEcologySource
oneNationJobs = political-ecology-source
  "Pauline Hanson's One Nation"
  "Australian Jobs and Infrastructure"
  "retrieved 2026-09-19"
  "https://www.onenation.org.au/jobs"
  partyPolicy
  "declared apprenticeship wage subsidies, full-time-work preference and nation-building water/rail/road/energy infrastructure"
  false refl

oneNationMedicalCannabis : PoliticalEcologySource
oneNationMedicalCannabis = political-ecology-source
  "Pauline Hanson's One Nation"
  "Medical Cannabis"
  "retrieved 2026-09-19"
  "https://www.onenation.org.au/cannabis"
  partyPolicy
  "declared continued support for lowering the cost of access to medicinal cannabis"
  false refl

data PolicyDomain : Set where
  immigration : PolicyDomain
  housing : PolicyDomain
  superannuation : PolicyDomain
  familyTax : PolicyDomain
  oilGasResources : PolicyDomain
  energyNuclearCoal : PolicyDomain
  climateNetZero : PolicyDomain
  jobsApprenticeships : PolicyDomain
  healthRegionalServices : PolicyDomain
  medicalCannabis : PolicyDomain
  familyLawChildSupport : PolicyDomain
  firearms : PolicyDomain
  education : PolicyDomain
  crimeJustice : PolicyDomain
  waterDams : PolicyDomain
  foreignOwnership : PolicyDomain
  multinationalTax : PolicyDomain
  citizenInitiatedReferenda : PolicyDomain
  covidInquiryMandates : PolicyDomain
  freeSpeech : PolicyDomain

canonicalPolicyDomains : List PolicyDomain
canonicalPolicyDomains =
  immigration
  ∷ housing
  ∷ superannuation
  ∷ familyTax
  ∷ oilGasResources
  ∷ energyNuclearCoal
  ∷ climateNetZero
  ∷ jobsApprenticeships
  ∷ healthRegionalServices
  ∷ medicalCannabis
  ∷ familyLawChildSupport
  ∷ firearms
  ∷ education
  ∷ crimeJustice
  ∷ waterDams
  ∷ foreignOwnership
  ∷ multinationalTax
  ∷ citizenInitiatedReferenda
  ∷ covidInquiryMandates
  ∷ freeSpeech
  ∷ []

data DeclaredPolicyImpliesPredictedEffect : Set where
data PolicyIndexImpliesInternalConsistency : Set where

declaredPolicyDoesNotAutoProveEffect :
  DeclaredPolicyImpliesPredictedEffect → ⊥
declaredPolicyDoesNotAutoProveEffect ()

policyIndexDoesNotAutoProveConsistency :
  PolicyIndexImpliesInternalConsistency → ⊥
policyIndexDoesNotAutoProveConsistency ()

------------------------------------------------------------------------
-- RINEHART / TOWNSVILLE DEVELOPMENT PROPOSALS
------------------------------------------------------------------------

abcTownsville2026 : PoliticalEcologySource
abcTownsville2026 = political-ecology-source
  "ABC News"
  "Gina Rinehart and Pauline Hanson propose ambitious vision in Townsville"
  "2026-06-18"
  "https://www.abc.net.au/listen/programs/abc-news-top-stories/naus_1900flash_1806/106815960"
  regionalDevelopmentProposal
  "reports Hanson and Rinehart appearing together in Townsville and Rinehart suggesting islands off Townsville be used as SpaceX satellite-launch sites"
  false refl

data DevelopmentProposalKind : Set where
  satelliteLaunchIslands : DevelopmentProposalKind
  aiDataCentre : DevelopmentProposalKind
  semiconductorManufacturing : DevelopmentProposalKind
  freeLandSettlementOrIndustry : DevelopmentProposalKind

record DevelopmentProposalReceipt : Set where
  constructor development-proposal-receipt
  field
    proposalKind : DevelopmentProposalKind
    source : PoliticalEcologySource
    verifiedFromSource : Bool
    verifiedFromSourceIsTrue : verifiedFromSource ≡ true
    distinctFromDataCentreProposal : Bool
    distinctFromDataCentreProposalIsTrue :
      distinctFromDataCentreProposal ≡ true

open DevelopmentProposalReceipt public

townsvilleSpaceXIslandProposal : DevelopmentProposalReceipt
townsvilleSpaceXIslandProposal =
  development-proposal-receipt
    satelliteLaunchIslands
    abcTownsville2026
    true refl
    true refl

data AdjacentNewsItemImpliesSameProposal : Set where

adjacentDataCentreStoryDoesNotMergeWithIslandProposal :
  AdjacentNewsItemImpliesSameProposal → ⊥
adjacentDataCentreStoryDoesNotMergeWithIslandProposal ()

------------------------------------------------------------------------
-- KATH & KIM / CULTURAL REGISTER: ANALOGY, NOT PERSON IDENTITY
------------------------------------------------------------------------

turnbullKathKim2004 : PoliticalEcologySource
turnbullKathKim2004 = political-ecology-source
  "Sue Turnbull"
  "Look at Moiye, Kimmie, Look at Moiye!: Kath and Kim and the Australian Comedy of Taste"
  "Media International Australia 113(1), 2004; DOI 10.1177/1329878X0411300112"
  "https://doi.org/10.1177/1329878X0411300112"
  culturalStudy
  "analyses Kath & Kim through class, taste, suburban aspiration and comedy of recognition"
  false refl

nfsaKathKim : PoliticalEcologySource
nfsaKathKim = political-ecology-source
  "National Film and Sound Archive of Australia"
  "Kath and Kim collection notes"
  "retrieved 2026-09-19"
  "https://www.nfsa.gov.au/collection/item/kylie-epponnee-rae-kath-and-kim"
  culturalStudy
  "describes the series as parody of suburban life, popular culture, brand/advertising consumption and aspirational suburban aesthetics"
  false refl

data CulturalRegisterFeature : Set where
  suburbanVernacular : CulturalRegisterFeature
  aspirationalConsumption : CulturalRegisterFeature
  antiElitePlainSpeech : CulturalRegisterFeature
  comedyOfRecognition : CulturalRegisterFeature
  battlerPerformance : CulturalRegisterFeature

record CulturalAnalogy : Set where
  constructor cultural-analogy
  field
    sourceCultureReference : String
    targetPoliticalReference : String
    sharedCandidateFeatures : List CulturalRegisterFeature
    analogyIsIdentityClaim : Bool
    analogyIsIdentityClaimIsFalse : analogyIsIdentityClaim ≡ false
    analogyIsCausalExplanation : Bool
    analogyIsCausalExplanationIsFalse : analogyIsCausalExplanation ≡ false

open CulturalAnalogy public

kathKimHansonCandidateAnalogy : CulturalAnalogy
kathKimHansonCandidateAnalogy =
  cultural-analogy
    "Kath & Kim suburban comedy/taste register"
    "Pauline Hanson / One Nation public-performance register"
    (suburbanVernacular
     ∷ aspirationalConsumption
     ∷ antiElitePlainSpeech
     ∷ comedyOfRecognition
     ∷ battlerPerformance
     ∷ [])
    false refl
    false refl

------------------------------------------------------------------------
-- MULTI-AXIS POLITICAL-ECOLOGY HYPERFABRIC
------------------------------------------------------------------------

data PoliticalEcologyAxis : Set where
  regionHistoryAxis : PoliticalEcologyAxis
  classStatusAxis : PoliticalEcologyAxis
  economicPressureAxis : PoliticalEcologyAxis
  immigrationIdentityAxis : PoliticalEcologyAxis
  mediaAmplificationAxis : PoliticalEcologyAxis
  socialPlatformAxis : PoliticalEcologyAxis
  publicPerformanceAxis : PoliticalEcologyAxis
  policyBundleAxis : PoliticalEcologyAxis
  personnelNetworkAxis : PoliticalEcologyAxis
  donorEliteAxis : PoliticalEcologyAxis
  institutionalPowerAxis : PoliticalEcologyAxis
  culturalRegisterAxis : PoliticalEcologyAxis
  temporalTrajectoryAxis : PoliticalEcologyAxis
  sourceProvenanceAxis : PoliticalEcologyAxis

canonicalPoliticalEcologyAxes : List PoliticalEcologyAxis
canonicalPoliticalEcologyAxes =
  regionHistoryAxis
  ∷ classStatusAxis
  ∷ economicPressureAxis
  ∷ immigrationIdentityAxis
  ∷ mediaAmplificationAxis
  ∷ socialPlatformAxis
  ∷ publicPerformanceAxis
  ∷ policyBundleAxis
  ∷ personnelNetworkAxis
  ∷ donorEliteAxis
  ∷ institutionalPowerAxis
  ∷ culturalRegisterAxis
  ∷ temporalTrajectoryAxis
  ∷ sourceProvenanceAxis
  ∷ []

data SingleAxisExplainsOneNation : Set where

singleAxisExplanationRejected :
  SingleAxisExplainsOneNation → ⊥
singleAxisExplanationRejected ()

record PoliticalEcologyBoundary : Set where
  constructor political-ecology-boundary
  field
    groomLongRunConservativeHistoryRetained : Bool
    groomHistoryCreatesVoterEssence : Bool
    groomHistoryCreatesVoterEssenceIsFalse :
      groomHistoryCreatesVoterEssence ≡ false

    workingClassAndMiddleClassStatusHypothesesCoexist : Bool
    oneClassRegisterMadeSovereign : Bool
    oneClassRegisterMadeSovereignIsFalse :
      oneClassRegisterMadeSovereign ≡ false

    mediaAmplificationTracked : Bool
    mediaAmplificationProvesElectoralCausation : Bool
    mediaAmplificationProvesElectoralCausationIsFalse :
      mediaAmplificationProvesElectoralCausation ≡ false

    barnabyDefectionTracked : Bool
    controversialMemberDefinesWholeParty : Bool
    controversialMemberDefinesWholePartyIsFalse :
      controversialMemberDefinesWholeParty ≡ false

    fullPolicyBundleTracked : Bool
    declaredPoliciesEqualRealisedEffects : Bool
    declaredPoliciesEqualRealisedEffectsIsFalse :
      declaredPoliciesEqualRealisedEffects ≡ false

    townsvilleIslandProposalIsSpaceXLaunchProposal : Bool
    townsvilleIslandProposalIsDataCentreProposal : Bool
    townsvilleIslandProposalIsDataCentreProposalIsFalse :
      townsvilleIslandProposalIsDataCentreProposal ≡ false

    kathKimComparisonRemainsCulturalAnalogy : Bool
    culturalAnalogyCreatesPersonEssence : Bool
    culturalAnalogyCreatesPersonEssenceIsFalse :
      culturalAnalogyCreatesPersonEssence ≡ false

open PoliticalEcologyBoundary public

canonicalPoliticalEcologyBoundary : PoliticalEcologyBoundary
canonicalPoliticalEcologyBoundary =
  political-ecology-boundary
    true
    false refl
    true
    false refl
    true
    false refl
    true
    false refl
    true
    false refl
    true
    false refl
    true
    false refl

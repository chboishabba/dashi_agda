module DASHI.Wikimedia.IbrahimSnowballManosphereIDWOnlineInfluenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSocialInfluenceConsentCoercionPrimarySourcesExact as Influence
import DASHI.Wikimedia.IbrahimSnowballPedagogyLearningBehaviorInteractionThirdOrderExact as Pedagogy
import DASHI.Wikimedia.IbrahimSnowballReligionEschatologyIdeologyIdentityExact as ReligionIdeology
import DASHI.Wikimedia.IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact as ClimatePolitical

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION:
--
--   manosphere / "intellectual dark web" (IDW)
--        <-> online media / platform ecology
--        <-> social influence / peer relation / audience formation
--        <-> pedagogy / informal learning / visible behaviour
--        <-> ideology / political-theology / climate discourse
--
-- Public-source calibration inspected 2026-09-10:
--
-- * Lott, Murumaa-Mengel & Marling (2025) treat manosphere mainstreaming as a
--   bounded qualitative case study of Estonian manfluencers and TikTok, with
--   attention-economy/platform coordinates. It is not a universal causal model.
-- * Bachaud & Johns (2023) examine selective use/misuse of evolutionary-
--   psychology claims in online manosphere communities. Scientific proposition,
--   citation, interpretation and ideological use remain distinct source roles.
-- * Bari Weiss (2018) popularised the "Intellectual Dark Web" label for a loose
--   set of public thinkers/media personalities; later scholarship/retrospective
--   discussion records substantial internal diversity and later fragmentation.
-- * Finlayson (2021) supplies one critical scholarly analysis of the IDW in
--   relation to neoliberal/right-wing online political communication; it does
--   not make IDW identical to the alt-right or establish every named person's
--   beliefs.
--
-- External labels are historical/source-indexed classification coordinates.
-- They do not establish self-identification, membership, ideology, assent,
-- private belief, motive, causal persuasion, or current views.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- External identities. Person QIDs are person identities only; a source must
-- separately pay any network/movement classification.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim manosphere/IDW online-influence BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10; no membership or ideology promotion")

manosphereQid : Identity.ExternalIdentityDemand
manosphereQid = mkQid "manosphere" "Q17068342"

intellectualDarkWebQid : Identity.ExternalIdentityDemand
intellectualDarkWebQid = mkQid "Intellectual Dark Web" "Q65090919"

ericWeinsteinQid : Identity.ExternalIdentityDemand
ericWeinsteinQid = mkQid "Eric Weinstein" "Q5387722"

bariWeissQid : Identity.ExternalIdentityDemand
bariWeissQid = mkQid "Bari Weiss" "Q39086707"

jordanPetersonQid : Identity.ExternalIdentityDemand
jordanPetersonQid = mkQid "Jordan Peterson" "Q6276882"

andrewTateQid : Identity.ExternalIdentityDemand
andrewTateQid = mkQid "Andrew Tate" "Q18637166"

benShapiroQid : Identity.ExternalIdentityDemand
benShapiroQid = mkQid "Ben Shapiro" "Q4886439"

samHarrisQid : Identity.ExternalIdentityDemand
samHarrisQid = mkQid "Sam Harris (philosopher/neuroscientist)" "Q296047"

------------------------------------------------------------------------
-- Attributed public sources. Each source owns only its bounded propositions.
------------------------------------------------------------------------

lottManosphereSource : Attribution.AttributedSource
lottManosphereSource = Attribution.mkDOISource
  "Kaarel Lott; Maria Murumaa-Mengel; Raili Marling"
  "Mainstreaming the manosphere: discourses of contemporary masculinity among Estonian manfluencers"
  "Humanities and Social Sciences Communications 12, 602"
  "2025"
  "10.1057/s41599-025-04903-y"
  "https://doi.org/10.1057/s41599-025-04903-y"
  Attribution.academicArticleSource
  "bounded qualitative source on Estonian manfluencer discourse, mainstreaming and platform/attention-economy context; not universal manosphere membership or algorithmic-causation evidence"
  Attribution.publicAttribution

bachaudJohnsSource : Attribution.AttributedSource
bachaudJohnsSource = Attribution.mkDOISource
  "Louis Bachaud; Sarah E. Johns"
  "The use and misuse of evolutionary psychology in online manosphere communities: The case of female mating strategies"
  "Evolutionary Human Sciences 5, e28"
  "2023"
  "10.1017/ehs.2023.22"
  "https://doi.org/10.1017/ehs.2023.22"
  Attribution.academicArticleSource
  "source-bounded analysis of how evolutionary-psychology propositions may be selectively interpreted in manosphere communities; scientific claim and ideological use remain separate"
  Attribution.publicAttribution

finlaysonIDWSource : Attribution.AttributedSource
finlaysonIDWSource = Attribution.mkDOISource
  "Alan Finlayson"
  "Neoliberalism, the Alt-Right and the Intellectual Dark Web"
  "Theory, Culture & Society 38(6)"
  "2021"
  "10.1177/02632764211036731"
  "https://doi.org/10.1177/02632764211036731"
  Attribution.academicArticleSource
  "critical scholarly analysis of IDW/right-wing digital political communication; does not identify IDW with alt-right or determine every named actor's beliefs"
  Attribution.publicAttribution

weissIDWHistoricalSource : Attribution.AttributedSource
weissIDWHistoricalSource = Attribution.mkNoDOISource
  "Bari Weiss"
  "Meet the Renegades of the Intellectual Dark Web"
  "The New York Times opinion section"
  "2018"
  "https://www.nytimes.com/2018/05/08/opinion/intellectual-dark-web.html"
  Attribution.newsSource
  "historical media-label/popularisation source for the 2018 IDW grouping; a named list is not timeless membership, ideology equivalence or self-identification"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- BIDI graph audit. Parent labels propose search seams; named/source-specific
-- cases constrain the parent labels in reverse.
------------------------------------------------------------------------

data OnlineInfluenceNode : Set where
  manosphereNode idwNode platformEcologyNode audienceNode ideologyNode : OnlineInfluenceNode

record OnlineInfluenceGraphAudit : Set where
  constructor online-influence-graph-audit
  field
    node : OnlineInfluenceNode
    upwardReading : String
    downwardConstraint : String
    principalWrongTypeRisk : String
    attributionRequired : Bool
    twoEyedRequired : Bool
    parentLabelExplainsEveryMemberOrCase : Bool
open OnlineInfluenceGraphAudit public

manosphereAudit : OnlineInfluenceGraphAudit
manosphereAudit = online-influence-graph-audit manosphereNode
  "heterogeneous umbrella/network ecology connecting multiple online subcommunities and influencer/media practices"
  "subgroup, creator, audience member, cited science, platform and ideology relations require separate receipts"
  "manosphere label != subgroup membership != misogynistic proposition != every user's belief != named-person self-identification"
  true true false

idwAudit : OnlineInfluenceGraphAudit
idwAudit = online-influence-graph-audit idwNode
  "historically source-indexed loose media/intellectual grouping popularised in 2018"
  "historical inclusion cannot recover present-day alignment, climate position, religion, party position, or continued group coherence"
  "media grouping != one ideology != durable organisation != self-identification != current policy position"
  true true false

platformAudit : OnlineInfluenceGraphAudit
platformAudit = online-influence-graph-audit platformEcologyNode
  "distribution/recommendation/attention infrastructure through which discourse may circulate"
  "exposure, recommendation, engagement, adoption, persuasion and private belief remain distinct consumers"
  "algorithmic exposure != persuasion != assent != radicalisation cause"
  true true false

audienceAudit : OnlineInfluenceGraphAudit
audienceAudit = online-influence-graph-audit audienceNode
  "observer/participant relation to media content and community interaction"
  "viewing, engagement, repetition, ironic use, dissent and endorsement cannot be inferred from one another"
  "audience membership != belief != consent != political action"
  true true false

ideologyAudit : OnlineInfluenceGraphAudit
ideologyAudit = online-influence-graph-audit ideologyNode
  "candidate interpretive/political framework attached only by an exact source"
  "same network label may contain divergent empirical, religious, climate and political positions"
  "network adjacency != ideology identity != motive"
  true true false

------------------------------------------------------------------------
-- Regression 1: umbrella label cannot recover subgroup/source role.
------------------------------------------------------------------------

data ManosphereSituatedCase : Set where
  sameUmbrellaResearchDiscussion sameUmbrellaIdeologicalCommunity : ManosphereSituatedCase

data ManosphereSurface : Set where sameManosphereUmbrella : ManosphereSurface

data ManosphereRole : Set where researchDiscussionRole ideologicalCommunityRole : ManosphereRole

manosphereSurface : ManosphereSituatedCase → ManosphereSurface
manosphereSurface _ = sameManosphereUmbrella

manosphereRole : ManosphereSituatedCase → ManosphereRole
manosphereRole sameUmbrellaResearchDiscussion = researchDiscussionRole
manosphereRole sameUmbrellaIdeologicalCommunity = ideologicalCommunityRole

manosphereRoleDefect : INF.NonFactorabilityWitness manosphereSurface manosphereRole
manosphereRoleDefect = INF.nonFactorabilityWitness
  sameUmbrellaResearchDiscussion sameUmbrellaIdeologicalCommunity refl (λ ())

manosphereLabelCannotFactorRole :
  INF.FactorsThrough manosphereSurface manosphereRole → ⊥
manosphereLabelCannotFactorRole =
  INF.witnessRulesOutEveryFlatFactorisation manosphereRoleDefect

------------------------------------------------------------------------
-- Regression 2: same exposure/engagement surface cannot recover assent.
------------------------------------------------------------------------

data ExposureCase : Set where
  sameEngagementEndorsement sameEngagementCriticalOrIronic : ExposureCase

data ExposureSurface : Set where samePlatformEngagement : ExposureSurface

data AssentReading : Set where endorsedContent didNotEstablishEndorsement : AssentReading

exposureSurface : ExposureCase → ExposureSurface
exposureSurface _ = samePlatformEngagement

assentReading : ExposureCase → AssentReading
assentReading sameEngagementEndorsement = endorsedContent
assentReading sameEngagementCriticalOrIronic = didNotEstablishEndorsement

exposureAssentDefect : INF.NonFactorabilityWitness exposureSurface assentReading
exposureAssentDefect = INF.nonFactorabilityWitness
  sameEngagementEndorsement sameEngagementCriticalOrIronic refl (λ ())

engagementCannotFactorAssent :
  INF.FactorsThrough exposureSurface assentReading → ⊥
engagementCannotFactorAssent =
  INF.witnessRulesOutEveryFlatFactorisation exposureAssentDefect

------------------------------------------------------------------------
-- Regression 3: person identity cannot recover network classification.
-- Classification is source/date/role indexed; QID only pays identity.
------------------------------------------------------------------------

data PublicFigureClassificationCase : Set where
  samePersonMediaClassified samePersonClassificationNotPaid : PublicFigureClassificationCase

data PersonIdentitySurface : Set where samePublicPersonIdentity : PersonIdentitySurface

data ClassificationReading : Set where sourcePaidClassification classificationUnresolved : ClassificationReading

personIdentitySurface : PublicFigureClassificationCase → PersonIdentitySurface
personIdentitySurface _ = samePublicPersonIdentity

classificationReading : PublicFigureClassificationCase → ClassificationReading
classificationReading samePersonMediaClassified = sourcePaidClassification
classificationReading samePersonClassificationNotPaid = classificationUnresolved

personClassificationDefect :
  INF.NonFactorabilityWitness personIdentitySurface classificationReading
personClassificationDefect = INF.nonFactorabilityWitness
  samePersonMediaClassified samePersonClassificationNotPaid refl (λ ())

personIdentityCannotFactorNetworkMembership :
  INF.FactorsThrough personIdentitySurface classificationReading → ⊥
personIdentityCannotFactorNetworkMembership =
  INF.witnessRulesOutEveryFlatFactorisation personClassificationDefect

------------------------------------------------------------------------
-- Regression 4: same scientific proposition surface can occupy different roles
-- in research and ideological discourse. Citation/quotation alone cannot
-- recover validity, interpretation or downstream use.
------------------------------------------------------------------------

data ScientificUseCase : Set where
  sameClaimResearchContext sameClaimIdeologicalAppropriation : ScientificUseCase

data ScientificClaimSurface : Set where sameScientificClaimToken : ScientificClaimSurface

data ScientificUseRole : Set where researchUse ideologicalUse : ScientificUseRole

scientificClaimSurface : ScientificUseCase → ScientificClaimSurface
scientificClaimSurface _ = sameScientificClaimToken

scientificUseRole : ScientificUseCase → ScientificUseRole
scientificUseRole sameClaimResearchContext = researchUse
scientificUseRole sameClaimIdeologicalAppropriation = ideologicalUse

scientificUseDefect : INF.NonFactorabilityWitness scientificClaimSurface scientificUseRole
scientificUseDefect = INF.nonFactorabilityWitness
  sameClaimResearchContext sameClaimIdeologicalAppropriation refl (λ ())

scientificClaimCannotFactorUseRole :
  INF.FactorsThrough scientificClaimSurface scientificUseRole → ⊥
scientificClaimCannotFactorUseRole =
  INF.witnessRulesOutEveryFlatFactorisation scientificUseDefect

------------------------------------------------------------------------
-- IDW historical-label regression: a shared historical media label cannot
-- recover present policy/science positions. This is deliberately generic; it
-- does not assign a current climate/religious/political stance to named people.
------------------------------------------------------------------------

data HistoricalIDWCase : Set where
  sameHistoricalLabelCurrentPositionA sameHistoricalLabelCurrentPositionB : HistoricalIDWCase

data HistoricalIDWSurface : Set where sameHistoricalIDWLabel : HistoricalIDWSurface

data CurrentPositionReading : Set where currentPositionA currentPositionB : CurrentPositionReading

historicalIDWSurface : HistoricalIDWCase → HistoricalIDWSurface
historicalIDWSurface _ = sameHistoricalIDWLabel

currentPositionReading : HistoricalIDWCase → CurrentPositionReading
currentPositionReading sameHistoricalLabelCurrentPositionA = currentPositionA
currentPositionReading sameHistoricalLabelCurrentPositionB = currentPositionB

historicalIDWPositionDefect :
  INF.NonFactorabilityWitness historicalIDWSurface currentPositionReading
historicalIDWPositionDefect = INF.nonFactorabilityWitness
  sameHistoricalLabelCurrentPositionA sameHistoricalLabelCurrentPositionB refl (λ ())

historicalIDWLabelCannotFactorCurrentPosition :
  INF.FactorsThrough historicalIDWSurface currentPositionReading → ⊥
historicalIDWLabelCannotFactorCurrentPosition =
  INF.witnessRulesOutEveryFlatFactorisation historicalIDWPositionDefect

------------------------------------------------------------------------
-- Existing owners reused instead of rebuilt.
------------------------------------------------------------------------

visibleComplianceStillCannotRecoverRelation :
  INF.FactorsThrough Influence.complianceSurface Influence.relationReading → ⊥
visibleComplianceStillCannotRecoverRelation = Influence.complianceCannotFactorRelation

pedagogyBoundary : Pedagogy.PedagogyLearningBehaviorInteractionBoundary
pedagogyBoundary = Pedagogy.canonicalPedagogyLearningBehaviorInteractionBoundary

religionIdeologyBoundary : ReligionIdeology.ReligionEschatologyIdeologySnowballBoundary
religionIdeologyBoundary = ReligionIdeology.canonicalReligionEschatologyIdeologySnowballBoundary

climatePoliticalBoundary : ClimatePolitical.PoliticalTheologyClimateLogicBoundary
climatePoliticalBoundary = ClimatePolitical.canonicalPoliticalTheologyClimateLogicBoundary

------------------------------------------------------------------------
-- Reverse constraints back into parent nodes.
------------------------------------------------------------------------

record ReverseOnlineParentConstraint : Set where
  constructor reverse-online-parent-constraint
  field
    parentNode : String
    childWitness : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ReverseOnlineParentConstraint public

socialInfluenceConstraint : ReverseOnlineParentConstraint
socialInfluenceConstraint = reverse-online-parent-constraint
  "Social influence"
  "manosphere/IDW audience and platform exposure cases"
  "exposure, interaction, conformity, coercion, consent, endorsement and private belief remain distinct"
  false

pedagogyConstraint : ReverseOnlineParentConstraint
pedagogyConstraint = reverse-online-parent-constraint
  "Pedagogy / informal learning"
  "public intellectual/influencer content"
  "content delivery or observed learning does not establish learner agency, assent, source validity or ethical legitimacy"
  false

ideologyConstraint : ReverseOnlineParentConstraint
ideologyConstraint = reverse-online-parent-constraint
  "Ideology"
  "heterogeneous umbrella/media network labels"
  "network adjacency, historical inclusion, self-description, present policy and private motive remain separately source-paid"
  false

climateReligionConstraint : ReverseOnlineParentConstraint
climateReligionConstraint = reverse-online-parent-constraint
  "Climate / religion / political-theology discourse"
  "historically overlapping public-intellectual networks"
  "a media-network label cannot recover climate position, religious worldview, end-times belief or policy action"
  false

------------------------------------------------------------------------
-- Snowball payment / firewalls.
------------------------------------------------------------------------

record ManosphereIDWOnlineInfluenceBidiBoundary : Set where
  constructor manosphere-idw-online-influence-bidi-boundary
  field
    qidsRequestedAndRetainedWhenSafelyResolved : Bool
    sourceRoleAndDateRetainedWithClassification : Bool
    manosphereAndIDWRemainDistinct : Bool
    umbrellaLabelDoesNotDetermineSubgroupOrBelief : Bool
    mediaLabelDoesNotCreateSelfIdentification : Bool
    personQidDoesNotCreateNetworkMembership : Bool
    engagementDoesNotCreateAssent : Bool
    exposureDoesNotCreatePersuasionOrRadicalisation : Bool
    scientificCitationDoesNotCreateIdeologicalValidity : Bool
    historicalNetworkLabelDoesNotDetermineCurrentPosition : Bool
    climateOrReligiousPositionNotInferredFromNetworkLabel : Bool
    namedPersonsNotMadeIdeologicallyEquivalent : Bool
    leafEvidenceConstrainsParentSemanticsBidi : Bool
    attributionTravelsWithGraphExpansion : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ManosphereIDWOnlineInfluenceBidiBoundary public

canonicalManosphereIDWOnlineInfluenceBidiBoundary :
  ManosphereIDWOnlineInfluenceBidiBoundary
canonicalManosphereIDWOnlineInfluenceBidiBoundary =
  manosphere-idw-online-influence-bidi-boundary
    true true true true true true true true true true true true true true false

data ManosphereLabelCreatesEveryMemberBelief : Set where
data IDWLabelCreatesUnifiedIdeology : Set where
data QidCreatesNetworkMembership : Set where
data EngagementCreatesAssent : Set where
data RecommendationCreatesRadicalisation : Set where
data ScientificCitationCreatesIdeologicalTruth : Set where
data HistoricalIDWLabelCreatesCurrentClimatePosition : Set where

manosphereLabelDoesNotCreateEveryMemberBelief :
  ManosphereLabelCreatesEveryMemberBelief → ⊥
manosphereLabelDoesNotCreateEveryMemberBelief ()

idwLabelDoesNotCreateUnifiedIdeology : IDWLabelCreatesUnifiedIdeology → ⊥
idwLabelDoesNotCreateUnifiedIdeology ()

qidDoesNotCreateNetworkMembership : QidCreatesNetworkMembership → ⊥
qidDoesNotCreateNetworkMembership ()

engagementDoesNotCreateAssent : EngagementCreatesAssent → ⊥
engagementDoesNotCreateAssent ()

recommendationDoesNotCreateRadicalisation : RecommendationCreatesRadicalisation → ⊥
recommendationDoesNotCreateRadicalisation ()

scientificCitationDoesNotCreateIdeologicalTruth : ScientificCitationCreatesIdeologicalTruth → ⊥
scientificCitationDoesNotCreateIdeologicalTruth ()

historicalIDWLabelDoesNotCreateCurrentClimatePosition :
  HistoricalIDWLabelCreatesCurrentClimatePosition → ⊥
historicalIDWLabelDoesNotCreateCurrentClimatePosition ()

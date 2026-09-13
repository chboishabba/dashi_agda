module DASHI.Wikimedia.IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballSourceMonitoringCollectiveMemoryEpistemicInjusticeBidiExact as Collective
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as LearningMemory
import DASHI.Wikimedia.IbrahimSnowballReligionEschatologyIdeologyIdentityExact as ReligionPrior
import DASHI.Wikimedia.IbrahimSnowballOralHistoryTraditionArchivalSilenceDigitalMemoryBidiExact as OralHistory
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Culture.PatternMindReciprocityLoveBridge as PatternMind
import DASHI.Culture.KimmererBraidingAcknowledgement as Kimmerer

------------------------------------------------------------------------
-- IBRAHIM / COLLECTIVE MEMORY / MANDELA EFFECT / RELIGION / INDIGENOUS
-- KNOWLEDGE / BRAIDING BIDI
--
-- Shared recollection, collective memory, false memory, religious memory,
-- oral/traditional knowledge and historical truth are different consumers.
-- Social transmission is not itself evidence of falsehood, and community
-- significance is not itself historical/empirical verification.
--
-- Fruit of the Loom is a bounded visual-Mandela-effect case study.  It is not
-- used as evidence for paranormal mechanisms or as a model for Indigenous oral
-- tradition.  Indigenous knowledge carriers retain place, people relation,
-- practice, authority, permission, obligation and transmission mode through the
-- existing Two-Eyed Seeing owner.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim Mandela/religion/Indigenous-memory/braiding BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, memory provenance, cultural authority, diagnosis or historical verification")

mandelaEffectQid : Identity.ExternalIdentityDemand
mandelaEffectQid = mkQid "Mandela effect" "Q54765858"

falseMemoryQid : Identity.ExternalIdentityDemand
falseMemoryQid = mkQid "false memory" "Q2051704"

collectiveMemoryQid : Identity.ExternalIdentityDemand
collectiveMemoryQid = Collective.collectiveMemoryQid

fruitOfTheLoomQid : Identity.ExternalIdentityDemand
fruitOfTheLoomQid = mkQid "Fruit of the Loom" "Q765087"

religionQid : Identity.ExternalIdentityDemand
religionQid = mkQid "religion" "Q9174"

traditionalKnowledgeQid : Identity.ExternalIdentityDemand
traditionalKnowledgeQid = mkQid "traditional knowledge / Indigenous knowledge" "Q1428168"

traditionalEcologicalKnowledgeQid : Identity.ExternalIdentityDemand
traditionalEcologicalKnowledgeQid = mkQid "traditional ecological knowledge" "Q7832334"

robinWallKimmererQid : Identity.ExternalIdentityDemand
robinWallKimmererQid = mkQid "Robin Wall Kimmerer" "Q7352852"

braidingSweetgrassQid : Identity.ExternalIdentityDemand
braidingSweetgrassQid = mkQid "Braiding Sweetgrass" "Q85748689"

twoEyedSeeingQid : Identity.ExternalIdentityDemand
twoEyedSeeingQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Mandela/religion/Indigenous-memory/braiding BIDI"
  "external concept identity"
  "Etuaptmumk / Two-Eyed Seeing"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact general concept QID promoted in this pass; article-level QIDs are not substituted for the concept")

patternMindQid : Identity.ExternalIdentityDemand
patternMindQid = Identity.mkOptionalIdentityDemand
  "Ibrahim Mandela/religion/Indigenous-memory/braiding BIDI"
  "repo-local vocabulary"
  "PatternMind"
  Identity.wikidataQid
  (Identity.notApplicable
    "PatternMind is retained as repository-local relational repair-context vocabulary; no speculative external QID is assigned")

------------------------------------------------------------------------
-- Dewey coordinates.  Only exact inspected values are retained.
------------------------------------------------------------------------

religionDewey : Dewey.DeweyCoordinate
religionDewey = Dewey.mkVerifiedDewey
  "religion"
  "200"
  "Wikidata Q9174 DDC statement inspected 2026-09-11"

mandelaEffectDewey : Dewey.DeweyCoordinate
mandelaEffectDewey = Dewey.mkUnresolvedDewey
  "Mandela effect"
  "no exact inspected DDC value promoted in this pass"

falseMemoryDewey : Dewey.DeweyCoordinate
falseMemoryDewey = Dewey.mkUnresolvedDewey
  "false memory"
  "Q2051704 exposes LCC coordinates but no exact DDC value promoted here"

traditionalKnowledgeDewey : Dewey.DeweyCoordinate
traditionalKnowledgeDewey = Dewey.mkUnresolvedDewey
  "traditional / Indigenous knowledge"
  "no exact inspected DDC value promoted in this pass"

braidingSweetgrassDewey : Dewey.DeweyCoordinate
braidingSweetgrassDewey = Dewey.mkUnresolvedDewey
  "Braiding Sweetgrass"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI / canonical-source line.
------------------------------------------------------------------------

prasadBainbridgeMandelaSource : Attribution.AttributedSource
prasadBainbridgeMandelaSource = Attribution.mkDOISource
  "Deepasri Prasad; Wilma A. Bainbridge"
  "The Visual Mandela Effect as Evidence for Shared and Specific False Memories Across People"
  "Psychological Science 33(12), 1971-1988"
  "2022"
  "10.1177/09567976221108944"
  "https://doi.org/10.1177/09567976221108944"
  Attribution.academicArticleSource
  "experimental visual-memory work demonstrating shared specific false-memory errors for some popular icons; does not establish a paranormal mechanism or make every shared recollection false"
  Attribution.publicAttribution

maswoodRajaramSocialTransmissionSource : Attribution.AttributedSource
maswoodRajaramSocialTransmissionSource = Attribution.mkDOISource
  "Raeya Maswood; Suparna Rajaram"
  "Social Transmission of False Memory in Small Groups and Large Networks"
  "Topics in Cognitive Science 11(4), 687-709"
  "2019"
  "10.1111/tops.12348"
  "https://doi.org/10.1111/tops.12348"
  Attribution.academicArticleSource
  "review of social contagion, collaborative remembering and collective false-memory transmission; social transmission can carry accurate or inaccurate memory and therefore does not by itself determine truth"
  Attribution.publicAttribution

fruitOfficialHistorySource : Attribution.AttributedSource
fruitOfficialHistorySource = Attribution.mkNoDOISource
  "Fruit of the Loom"
  "Cornucopia and Michigan / Fruit of the Loom FAQs"
  "official company FAQ and logo-history response"
  "2026"
  "https://www.fruit.com/fotl-faqs"
  Attribution.institutionalSource
  "official current company claim that the registered Fruit Cluster logo never contained a cornucopia; bounded corporate/brand-history source requiring archival corroboration for exhaustive historical claims"
  Attribution.publicAttribution

norrisAboriginalAstronomySource : Attribution.AttributedSource
norrisAboriginalAstronomySource = Attribution.mkDOISource
  "Ray P. Norris"
  "Dawes Review 5: Australian Aboriginal Astronomy and Navigation"
  "Publications of the Astronomical Society of Australia 33, e039"
  "2016"
  "10.1017/pasa.2016.25"
  "https://doi.org/10.1017/pasa.2016.25"
  Attribution.academicArticleSource
  "review of Australian Aboriginal astronomical knowledge, oral tradition, ceremony, calendars and navigation; does not imply that every oral tradition is literal historical reportage or that all Aboriginal peoples share one knowledge system"
  Attribution.publicAttribution

bartlettTwoEyedSource : Attribution.AttributedSource
bartlettTwoEyedSource = Attribution.mkDOISource
  "Cheryl Bartlett; Murdena Marshall; Albert Marshall"
  "Two-Eyed Seeing and other lessons learned within a co-learning journey of bringing together indigenous and mainstream knowledges and ways of knowing"
  "Journal of Environmental Studies and Sciences 2, 331-340"
  "2012"
  "10.1007/s13412-012-0086-8"
  "https://doi.org/10.1007/s13412-012-0086-8"
  Attribution.academicArticleSource
  "source calibration for coordinated use of strengths from distinct knowledge systems without requiring fusion"
  Attribution.publicAttribution

kimmererBraidingSource : Attribution.AttributedSource
kimmererBraidingSource = Attribution.mkNoDOISource
  "Robin Wall Kimmerer"
  "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge, and the Teachings of Plants"
  "Milkweed Editions"
  "2013"
  "https://www.robinwallkimmerer.com/books"
  Attribution.academicBookSource
  "material inspiration for braid/reciprocity/obligation-bearing knowledge vocabulary; cultural and narrative source does not import formal theorem authority"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing repo-native carriers are reused rather than replaced.
------------------------------------------------------------------------

patternMindBoundary : PatternMind.PatternMindReciprocityLoveBridge
patternMindBoundary = PatternMind.canonicalPatternMindReciprocityLoveBridge

------------------------------------------------------------------------
-- Regression 1: collective agreement cannot recover historical truth.
------------------------------------------------------------------------

data SharedRecallCase : Set where
  sameSharedRecallHistoricallyPaid sameSharedRecallHistoricallyUnsupported : SharedRecallCase

data SharedRecallSurface : Set where sameSharedRecall : SharedRecallSurface
data HistoricalStatus : Set where historicalReceiptPaid historicalReceiptOpen : HistoricalStatus

sharedRecallSurface : SharedRecallCase → SharedRecallSurface
sharedRecallSurface _ = sameSharedRecall

historicalStatus : SharedRecallCase → HistoricalStatus
historicalStatus sameSharedRecallHistoricallyPaid = historicalReceiptPaid
historicalStatus sameSharedRecallHistoricallyUnsupported = historicalReceiptOpen

sharedRecallHistoryDefect : INF.NonFactorabilityWitness sharedRecallSurface historicalStatus
sharedRecallHistoryDefect = INF.nonFactorabilityWitness
  sameSharedRecallHistoricallyPaid sameSharedRecallHistoricallyUnsupported refl (λ ())

sharedRecallCannotFactorHistoricalTruth :
  INF.FactorsThrough sharedRecallSurface historicalStatus → ⊥
sharedRecallCannotFactorHistoricalTruth =
  INF.witnessRulesOutEveryFlatFactorisation sharedRecallHistoryDefect

------------------------------------------------------------------------
-- Regression 2: Mandela-effect label cannot recover the mechanism by which a
-- shared false recollection arose.
------------------------------------------------------------------------

data MandelaMechanismCase : Set where
  sameMandelaSurfaceSocialTransmission sameMandelaSurfaceConvergentReconstruction : MandelaMechanismCase

data MandelaSurface : Set where sameMandelaEffectClassification : MandelaSurface
data MemoryMechanism : Set where sociallyTransmittedMemory convergentReconstructiveMemory : MemoryMechanism

mandelaSurface : MandelaMechanismCase → MandelaSurface
mandelaSurface _ = sameMandelaEffectClassification

memoryMechanism : MandelaMechanismCase → MemoryMechanism
memoryMechanism sameMandelaSurfaceSocialTransmission = sociallyTransmittedMemory
memoryMechanism sameMandelaSurfaceConvergentReconstruction = convergentReconstructiveMemory

mandelaMechanismDefect : INF.NonFactorabilityWitness mandelaSurface memoryMechanism
mandelaMechanismDefect = INF.nonFactorabilityWitness
  sameMandelaSurfaceSocialTransmission sameMandelaSurfaceConvergentReconstruction refl (λ ())

mandelaLabelCannotFactorMechanism :
  INF.FactorsThrough mandelaSurface memoryMechanism → ⊥
mandelaLabelCannotFactorMechanism =
  INF.witnessRulesOutEveryFlatFactorisation mandelaMechanismDefect

------------------------------------------------------------------------
-- Regression 3: social transmission cannot decide epistemic role.  This is the
-- firewall preventing oral/traditional/religious transmission from being typed
-- as collective false memory merely because it is collectively transmitted.
------------------------------------------------------------------------

data TransmissionCase : Set where
  sameSocialTransmissionFalseMemory sameSocialTransmissionKnowledgeCarrier : TransmissionCase

data TransmissionSurface : Set where sameSociallyTransmittedSurface : TransmissionSurface
data EpistemicRole : Set where falseMemoryRole situatedKnowledgeCarrierRole : EpistemicRole

transmissionSurface : TransmissionCase → TransmissionSurface
transmissionSurface _ = sameSociallyTransmittedSurface

epistemicRole : TransmissionCase → EpistemicRole
epistemicRole sameSocialTransmissionFalseMemory = falseMemoryRole
epistemicRole sameSocialTransmissionKnowledgeCarrier = situatedKnowledgeCarrierRole

transmissionRoleDefect : INF.NonFactorabilityWitness transmissionSurface epistemicRole
transmissionRoleDefect = INF.nonFactorabilityWitness
  sameSocialTransmissionFalseMemory sameSocialTransmissionKnowledgeCarrier refl (λ ())

socialTransmissionCannotFactorEpistemicRole :
  INF.FactorsThrough transmissionSurface epistemicRole → ⊥
socialTransmissionCannotFactorEpistemicRole =
  INF.witnessRulesOutEveryFlatFactorisation transmissionRoleDefect

------------------------------------------------------------------------
-- Regression 4: religious/shared narrative cannot recover historical status.
-- Historical testing also cannot exhaust ritual, identity or relational meaning.
------------------------------------------------------------------------

data ReligiousNarrativeCase : Set where
  sameReligiousNarrativeHistoricalClaimPaid sameReligiousNarrativeHistoricalClaimOpen : ReligiousNarrativeCase

data ReligiousNarrativeSurface : Set where sameReligiousNarrative : ReligiousNarrativeSurface

religiousNarrativeSurface : ReligiousNarrativeCase → ReligiousNarrativeSurface
religiousNarrativeSurface _ = sameReligiousNarrative

religiousHistoricalStatus : ReligiousNarrativeCase → HistoricalStatus
religiousHistoricalStatus sameReligiousNarrativeHistoricalClaimPaid = historicalReceiptPaid
religiousHistoricalStatus sameReligiousNarrativeHistoricalClaimOpen = historicalReceiptOpen

religionHistoryDefect : INF.NonFactorabilityWitness religiousNarrativeSurface religiousHistoricalStatus
religionHistoryDefect = INF.nonFactorabilityWitness
  sameReligiousNarrativeHistoricalClaimPaid sameReligiousNarrativeHistoricalClaimOpen refl (λ ())

religiousNarrativeCannotFactorHistoricalTruth :
  INF.FactorsThrough religiousNarrativeSurface religiousHistoricalStatus → ⊥
religiousNarrativeCannotFactorHistoricalTruth =
  INF.witnessRulesOutEveryFlatFactorisation religionHistoryDefect

------------------------------------------------------------------------
-- Regression 5: a flattened story/claim surface cannot recover the richer
-- Indigenous knowledge carrier role preserved by the existing Two-Eyed owner.
------------------------------------------------------------------------

data StoryCarrierCase : Set where
  sameStorySurfaceDetachedClaim sameStorySurfaceSituatedCarrier : StoryCarrierCase

data StorySurface : Set where samePublicStorySurface : StorySurface
data CarrierRole : Set where detachedClaimRole situatedRelationalCarrierRole : CarrierRole

storySurface : StoryCarrierCase → StorySurface
storySurface _ = samePublicStorySurface

carrierRole : StoryCarrierCase → CarrierRole
carrierRole sameStorySurfaceDetachedClaim = detachedClaimRole
carrierRole sameStorySurfaceSituatedCarrier = situatedRelationalCarrierRole

storyCarrierDefect : INF.NonFactorabilityWitness storySurface carrierRole
storyCarrierDefect = INF.nonFactorabilityWitness
  sameStorySurfaceDetachedClaim sameStorySurfaceSituatedCarrier refl (λ ())

storySurfaceCannotFactorKnowledgeCarrierRole :
  INF.FactorsThrough storySurface carrierRole → ⊥
storySurfaceCannotFactorKnowledgeCarrierRole =
  INF.witnessRulesOutEveryFlatFactorisation storyCarrierDefect

------------------------------------------------------------------------
-- Fruit of the Loom case receipt: memory report and historical logo record stay
-- separate.  Current official corporate evidence is not treated as exhaustive
-- archival proof by itself.
------------------------------------------------------------------------

record FruitCornucopiaCaseReceipt : Set where
  constructor fruit-cornucopia-case-receipt
  field
    companyIdentityPaid : Bool
    sharedCornucopiaRecollectionObservedAsPublicPhenomenon : Bool
    officialCurrentCompanyDenialRetained : Bool
    visualMandelaResearchRelevant : Bool
    archivedTrademarkLogoHistoryStillOwnsHistoricalAudit : Bool
    sharedRecollectionCreatesHistoricalLogoFact : Bool
    companyFaqAloneExhaustsEveryHistoricalArtifact : Bool
open FruitCornucopiaCaseReceipt public

canonicalFruitCornucopiaCaseReceipt : FruitCornucopiaCaseReceipt
canonicalFruitCornucopiaCaseReceipt =
  fruit-cornucopia-case-receipt
    true true true true true false false

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parents.
------------------------------------------------------------------------

record CollectiveMemoryReverseConstraint : Set where
  constructor collective-memory-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open CollectiveMemoryReverseConstraint public

memoryConstraint : CollectiveMemoryReverseConstraint
memoryConstraint = collective-memory-reverse-constraint
  "Memory / learning / trauma hyperfabric"
  "remembered content, latent memory state, source monitoring, social transmission, confidence and truth remain distinct"
  false

religionConstraint : CollectiveMemoryReverseConstraint
religionConstraint = collective-memory-reverse-constraint
  "Religion / ritual / collective identity"
  "shared narrative, historical proposition, ritual meaning, identity, doctrine, authority and community transmission remain distinct"
  false

indigenousKnowledgeConstraint : CollectiveMemoryReverseConstraint
indigenousKnowledgeConstraint = collective-memory-reverse-constraint
  "Indigenous / traditional knowledge"
  "content, place, people relation, practice, time, provenance, custodial authority, permission, obligation and transmission mode remain distinct"
  false

braidingConstraint : CollectiveMemoryReverseConstraint
braidingConstraint = collective-memory-reverse-constraint
  "Braiding Sweetgrass / Two-Eyed Seeing / PatternMind"
  "braiding coordinates distinct knowledge histories without fusing provenance; repeated attention and reciprocity are relational carriers, not truth shortcuts"
  false

australianIndigenousConstraint : CollectiveMemoryReverseConstraint
australianIndigenousConstraint = collective-memory-reverse-constraint
  "Australian Indigenous knowledge / Country / oral tradition"
  "oral story, song, ceremony, navigation, observation, custodial standing, Country relation and externally testable proposition remain separately recoverable"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SharedMemoryMeansTruth : Set where
data SharedMemoryMeansFalsehood : Set where
data SocialTransmissionMeansMandelaEffect : Set where
data OralTraditionMeansFalseMemory : Set where
data ReligionMeansHistoricalTruth : Set where
data HistoricalAuditErasesReligiousMeaning : Set where
data IndigenousKnowledgeMeansUniversalOntology : Set where
data PatternMindIsUniversalIndigenousOntology : Set where
data TwoEyedSeeingMeansFusion : Set where
data FruitMemoryMeansCornucopiaHistoricalFact : Set where

sharedMemoryDoesNotCreateTruth : SharedMemoryMeansTruth → ⊥
sharedMemoryDoesNotCreateTruth ()

sharedMemoryDoesNotCreateFalsehood : SharedMemoryMeansFalsehood → ⊥
sharedMemoryDoesNotCreateFalsehood ()

socialTransmissionDoesNotCreateMandelaEffect : SocialTransmissionMeansMandelaEffect → ⊥
socialTransmissionDoesNotCreateMandelaEffect ()

oralTraditionDoesNotCreateFalseMemory : OralTraditionMeansFalseMemory → ⊥
oralTraditionDoesNotCreateFalseMemory ()

religionDoesNotCreateHistoricalTruth : ReligionMeansHistoricalTruth → ⊥
religionDoesNotCreateHistoricalTruth ()

historicalAuditDoesNotEraseReligiousMeaning : HistoricalAuditErasesReligiousMeaning → ⊥
historicalAuditDoesNotEraseReligiousMeaning ()

indigenousKnowledgeDoesNotCreateUniversalOntology : IndigenousKnowledgeMeansUniversalOntology → ⊥
indigenousKnowledgeDoesNotCreateUniversalOntology ()

patternMindDoesNotBecomeUniversalIndigenousOntology : PatternMindIsUniversalIndigenousOntology → ⊥
patternMindDoesNotBecomeUniversalIndigenousOntology ()

twoEyedSeeingDoesNotRequireFusion : TwoEyedSeeingMeansFusion → ⊥
twoEyedSeeingDoesNotRequireFusion ()

fruitMemoryDoesNotCreateHistoricalLogoFact : FruitMemoryMeansCornucopiaHistoricalFact → ⊥
fruitMemoryDoesNotCreateHistoricalLogoFact ()

record MandelaReligionIndigenousMemoryBraidingBoundary : Set where
  constructor mandela-religion-indigenous-memory-braiding-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyUnresolvedRetainedExplicitly : Bool
    doiAndCanonicalSourcesRetained : Bool
    collectiveAgreementSeparatedFromHistoricalTruth : Bool
    mandelaLabelSeparatedFromMemoryMechanism : Bool
    socialTransmissionSeparatedFromEpistemicRole : Bool
    religionMeaningSeparatedFromHistoricalAudit : Bool
    indigenousKnowledgeSeparatedFromFalseMemoryTyping : Bool
    twoEyedCoordinationPreservesDistinctProvenance : Bool
    patternMindRetainedAsRepoLocalVocabulary : Bool
    fruitOfLoomCaseBoundedToSourcePaidEvidence : Bool
    australianIndigenousKnowledgeNotUniversalised : Bool
    presentAxisVocabularyClaimedComplete : Bool
open MandelaReligionIndigenousMemoryBraidingBoundary public

canonicalMandelaReligionIndigenousMemoryBraidingBoundary :
  MandelaReligionIndigenousMemoryBraidingBoundary
canonicalMandelaReligionIndigenousMemoryBraidingBoundary =
  mandela-religion-indigenous-memory-braiding-boundary
    true true true true true true true true true true true true false

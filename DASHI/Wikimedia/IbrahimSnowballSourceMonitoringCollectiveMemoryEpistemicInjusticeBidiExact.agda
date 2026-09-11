module DASHI.Wikimedia.IbrahimSnowballSourceMonitoringCollectiveMemoryEpistemicInjusticeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.VocabularyProvenanceExact as Vocabulary
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballKnowledgeCultureHistoryFrontierExact as KnowledgeHistory

------------------------------------------------------------------------
-- IBRAHIM / SOURCE-MONITORING / COLLECTIVE-MEMORY / EPISTEMIC-INJUSTICE BIDI
--
-- This owner fills a missing seam between the repo's versioned memory/testimony
-- machinery, source-dependency/consensus work, history/culture traversal and
-- Fricker-calibrated vocabulary-provenance boundary.
--
-- Remembered content, remembered source, social circulation, collective-memory
-- status, credibility allocation, hermeneutical resources and proposition truth
-- remain different consumers.  The finite witnesses below are DASHI
-- constructions; the cited sources motivate distinctions rather than importing
-- theorem authority.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim source-monitoring/collective-memory/epistemic-injustice BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create source attribution, collective agreement, credibility justice, historical truth or authority")

collectiveMemoryQid : Identity.ExternalIdentityDemand
collectiveMemoryQid = mkQid "collective memory" "Q254217"

epistemicInjusticeQid : Identity.ExternalIdentityDemand
epistemicInjusticeQid = mkQid "epistemic injustice" "Q48970669"

sourceMonitoringQid : Identity.ExternalIdentityDemand
sourceMonitoringQid = Identity.mkOptionalIdentityDemand
  "Ibrahim source-monitoring/collective-memory/epistemic-injustice BIDI"
  "external concept identity"
  "source monitoring in memory"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact standalone source-monitoring QID promoted in this pass; concept is source-paid by Johnson/Hashtroudi/Lindsay 1993")

testimonialInjusticeQid : Identity.ExternalIdentityDemand
testimonialInjusticeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim source-monitoring/collective-memory/epistemic-injustice BIDI"
  "external concept identity"
  "testimonial injustice"
  Identity.wikidataQid
  (Identity.unresolved
    "epistemic injustice Q48970669 is paid; no narrower same-object QID promoted here")

hermeneuticalInjusticeQid : Identity.ExternalIdentityDemand
hermeneuticalInjusticeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim source-monitoring/collective-memory/epistemic-injustice BIDI"
  "external concept identity"
  "hermeneutical injustice"
  Identity.wikidataQid
  (Identity.unresolved
    "epistemic injustice Q48970669 is paid; no narrower same-object QID promoted here")

------------------------------------------------------------------------
-- Dewey stays navigation-only.  No nearby psychology/sociology/philosophy shelf
-- is promoted without an exact inspected DDC statement.
------------------------------------------------------------------------

collectiveMemoryDewey : Dewey.DeweyCoordinate
collectiveMemoryDewey = Dewey.mkUnresolvedDewey
  "collective memory"
  "no exact inspected DDC value promoted in this pass"

sourceMonitoringDewey : Dewey.DeweyCoordinate
sourceMonitoringDewey = Dewey.mkUnresolvedDewey
  "source monitoring"
  "no exact inspected DDC value promoted in this pass"

epistemicInjusticeDewey : Dewey.DeweyCoordinate
epistemicInjusticeDewey = Dewey.mkUnresolvedDewey
  "epistemic injustice"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI/source line.
------------------------------------------------------------------------

johnsonSourceMonitoringSource : Attribution.AttributedSource
johnsonSourceMonitoringSource = Attribution.mkDOISource
  "Marcia K. Johnson; Shahin Hashtroudi; D. Stephen Lindsay"
  "Source monitoring"
  "Psychological Bulletin 114(1), 3-28"
  "1993"
  "10.1037/0033-2909.114.1.3"
  "https://doi.org/10.1037/0033-2909.114.1.3"
  Attribution.academicArticleSource
  "source-monitoring framework for judgments about origins of remembered information; source-attribution fallibility does not imply that every memory is false"
  Attribution.publicAttribution

wertschRoedigerCollectiveMemorySource : Attribution.AttributedSource
wertschRoedigerCollectiveMemorySource = Attribution.mkDOISource
  "James V. Wertsch; Henry L. Roediger III"
  "Collective memory: conceptual foundations and theoretical approaches"
  "Memory 16(3), 318-326"
  "2008"
  "10.1080/09658210701801434"
  "https://doi.org/10.1080/09658210701801434"
  Attribution.academicArticleSource
  "review of collective-memory concepts and mechanisms; collective memory is not identified with one individual's autobiographical memory or with historical truth"
  Attribution.publicAttribution

olickRobbinsSocialMemorySource : Attribution.AttributedSource
olickRobbinsSocialMemorySource = Attribution.mkDOISource
  "Jeffrey K. Olick; Joyce Robbins"
  "Social Memory Studies: From Collective Memory to the Historical Sociology of Mnemonic Practices"
  "Annual Review of Sociology 24, 105-140"
  "1998"
  "10.1146/annurev.soc.24.1.105"
  "https://doi.org/10.1146/annurev.soc.24.1.105"
  Attribution.academicArticleSource
  "maps the heterogeneous social-memory field and mnemonic practices; social circulation/history is not collapsed into individual cognitive storage"
  Attribution.publicAttribution

frickerEpistemicInjusticeSource : Attribution.AttributedSource
frickerEpistemicInjusticeSource = Attribution.mkDOISource
  "Miranda Fricker"
  "Epistemic Injustice: Power and the Ethics of Knowing"
  "Oxford University Press"
  "2007"
  "10.1093/acprof:oso/9780198237907.001.0001"
  "https://doi.org/10.1093/acprof:oso/9780198237907.001.0001"
  Attribution.academicBookSource
  "conceptual provenance for testimonial and hermeneutical injustice; finite nonfactorability witnesses and any case application remain separately owned by DASHI/source evidence"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact upstream boundaries reused.
------------------------------------------------------------------------

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

vocabularyAuthorityBoundary : Vocabulary.EpistemicAuthorityBoundary
vocabularyAuthorityBoundary = Vocabulary.canonicalEpistemicAuthorityBoundary

knowledgeHistoryBoundary : KnowledgeHistory.FrontierSnowballBoundary
knowledgeHistoryBoundary = KnowledgeHistory.canonicalFrontierSnowballBoundary

------------------------------------------------------------------------
-- Regression 1: remembered content cannot recover remembered source.
------------------------------------------------------------------------

data SourceMemoryCase : Set where
  sameRememberedContentDirectExperience sameRememberedContentSociallyAcquired : SourceMemoryCase

data RememberedContentSurface : Set where sameRememberedContent : RememberedContentSurface
data RememberedSource : Set where directExperienceSource sociallyAcquiredSource : RememberedSource

rememberedContentSurface : SourceMemoryCase → RememberedContentSurface
rememberedContentSurface _ = sameRememberedContent

rememberedSource : SourceMemoryCase → RememberedSource
rememberedSource sameRememberedContentDirectExperience = directExperienceSource
rememberedSource sameRememberedContentSociallyAcquired = sociallyAcquiredSource

sourceMonitoringDefect : INF.NonFactorabilityWitness rememberedContentSurface rememberedSource
sourceMonitoringDefect = INF.nonFactorabilityWitness
  sameRememberedContentDirectExperience sameRememberedContentSociallyAcquired refl (λ ())

rememberedContentCannotFactorRememberedSource :
  INF.FactorsThrough rememberedContentSurface rememberedSource → ⊥
rememberedContentCannotFactorRememberedSource =
  INF.witnessRulesOutEveryFlatFactorisation sourceMonitoringDefect

------------------------------------------------------------------------
-- Regression 2: collective/public narrative cannot recover member-level memory
-- origin or independence.
------------------------------------------------------------------------

data CollectiveCase : Set where
  samePublicNarrativeIndependentMemories samePublicNarrativeCommonCirculation : CollectiveCase

data CollectiveSurface : Set where sameCollectiveNarrative : CollectiveSurface
data MemberOrigin : Set where independentlyRemembered commonSocialCirculation : MemberOrigin

collectiveSurface : CollectiveCase → CollectiveSurface
collectiveSurface _ = sameCollectiveNarrative

memberOrigin : CollectiveCase → MemberOrigin
memberOrigin samePublicNarrativeIndependentMemories = independentlyRemembered
memberOrigin samePublicNarrativeCommonCirculation = commonSocialCirculation

collectiveOriginDefect : INF.NonFactorabilityWitness collectiveSurface memberOrigin
collectiveOriginDefect = INF.nonFactorabilityWitness
  samePublicNarrativeIndependentMemories samePublicNarrativeCommonCirculation refl (λ ())

collectiveNarrativeCannotFactorMemberOrigin :
  INF.FactorsThrough collectiveSurface memberOrigin → ⊥
collectiveNarrativeCannotFactorMemberOrigin =
  INF.witnessRulesOutEveryFlatFactorisation collectiveOriginDefect

------------------------------------------------------------------------
-- Regression 3: report/evidence content cannot recover credibility treatment.
-- This is a structural calibration for testimonial-injustice audits; it does
-- not declare either finite state to instantiate a real-world injustice.
------------------------------------------------------------------------

data CredibilityTreatmentCase : Set where
  sameEvidenceCredibilityUptakeA sameEvidenceCredibilityUptakeB : CredibilityTreatmentCase

data EvidenceContentSurface : Set where sameEvidenceContent : EvidenceContentSurface
data CredibilityUptake : Set where credibilityUptakeA credibilityUptakeB : CredibilityUptake

evidenceContentSurface : CredibilityTreatmentCase → EvidenceContentSurface
evidenceContentSurface _ = sameEvidenceContent

credibilityUptake : CredibilityTreatmentCase → CredibilityUptake
credibilityUptake sameEvidenceCredibilityUptakeA = credibilityUptakeA
credibilityUptake sameEvidenceCredibilityUptakeB = credibilityUptakeB

credibilityTreatmentDefect : INF.NonFactorabilityWitness evidenceContentSurface credibilityUptake
credibilityTreatmentDefect = INF.nonFactorabilityWitness
  sameEvidenceCredibilityUptakeA sameEvidenceCredibilityUptakeB refl (λ ())

evidenceContentCannotFactorCredibilityTreatment :
  INF.FactorsThrough evidenceContentSurface credibilityUptake → ⊥
evidenceContentCannotFactorCredibilityTreatment =
  INF.witnessRulesOutEveryFlatFactorisation credibilityTreatmentDefect

------------------------------------------------------------------------
-- Regression 4: shared collective memory cannot recover historical truth.
------------------------------------------------------------------------

data CollectiveTruthCase : Set where
  sameCollectiveMemoryHistoricallySupported sameCollectiveMemoryHistoricallyUnsupported : CollectiveTruthCase

data CollectiveMemorySurface : Set where sameCollectiveMemory : CollectiveMemorySurface
data HistoricalTruthStatus : Set where historicalSupportPaid historicalSupportOpen : HistoricalTruthStatus

collectiveMemorySurface : CollectiveTruthCase → CollectiveMemorySurface
collectiveMemorySurface _ = sameCollectiveMemory

historicalTruthStatus : CollectiveTruthCase → HistoricalTruthStatus
historicalTruthStatus sameCollectiveMemoryHistoricallySupported = historicalSupportPaid
historicalTruthStatus sameCollectiveMemoryHistoricallyUnsupported = historicalSupportOpen

collectiveTruthDefect : INF.NonFactorabilityWitness collectiveMemorySurface historicalTruthStatus
collectiveTruthDefect = INF.nonFactorabilityWitness
  sameCollectiveMemoryHistoricallySupported sameCollectiveMemoryHistoricallyUnsupported refl (λ ())

collectiveMemoryCannotFactorHistoricalTruth :
  INF.FactorsThrough collectiveMemorySurface historicalTruthStatus → ⊥
collectiveMemoryCannotFactorHistoricalTruth =
  INF.witnessRulesOutEveryFlatFactorisation collectiveTruthDefect

------------------------------------------------------------------------
-- Regression 5: available public vocabulary cannot recover whether a person or
-- community has an experience/knowledge relation that the vocabulary fails to
-- represent.  This is a hermeneutical-resource audit, not automatic diagnosis
-- of hermeneutical injustice.
------------------------------------------------------------------------

data VocabularyCase : Set where
  samePublicVocabularyExperienceRepresentable samePublicVocabularyExperiencePoorlyRepresented : VocabularyCase

data PublicVocabularySurface : Set where samePublicVocabulary : PublicVocabularySurface
data InterpretiveResourceFit : Set where representableWithAvailableTerms interpretiveGapRemains : InterpretiveResourceFit

publicVocabularySurface : VocabularyCase → PublicVocabularySurface
publicVocabularySurface _ = samePublicVocabulary

interpretiveResourceFit : VocabularyCase → InterpretiveResourceFit
interpretiveResourceFit samePublicVocabularyExperienceRepresentable = representableWithAvailableTerms
interpretiveResourceFit samePublicVocabularyExperiencePoorlyRepresented = interpretiveGapRemains

hermeneuticalResourceDefect : INF.NonFactorabilityWitness publicVocabularySurface interpretiveResourceFit
hermeneuticalResourceDefect = INF.nonFactorabilityWitness
  samePublicVocabularyExperienceRepresentable samePublicVocabularyExperiencePoorlyRepresented refl (λ ())

publicVocabularyCannotFactorInterpretiveResourceFit :
  INF.FactorsThrough publicVocabularySurface interpretiveResourceFit → ⊥
publicVocabularyCannotFactorInterpretiveResourceFit =
  INF.witnessRulesOutEveryFlatFactorisation hermeneuticalResourceDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record SourceCollectiveJusticeReverseConstraint : Set where
  constructor source-collective-justice-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SourceCollectiveJusticeReverseConstraint public

memoryConstraint : SourceCollectiveJusticeReverseConstraint
memoryConstraint = source-collective-justice-reverse-constraint
  "Memory / cognition"
  "remembered content, source attribution, confidence, retrieval context, post-event information and report remain distinct"
  false

historyCultureConstraint : SourceCollectiveJusticeReverseConstraint
historyCultureConstraint = source-collective-justice-reverse-constraint
  "History / culture / collective memory"
  "shared narrative, social circulation, mnemonic institution/artifact, member-level memory origin, source genealogy and historical truth remain distinct"
  false

epistemicJusticeConstraint : SourceCollectiveJusticeReverseConstraint
epistemicJusticeConstraint = source-collective-justice-reverse-constraint
  "Epistemic justice / testimony / vocabulary"
  "report content, speaker/source position, credibility allocation, uptake, available interpretive resources and proposition truth remain distinct"
  false

mediaInstitutionConstraint : SourceCollectiveJusticeReverseConstraint
mediaInstitutionConstraint = source-collective-justice-reverse-constraint
  "Media / institutions / knowledge transmission"
  "repetition, public salience, algorithmic/institutional circulation, common-source dependence and independent corroboration remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SameMemoryContentMeansSameSource : Set where
data CollectiveMemoryMeansIndependentMemory : Set where
data CollectiveMemoryMeansHistoricalTruth : Set where
data CredibilityTreatmentMeansTruth : Set where
data PublicVocabularyExhaustsExperience : Set where
data EpistemicInjusticeQidProvesCase : Set where

sameMemoryContentDoesNotCreateSameSource : SameMemoryContentMeansSameSource → ⊥
sameMemoryContentDoesNotCreateSameSource ()

collectiveMemoryDoesNotCreateIndependence : CollectiveMemoryMeansIndependentMemory → ⊥
collectiveMemoryDoesNotCreateIndependence ()

collectiveMemoryDoesNotCreateHistoricalTruth : CollectiveMemoryMeansHistoricalTruth → ⊥
collectiveMemoryDoesNotCreateHistoricalTruth ()

credibilityTreatmentDoesNotCreateTruth : CredibilityTreatmentMeansTruth → ⊥
credibilityTreatmentDoesNotCreateTruth ()

publicVocabularyDoesNotExhaustExperience : PublicVocabularyExhaustsExperience → ⊥
publicVocabularyDoesNotExhaustExperience ()

epistemicInjusticeQidDoesNotProveCase : EpistemicInjusticeQidProvesCase → ⊥
epistemicInjusticeQidDoesNotProveCase ()

record SourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary : Set where
  constructor source-monitoring-collective-memory-epistemic-injustice-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedSpecificQidsRetained : Bool
    deweyUnresolvedRetainedExplicitly : Bool
    doiAndSourceRoleRetained : Bool
    sourceMonitoringSeparatedFromRememberedContent : Bool
    collectiveNarrativeSeparatedFromMemberOrigin : Bool
    collectiveMemorySeparatedFromHistoricalTruth : Bool
    credibilityTreatmentSeparatedFromEvidenceContent : Bool
    interpretiveResourcesSeparatedFromExperience : Bool
    frickerVocabularyBoundaryReused : Bool
    sourceDependencyBoundaryReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary public

canonicalSourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary :
  SourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary
canonicalSourceMonitoringCollectiveMemoryEpistemicInjusticeBoundary =
  source-monitoring-collective-memory-epistemic-injustice-boundary
    true true true true true true true true true true true true false

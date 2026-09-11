module DASHI.Wikimedia.IbrahimSnowballEvidenceDependencyReplicationConsensusBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as Media
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as WitchTrial

------------------------------------------------------------------------
-- IBRAHIM / EVIDENCE-DEPENDENCY / REPLICATION-CONSENSUS BIDI
--
-- Repetition is not independence.  This owner quotients repeated evidence by
-- provenance dependency before a consumer treats multiplicity as corroboration.
-- The same pattern applies to generated testimony, repeated memory reports,
-- multiple effect sizes from one study/sample, copied journalism, OSINT reposts,
-- and consensus summaries.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-dependency/replication/consensus BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create independence, effective sample size, replication quality, consensus truth or source authority")

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

replicationCrisisQid : Identity.ExternalIdentityDemand
replicationCrisisQid = mkQid "replication crisis" "Q25303778"

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = Prior.reproducibilityQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = Prior.scientificConsensusQid

commonSourceDependenceQid : Identity.ExternalIdentityDemand
commonSourceDependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-dependency/replication/consensus BIDI"
  "external concept identity"
  "evidence dependence / common-source dependence / provenance dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single Wikidata concept promoted for general evidential dependency across testimony, science, media and OSINT")

------------------------------------------------------------------------
-- Dewey: exact only where inspected.
------------------------------------------------------------------------

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkVerifiedDewey
  "meta-analysis"
  "519.53"
  "Wikidata Q815382 DDC statement inspected 2026-09-11"

replicationCrisisDewey : Dewey.DeweyCoordinate
replicationCrisisDewey = Dewey.mkUnresolvedDewey
  "replication crisis"
  "inspected Wikidata Q25303778 supplies LCC Q175.37 but no DDC value; do not convert classification systems"

commonSourceDependenceDewey : Dewey.DeweyCoordinate
commonSourceDependenceDewey = Dewey.mkUnresolvedDewey
  "evidence dependency / common-source dependence"
  "no exact inspected DDC value promoted"

------------------------------------------------------------------------
-- DOI/source atlas.
------------------------------------------------------------------------

pilditchDependencySource : Attribution.AttributedSource
pilditchDependencySource = Attribution.mkDOISource
  "Toby D. Pilditch; Ulrike Hahn; David Lagnado"
  "The problem of dependency"
  "Synthese 205, 143"
  "2025"
  "10.1007/s11229-025-04969-w"
  "https://doi.org/10.1007/s11229-025-04969-w"
  Attribution.academicArticleSource
  "formal/experimental treatment of evidential dependency across multiple pieces of evidence including testimony and measurement; supports retaining dependence structure rather than counting evidence pieces as independent votes"
  Attribution.publicAttribution

cheungNonIndependentMetaSource : Attribution.AttributedSource
cheungNonIndependentMetaSource = Attribution.mkDOISource
  "Mike W.-L. Cheung"
  "A Guide to Conducting a Meta-Analysis with Non-Independent Effect Sizes"
  "Neuropsychology Review 29, 387-396"
  "2019"
  "10.1007/s11065-019-09415-6"
  "https://doi.org/10.1007/s11065-019-09415-6"
  Attribution.academicArticleSource
  "methodological review showing that treating non-independent effect sizes as independent can distort uncertainty and inference; dependence must be modeled rather than erased"
  Attribution.publicAttribution

songEcologyDependenceSource : Attribution.AttributedSource
songEcologyDependenceSource = Attribution.mkDOISource
  "Chao Song; Scott D. Peacor; et al."
  "An assessment of statistical methods for nonindependent data in ecological meta-analyses"
  "Ecology 101(12), e03184"
  "2020"
  "10.1002/ecy.3184"
  "https://doi.org/10.1002/ecy.3184"
  Attribution.academicArticleSource
  "simulation/method study of within-paper nonindependence in ecological meta-analysis; source role is methodological calibration, not a universal weighting theorem for every evidence domain"
  Attribution.publicAttribution

hertzumJournalismSources : Attribution.AttributedSource
hertzumJournalismSources = Attribution.mkDOISource
  "Morten Hertzum"
  "How do journalists seek information from sources? A systematic review"
  "Information Processing & Management 59(6), 103087"
  "2022"
  "10.1016/j.ipm.2022.103087"
  "https://doi.org/10.1016/j.ipm.2022.103087"
  Attribution.academicArticleSource
  "systematic review of journalistic source seeking and source balancing; motivates source-genealogy audits for apparent multi-outlet corroboration without asserting that all media repetition is dependent"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- A tiny dependency quotient carrier.
------------------------------------------------------------------------

data DependencyClass : Set where
  independentOrigin commonOrigin unknownOrigin : DependencyClass

record EvidenceItem : Set where
  constructor evidence-item
  field
    itemLabel : String
    provenanceLabel : String
    dependencyClass : DependencyClass
open EvidenceItem public

record DependencyAudit : Set where
  constructor dependency-audit
  field
    observedItemCount : Nat
    provenanceComponentCount : Nat
    independencePaid : Bool
    unresolvedDependencyRetained : Bool
open DependencyAudit public

------------------------------------------------------------------------
-- Regression 1: raw multiplicity cannot recover provenance independence.
------------------------------------------------------------------------

data MultiplicityCase : Set where
  sameCountIndependentOrigins sameCountCommonOrigin : MultiplicityCase

data MultiplicitySurface : Set where sameEvidenceCount : MultiplicitySurface

data IndependenceState : Set where independencePaid commonSourceDependent : IndependenceState

multiplicitySurface : MultiplicityCase → MultiplicitySurface
multiplicitySurface _ = sameEvidenceCount

independenceState : MultiplicityCase → IndependenceState
independenceState sameCountIndependentOrigins = independencePaid
independenceState sameCountCommonOrigin = commonSourceDependent

multiplicityDependencyDefect : INF.NonFactorabilityWitness multiplicitySurface independenceState
multiplicityDependencyDefect = INF.nonFactorabilityWitness
  sameCountIndependentOrigins sameCountCommonOrigin refl (λ ())

rawMultiplicityCannotFactorIndependence :
  INF.FactorsThrough multiplicitySurface independenceState → ⊥
rawMultiplicityCannotFactorIndependence =
  INF.witnessRulesOutEveryFlatFactorisation multiplicityDependencyDefect

------------------------------------------------------------------------
-- Regression 2: publication/effect-size count cannot recover effective evidence.
------------------------------------------------------------------------

data MetaCase : Set where
  samePublishedCountIndependentSamples samePublishedCountSharedSample : MetaCase

data PublishedSurface : Set where samePublishedMultiplicity : PublishedSurface
data EffectiveEvidence : Set where moreIndependentInformation lessIndependentInformation : EffectiveEvidence

publishedSurface : MetaCase → PublishedSurface
publishedSurface _ = samePublishedMultiplicity

effectiveEvidence : MetaCase → EffectiveEvidence
effectiveEvidence samePublishedCountIndependentSamples = moreIndependentInformation
effectiveEvidence samePublishedCountSharedSample = lessIndependentInformation

metaDependenceDefect : INF.NonFactorabilityWitness publishedSurface effectiveEvidence
metaDependenceDefect = INF.nonFactorabilityWitness
  samePublishedCountIndependentSamples samePublishedCountSharedSample refl (λ ())

publicationCountCannotFactorEffectiveIndependentEvidence :
  INF.FactorsThrough publishedSurface effectiveEvidence → ⊥
publicationCountCannotFactorEffectiveIndependentEvidence =
  INF.witnessRulesOutEveryFlatFactorisation metaDependenceDefect

------------------------------------------------------------------------
-- Regression 3: media outlet count cannot recover source diversity.
------------------------------------------------------------------------

data MediaCase : Set where
  sameOutletCountDistinctSources sameOutletCountCopiedSource : MediaCase

data OutletSurface : Set where sameOutletMultiplicity : OutletSurface
data SourceDiversity : Set where diversePrimarySources copiedOrCommonSource : SourceDiversity

outletSurface : MediaCase → OutletSurface
outletSurface _ = sameOutletMultiplicity

sourceDiversity : MediaCase → SourceDiversity
sourceDiversity sameOutletCountDistinctSources = diversePrimarySources
sourceDiversity sameOutletCountCopiedSource = copiedOrCommonSource

mediaDependencyDefect : INF.NonFactorabilityWitness outletSurface sourceDiversity
mediaDependencyDefect = INF.nonFactorabilityWitness
  sameOutletCountDistinctSources sameOutletCountCopiedSource refl (λ ())

outletCountCannotFactorSourceDiversity :
  INF.FactorsThrough outletSurface sourceDiversity → ⊥
outletCountCannotFactorSourceDiversity =
  INF.witnessRulesOutEveryFlatFactorisation mediaDependencyDefect

------------------------------------------------------------------------
-- Regression 4: repeated retrieval/report from one memory lineage is not
-- automatically independent corroboration.
------------------------------------------------------------------------

data RetrievalCase : Set where
  sameReportCountIndependentPeople sameReportCountRepeatedRetrieval : RetrievalCase

data RetrievalCountSurface : Set where sameReportMultiplicity : RetrievalCountSurface
data CorroborativeStatus : Set where corroborativeIndependent repeatedSameLineage : CorroborativeStatus

retrievalCountSurface : RetrievalCase → RetrievalCountSurface
retrievalCountSurface _ = sameReportMultiplicity

corroborativeStatus : RetrievalCase → CorroborativeStatus
corroborativeStatus sameReportCountIndependentPeople = corroborativeIndependent
corroborativeStatus sameReportCountRepeatedRetrieval = repeatedSameLineage

retrievalDependencyDefect : INF.NonFactorabilityWitness retrievalCountSurface corroborativeStatus
retrievalDependencyDefect = INF.nonFactorabilityWitness
  sameReportCountIndependentPeople sameReportCountRepeatedRetrieval refl (λ ())

repeatedReportCountCannotFactorIndependentCorroboration :
  INF.FactorsThrough retrievalCountSurface corroborativeStatus → ⊥
repeatedReportCountCannotFactorIndependentCorroboration =
  INF.witnessRulesOutEveryFlatFactorisation retrievalDependencyDefect

------------------------------------------------------------------------
-- Regression 5: consensus size cannot recover dependency quality of its basis.
------------------------------------------------------------------------

data ConsensusDependencyCase : Set where
  sameConsensusBreadthIndependentBase sameConsensusBreadthDependentBase : ConsensusDependencyCase

data ConsensusBreadthSurface : Set where sameConsensusBreadth : ConsensusBreadthSurface
data EvidenceBaseQuality : Set where independentlySupportedBase dependenceHeavyBase : EvidenceBaseQuality

consensusBreadthSurface : ConsensusDependencyCase → ConsensusBreadthSurface
consensusBreadthSurface _ = sameConsensusBreadth

evidenceBaseQuality : ConsensusDependencyCase → EvidenceBaseQuality
evidenceBaseQuality sameConsensusBreadthIndependentBase = independentlySupportedBase
evidenceBaseQuality sameConsensusBreadthDependentBase = dependenceHeavyBase

consensusDependencyDefect : INF.NonFactorabilityWitness consensusBreadthSurface evidenceBaseQuality
consensusDependencyDefect = INF.nonFactorabilityWitness
  sameConsensusBreadthIndependentBase sameConsensusBreadthDependentBase refl (λ ())

consensusBreadthCannotFactorEvidenceBaseIndependence :
  INF.FactorsThrough consensusBreadthSurface evidenceBaseQuality → ⊥
consensusBreadthCannotFactorEvidenceBaseIndependence =
  INF.witnessRulesOutEveryFlatFactorisation consensusDependencyDefect

------------------------------------------------------------------------
-- Exact reuse of existing owners.
------------------------------------------------------------------------

priorLearningMemoryBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorLearningMemoryBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

witchTrialBoundary : WitchTrial.WitchTrialEvidenceBoundary
witchTrialBoundary = WitchTrial.canonicalWitchTrialEvidenceBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record DependencyReverseConstraint : Set where
  constructor dependency-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open DependencyReverseConstraint public

scienceConstraint : DependencyReverseConstraint
scienceConstraint = dependency-reverse-constraint
  "Science / replication / meta-analysis"
  "study count, effect-size count, sample/code/data genealogy, methodological reproducibility, provenance independence, uncertainty and consensus remain distinct"
  false

mediaConstraint : DependencyReverseConstraint
mediaConstraint = dependency-reverse-constraint
  "Media / information / OSINT"
  "outlet count, publication count, primary source count, copying/reposting lineage, source diversity and corroboration remain distinct"
  false

memoryConstraint : DependencyReverseConstraint
memoryConstraint = dependency-reverse-constraint
  "Memory / testimony"
  "repeated retrieval, repeated reporting, independent witnesses, shared post-event information and corroborative independence remain distinct"
  false

historyConstraint : DependencyReverseConstraint
historyConstraint = dependency-reverse-constraint
  "History / archives"
  "surviving document count, textual descent/copying, common informant/source, archival custody and independent attestation remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data MoreItemsMeanMoreIndependentEvidence : Set where
data MorePapersMeanMoreIndependentStudies : Set where
data MoreOutletsMeanMorePrimarySources : Set where
data RepeatedMemoryReportsMeanIndependentCorroboration : Set where
data ConsensusSizeMeansIndependentEvidenceBase : Set where
data MetaAnalysisMeansIndependenceHandled : Set where

moreItemsDoNotCreateIndependence : MoreItemsMeanMoreIndependentEvidence → ⊥
moreItemsDoNotCreateIndependence ()

morePapersDoNotCreateIndependentStudies : MorePapersMeanMoreIndependentStudies → ⊥
morePapersDoNotCreateIndependentStudies ()

moreOutletsDoNotCreatePrimarySources : MoreOutletsMeanMorePrimarySources → ⊥
moreOutletsDoNotCreatePrimarySources ()

repeatedReportsDoNotCreateCorroboration : RepeatedMemoryReportsMeanIndependentCorroboration → ⊥
repeatedReportsDoNotCreateCorroboration ()

consensusSizeDoesNotCreateIndependentEvidenceBase : ConsensusSizeMeansIndependentEvidenceBase → ⊥
consensusSizeDoesNotCreateIndependentEvidenceBase ()

metaAnalysisDoesNotGuaranteeDependenceHandled : MetaAnalysisMeansIndependenceHandled → ⊥
metaAnalysisDoesNotGuaranteeDependenceHandled ()

record EvidenceDependencyReplicationConsensusBoundary : Set where
  constructor evidence-dependency-replication-consensus-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyAttachedOnlyWhenInspected : Bool
    doiSourceRolesRetained : Bool
    rawMultiplicitySeparatedFromIndependence : Bool
    publicationCountSeparatedFromEffectiveEvidence : Bool
    outletCountSeparatedFromSourceDiversity : Bool
    repeatedRetrievalSeparatedFromIndependentCorroboration : Bool
    consensusBreadthSeparatedFromEvidenceBaseIndependence : Bool
    unresolvedDependencyRetainedExplicitly : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceDependencyReplicationConsensusBoundary public

canonicalEvidenceDependencyReplicationConsensusBoundary :
  EvidenceDependencyReplicationConsensusBoundary
canonicalEvidenceDependencyReplicationConsensusBoundary =
  evidence-dependency-replication-consensus-boundary
    true true true true true true true true true true false

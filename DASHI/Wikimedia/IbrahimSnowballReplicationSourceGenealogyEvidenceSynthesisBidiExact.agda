module DASHI.Wikimedia.IbrahimSnowballReplicationSourceGenealogyEvidenceSynthesisBidiExact where

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

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL: REPLICATION -> SOURCE GENEALOGY -> EVIDENCE SYNTHESIS
-- -> META-ANALYSIS -> CONSENSUS, with attribution/provenance retained.
--
-- Counts of studies, papers, reports, citations, memories, media stories or
-- replications do not by themselves pay independence.  Evidence synthesis is
-- a consumer over source genealogy, inclusion criteria, dependence, methods,
-- uncertainty and attribution.  Consensus remains downstream of that audit and
-- is not definitionally identical to proposition truth.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim replication/source-genealogy/evidence-synthesis BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create independence, methodological adequacy, consensus or truth")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = Prior.reproducibilityQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = Prior.scientificConsensusQid

sourceGenealogyQid : Identity.ExternalIdentityDemand
sourceGenealogyQid = Identity.mkOptionalIdentityDemand
  "Ibrahim replication/source-genealogy/evidence-synthesis BIDI"
  "external concept identity"
  "source genealogy / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single QID promoted for study/report source genealogy or common-source dependence; provenance relation remains typed locally")

evidenceSynthesisQid : Identity.ExternalIdentityDemand
evidenceSynthesisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim replication/source-genealogy/evidence-synthesis BIDI"
  "external concept identity"
  "evidence synthesis"
  Identity.wikidataQid
  (Identity.unresolved
    "a 2026 Wikidata item labelled evidence synthesis exists but is not promoted here as the canonical research-method identity; systematic review Q1504425 and meta-analysis Q815382 remain the stable external coordinates")

------------------------------------------------------------------------
-- Dewey: no values guessed from nearby methodology shelves.
------------------------------------------------------------------------

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted in this pass"

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted in this pass"

sourceGenealogyDewey : Dewey.DeweyCoordinate
sourceGenealogyDewey = Dewey.mkUnresolvedDewey
  "source genealogy / dependence"
  "consumer-relative provenance relation; no one DDC coordinate promoted"

------------------------------------------------------------------------
-- DOI/source attribution.
------------------------------------------------------------------------

prisma2020Source : Attribution.AttributedSource
prisma2020Source = Attribution.mkDOISource
  "Matthew J. Page et al."
  "The PRISMA 2020 statement: an updated guideline for reporting systematic reviews"
  "BMJ 372:n71"
  "2021"
  "10.1136/bmj.n71"
  "https://doi.org/10.1136/bmj.n71"
  Attribution.academicArticleSource
  "reporting guideline for transparent identification, selection, appraisal and synthesis of studies; reporting compliance does not itself prove review validity, independence or truth"
  Attribution.publicAttribution

vanDenNoortgateDependenceSource : Attribution.AttributedSource
vanDenNoortgateDependenceSource = Attribution.mkDOISource
  "Wim Van den Noortgate; José Antonio López-López; Fulgencio Marín-Martínez; Julio Sánchez-Meca"
  "Three-level meta-analysis of dependent effect sizes"
  "Behavior Research Methods 45, 576-594"
  "2013"
  "10.3758/s13428-012-0261-6"
  "https://doi.org/10.3758/s13428-012-0261-6"
  Attribution.academicArticleSource
  "methodological treatment of dependence among effect sizes within and across studies; supports explicit dependence modelling rather than treating every effect size as an independent evidentiary line"
  Attribution.publicAttribution

cheungChanDependenceSource : Attribution.AttributedSource
cheungChanDependenceSource = Attribution.mkDOISource
  "Shu Fai Cheung; Darius K-S Chan"
  "Dependent effect sizes in meta-analysis: incorporating the degree of interdependence"
  "Journal of Applied Psychology 89(5), 780-791"
  "2004"
  "10.1037/0021-9010.89.5.780"
  "https://doi.org/10.1037/0021-9010.89.5.780"
  Attribution.academicArticleSource
  "methodological analysis of dependent effect sizes from shared samples; same sample or common source prevents naive independence counting"
  Attribution.publicAttribution

pustejovskyDependenceWorkflowSource : Attribution.AttributedSource
pustejovskyDependenceWorkflowSource = Attribution.mkDOISource
  "James E. Pustejovsky; Jingru Zhang; Elizabeth Tipton"
  "A preliminary data analysis workflow for meta-analysis of dependent effect sizes"
  "Philosophical Transactions of the Royal Society A 384"
  "2026"
  "10.1098/rsta.2024.0604"
  "https://doi.org/10.1098/rsta.2024.0604"
  Attribution.academicArticleSource
  "current workflow for identifying and handling dependent effect sizes in meta-analysis; methodology source only, not proof that any particular synthesis is unbiased"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact reuse from prior owners.
------------------------------------------------------------------------

priorBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

------------------------------------------------------------------------
-- Regression 1: review/study count cannot recover independent evidence lines.
------------------------------------------------------------------------

data ReviewCountCase : Set where
  sameIncludedCountIndependentStudies sameIncludedCountSharedGenealogy : ReviewCountCase

data ReviewCountSurface : Set where sameIncludedStudyCount : ReviewCountSurface
data EvidenceIndependence : Set where independentEvidenceLines commonSourceDependentLines : EvidenceIndependence

reviewCountSurface : ReviewCountCase → ReviewCountSurface
reviewCountSurface _ = sameIncludedStudyCount

evidenceIndependence : ReviewCountCase → EvidenceIndependence
evidenceIndependence sameIncludedCountIndependentStudies = independentEvidenceLines
evidenceIndependence sameIncludedCountSharedGenealogy = commonSourceDependentLines

reviewCountIndependenceDefect : INF.NonFactorabilityWitness reviewCountSurface evidenceIndependence
reviewCountIndependenceDefect = INF.nonFactorabilityWitness
  sameIncludedCountIndependentStudies sameIncludedCountSharedGenealogy refl (λ ())

studyCountCannotFactorIndependentEvidence :
  INF.FactorsThrough reviewCountSurface evidenceIndependence → ⊥
studyCountCannotFactorIndependentEvidence =
  INF.witnessRulesOutEveryFlatFactorisation reviewCountIndependenceDefect

------------------------------------------------------------------------
-- Regression 2: identical pooled result cannot recover source genealogy.
------------------------------------------------------------------------

data PooledCase : Set where
  samePooledEstimateIndependentInputs samePooledEstimateDependentInputs : PooledCase

data PooledSurface : Set where sameMetaAnalyticEstimate : PooledSurface
data GenealogyStatus : Set where genealogyIndependent genealogyDependent : GenealogyStatus

pooledSurface : PooledCase → PooledSurface
pooledSurface _ = sameMetaAnalyticEstimate

genealogyStatus : PooledCase → GenealogyStatus
genealogyStatus samePooledEstimateIndependentInputs = genealogyIndependent
genealogyStatus samePooledEstimateDependentInputs = genealogyDependent

pooledGenealogyDefect : INF.NonFactorabilityWitness pooledSurface genealogyStatus
pooledGenealogyDefect = INF.nonFactorabilityWitness
  samePooledEstimateIndependentInputs samePooledEstimateDependentInputs refl (λ ())

pooledEstimateCannotFactorSourceGenealogy :
  INF.FactorsThrough pooledSurface genealogyStatus → ⊥
pooledEstimateCannotFactorSourceGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation pooledGenealogyDefect

------------------------------------------------------------------------
-- Regression 3: systematic-review label/reporting cannot recover methodological
-- adequacy or proposition truth.
------------------------------------------------------------------------

data ReviewLabelCase : Set where
  sameSystematicReviewLabelAdequate sameSystematicReviewLabelInadequate : ReviewLabelCase

data ReviewLabelSurface : Set where sameSystematicReviewLabel : ReviewLabelSurface
data ReviewAdequacy : Set where reviewAdequacyPaid reviewAdequacyOpen : ReviewAdequacy

reviewLabelSurface : ReviewLabelCase → ReviewLabelSurface
reviewLabelSurface _ = sameSystematicReviewLabel

reviewAdequacy : ReviewLabelCase → ReviewAdequacy
reviewAdequacy sameSystematicReviewLabelAdequate = reviewAdequacyPaid
reviewAdequacy sameSystematicReviewLabelInadequate = reviewAdequacyOpen

reviewAdequacyDefect : INF.NonFactorabilityWitness reviewLabelSurface reviewAdequacy
reviewAdequacyDefect = INF.nonFactorabilityWitness
  sameSystematicReviewLabelAdequate sameSystematicReviewLabelInadequate refl (λ ())

systematicReviewLabelCannotFactorAdequacy :
  INF.FactorsThrough reviewLabelSurface reviewAdequacy → ⊥
systematicReviewLabelCannotFactorAdequacy =
  INF.witnessRulesOutEveryFlatFactorisation reviewAdequacyDefect

------------------------------------------------------------------------
-- Regression 4: consensus surface cannot recover evidentiary genealogy.
------------------------------------------------------------------------

data ConsensusGenealogyCase : Set where
  sameConsensusIndependentBase sameConsensusCommonSourceBase : ConsensusGenealogyCase

data ConsensusSurface : Set where sameConsensusPosition : ConsensusSurface
data ConsensusEvidenceBase : Set where independentEvidenceBase commonSourceEvidenceBase : ConsensusEvidenceBase

consensusSurface : ConsensusGenealogyCase → ConsensusSurface
consensusSurface _ = sameConsensusPosition

consensusEvidenceBase : ConsensusGenealogyCase → ConsensusEvidenceBase
consensusEvidenceBase sameConsensusIndependentBase = independentEvidenceBase
consensusEvidenceBase sameConsensusCommonSourceBase = commonSourceEvidenceBase

consensusGenealogyDefect : INF.NonFactorabilityWitness consensusSurface consensusEvidenceBase
consensusGenealogyDefect = INF.nonFactorabilityWitness
  sameConsensusIndependentBase sameConsensusCommonSourceBase refl (λ ())

consensusCannotFactorEvidenceGenealogy :
  INF.FactorsThrough consensusSurface consensusEvidenceBase → ⊥
consensusCannotFactorEvidenceGenealogy =
  INF.witnessRulesOutEveryFlatFactorisation consensusGenealogyDefect

------------------------------------------------------------------------
-- Cross-domain provenance grammar: testimony, memory, media, science.
------------------------------------------------------------------------

record ProvenanceFamily : Set where
  constructor provenance-family
  field
    familyLabel : String
    multiplicityCarrier : String
    independenceQuestion : String
    attributionMustTravel : Bool
open ProvenanceFamily public

witnessFamily : ProvenanceFamily
witnessFamily = provenance-family
  "witness/testimony"
  "multiple reports"
  "independent observation versus interrogation/repetition/common narrative"
  true

memoryFamily : ProvenanceFamily
memoryFamily = provenance-family
  "memory/learning"
  "repeated recall or repeated public remembered PNF"
  "independent retrieval evidence versus same latent memory/update history"
  true

scienceFamily : ProvenanceFamily
scienceFamily = provenance-family
  "science/replication"
  "multiple papers/effect sizes/replications"
  "independent samples/methods versus shared data, sample, code, lab or source genealogy"
  true

mediaFamily : ProvenanceFamily
mediaFamily = provenance-family
  "media/OSINT"
  "multiple stories/posts/citations"
  "independent reporting versus copying, syndication or shared upstream source"
  true

------------------------------------------------------------------------
-- Reverse BIDI constraints back into Ibrahim parents.
------------------------------------------------------------------------

record EvidenceSynthesisReverseConstraint : Set where
  constructor evidence-synthesis-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open EvidenceSynthesisReverseConstraint public

scienceConstraint : EvidenceSynthesisReverseConstraint
scienceConstraint = evidence-synthesis-reverse-constraint
  "Science / evidence synthesis / consensus"
  "study identity, sample/data/code genealogy, effect-size dependence, inclusion, appraisal, synthesis, uncertainty and consensus remain distinct"
  false

informationConstraint : EvidenceSynthesisReverseConstraint
informationConstraint = evidence-synthesis-reverse-constraint
  "Library / information science / bibliography"
  "citation multiplicity, unique work identity, source genealogy, access/inspection and evidentiary independence remain distinct"
  false

mediaConstraint : EvidenceSynthesisReverseConstraint
mediaConstraint = evidence-synthesis-reverse-constraint
  "Media / OSINT / alternative media"
  "story count, copying/syndication, common upstream source, firsthand reporting and independent corroboration remain distinct"
  false

memoryConstraint : EvidenceSynthesisReverseConstraint
memoryConstraint = evidence-synthesis-reverse-constraint
  "Memory / learning / trauma"
  "repeated retrieval/report, latent memory state, contextual learning history and independent external corroboration remain distinct"
  false

------------------------------------------------------------------------
-- Attribution/Snowball firewalls.
------------------------------------------------------------------------

data MorePapersMeanMoreIndependentEvidence : Set where
data MetaAnalysisMeansIndependentInputs : Set where
data SystematicReviewLabelMeansAdequateMethod : Set where
data ConsensusMeansIndependentEvidenceBase : Set where
data CitationCountMeansIndependentSources : Set where
data QidMeansMethodologicalAdequacy : Set where
data DOIImportsResultTruth : Set where

morePapersDoNotCreateIndependence : MorePapersMeanMoreIndependentEvidence → ⊥
morePapersDoNotCreateIndependence ()

metaAnalysisDoesNotCreateIndependentInputs : MetaAnalysisMeansIndependentInputs → ⊥
metaAnalysisDoesNotCreateIndependentInputs ()

systematicReviewLabelDoesNotCreateAdequacy : SystematicReviewLabelMeansAdequateMethod → ⊥
systematicReviewLabelDoesNotCreateAdequacy ()

consensusDoesNotCreateIndependentEvidenceBase : ConsensusMeansIndependentEvidenceBase → ⊥
consensusDoesNotCreateIndependentEvidenceBase ()

citationCountDoesNotCreateIndependentSources : CitationCountMeansIndependentSources → ⊥
citationCountDoesNotCreateIndependentSources ()

qidDoesNotCreateMethodologicalAdequacy : QidMeansMethodologicalAdequacy → ⊥
qidDoesNotCreateMethodologicalAdequacy ()

doiDoesNotImportResultTruth : DOIImportsResultTruth → ⊥
doiDoesNotImportResultTruth ()

record ReplicationSourceGenealogyEvidenceSynthesisBoundary : Set where
  constructor replication-source-genealogy-evidence-synthesis-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedSourceGenealogyIdentityRetained : Bool
    deweyUnknownsRetainedExplicitly : Bool
    doiSourceAttributionTravels : Bool
    studyCountSeparatedFromIndependence : Bool
    pooledEstimateSeparatedFromGenealogy : Bool
    reviewLabelSeparatedFromAdequacy : Bool
    consensusSeparatedFromEvidenceGenealogy : Bool
    crossDomainProvenanceFamiliesRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ReplicationSourceGenealogyEvidenceSynthesisBoundary public

canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary :
  ReplicationSourceGenealogyEvidenceSynthesisBoundary
canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary =
  replication-source-genealogy-evidence-synthesis-boundary
    true true true true true true true true true true false

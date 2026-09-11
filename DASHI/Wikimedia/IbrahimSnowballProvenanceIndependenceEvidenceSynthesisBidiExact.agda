module DASHI.Wikimedia.IbrahimSnowballProvenanceIndependenceEvidenceSynthesisBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SourceProvenanceExact as SourceProvenance
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as LearningMemory
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as Media

------------------------------------------------------------------------
-- IBRAHIM / PROVENANCE-INDEPENDENCE / EVIDENCE-SYNTHESIS BIDI
--
-- Multiplicity is not independence.  A set of reports, papers, citations,
-- replications or media items may descend from a shared observation, dataset,
-- codebase, model, source text or upstream synthesis.  Evidence synthesis and
-- consensus are therefore consumers of a provenance graph, not substitutes for
-- that graph.
--
-- This owner composes existing testimony/common-source, replication/consensus,
-- media and native Wikimedia source-layer boundaries.  It does not define a
-- parallel provenance architecture.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim provenance-independence/evidence-synthesis BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create independence, evidentiary weight, consensus truth or causal authority")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = LearningMemory.scientificConsensusQid

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = LearningMemory.reproducibilityQid

ipccQid : Identity.ExternalIdentityDemand
ipccQid = mkQid "Intergovernmental Panel on Climate Change" "Q171183"

ipccAR6SynthesisReportQid : Identity.ExternalIdentityDemand
ipccAR6SynthesisReportQid = mkQid
  "Climate Change 2023: AR6 Synthesis Report"
  "Q140144650"

citationCascadeQid : Identity.ExternalIdentityDemand
citationCascadeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim provenance-independence/evidence-synthesis BIDI"
  "external concept identity"
  "citation cascade / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact generic QID promoted for citation cascade/common-source dependence; retain as provenance relation rather than force a nearby bibliometrics concept")

------------------------------------------------------------------------
-- Dewey: only promote inspected coordinates.  Evidence-synthesis document
-- types remain unresolved here rather than inheriting a nearby science shelf.
------------------------------------------------------------------------

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted in this pass"

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted in this pass"

ipccDewey : Dewey.DeweyCoordinate
ipccDewey = Dewey.mkUnresolvedDewey
  "IPCC / climate assessment"
  "institution/report identity retained separately from any library-classification coordinate"

------------------------------------------------------------------------
-- Source-bounded examples.
------------------------------------------------------------------------

schafmeisterReplicationCitationSource : Attribution.AttributedSource
schafmeisterReplicationCitationSource = Attribution.mkDOISource
  "Felix Schafmeister"
  "The Effect of Replications on Citation Patterns: Evidence From a Large-Scale Reproducibility Project"
  "Psychological Science 32(10), 1537-1548"
  "2021"
  "10.1177/09567976211005767"
  "https://doi.org/10.1177/09567976211005767"
  Attribution.academicArticleSource
  "study of citation responses to independent replication attempts in the Reproducibility Project: Psychology; citation persistence is not itself evidence of independent replication or truth"
  Attribution.publicAttribution

informationCascadesSource : Attribution.AttributedSource
informationCascadesSource = Attribution.mkDOISource
  "Sushil Bikhchandani; David Hirshleifer; Omer Tamuz; Ivo Welch"
  "Information Cascades and Social Learning"
  "Journal of Economic Literature 62(3), 1040-1093"
  "2024"
  "10.1257/jel.20241472"
  "https://doi.org/10.1257/jel.20241472"
  Attribution.academicArticleSource
  "review of social learning and information cascades; repeated downstream adoption can reflect observation of others rather than independent private evidence"
  Attribution.publicAttribution

ipccAR6SynthesisSource : Attribution.AttributedSource
ipccAR6SynthesisSource = Attribution.mkDOISource
  "Intergovernmental Panel on Climate Change"
  "Climate Change 2023: Synthesis Report"
  "IPCC Sixth Assessment Report synthesis"
  "2023"
  "10.59327/IPCC/AR6-9789291691647"
  "https://doi.org/10.59327/IPCC/AR6-9789291691647"
  Attribution.institutionalSource
  "assessment/synthesis report integrating multiple working-group evidence streams; the report is a synthesis carrier, not an additional independent primary observation for every underlying claim"
  Attribution.publicAttribution

citationCascadeSource : Attribution.AttributedSource
citationCascadeSource = Attribution.mkDOISource
  "Chao Min et al."
  "Citation cascade and the evolution of topic relevance"
  "Journal of the Association for Information Science and Technology"
  "2021"
  "10.1002/asi.24370"
  "https://doi.org/10.1002/asi.24370"
  Attribution.academicArticleSource
  "bibliometric study of multi-generation citation cascades; citation descendants retain lineage and cannot be treated as automatically independent evidence"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Provenance grammar.
------------------------------------------------------------------------

data DependencyKind : Set where
  independentOrigin : DependencyKind
  sharedObservation : DependencyKind
  sharedDataset : DependencyKind
  sharedCodeOrModel : DependencyKind
  sharedPrimarySource : DependencyKind
  citationDescendant : DependencyKind
  synthesisDescendant : DependencyKind

data EvidenceFamily : Set where
  testimonyFamily studyFamily mediaFamily assessmentFamily : EvidenceFamily

record EvidenceLineageReceipt : Set where
  constructor evidence-lineage-receipt
  field
    family : EvidenceFamily
    sourceLabel : String
    stableIdentifier : String
    dependency : DependencyKind
    upstreamLabel : String
    independenceAudited : Bool
    countedAsIndependentLine : Bool
open EvidenceLineageReceipt public

------------------------------------------------------------------------
-- Regression 1: source count cannot recover independent evidence count.
------------------------------------------------------------------------

data MultiplicityCase : Set where
  sameCountIndependentSources sameCountCommonSourceDescendants : MultiplicityCase

data MultiplicitySurface : Set where sameSourceCount : MultiplicitySurface
data IndependentEvidenceStatus : Set where independentEvidenceLines commonSourceDependentLines : IndependentEvidenceStatus

multiplicitySurface : MultiplicityCase → MultiplicitySurface
multiplicitySurface _ = sameSourceCount

independentEvidenceStatus : MultiplicityCase → IndependentEvidenceStatus
independentEvidenceStatus sameCountIndependentSources = independentEvidenceLines
independentEvidenceStatus sameCountCommonSourceDescendants = commonSourceDependentLines

multiplicityIndependenceDefect : INF.NonFactorabilityWitness multiplicitySurface independentEvidenceStatus
multiplicityIndependenceDefect = INF.nonFactorabilityWitness
  sameCountIndependentSources sameCountCommonSourceDescendants refl (λ ())

sourceCountCannotFactorIndependentEvidenceCount :
  INF.FactorsThrough multiplicitySurface independentEvidenceStatus → ⊥
sourceCountCannotFactorIndependentEvidenceCount =
  INF.witnessRulesOutEveryFlatFactorisation multiplicityIndependenceDefect

------------------------------------------------------------------------
-- Regression 2: citation count cannot recover evidentiary support.
------------------------------------------------------------------------

data CitationCase : Set where
  sameCitationCountSupportive sameCitationCountCriticalOrIncidental : CitationCase

data CitationSurface : Set where sameCitationMultiplicity : CitationSurface
data CitationRole : Set where evidentiarySupport criticalOrIncidentalCitation : CitationRole

citationSurface : CitationCase → CitationSurface
citationSurface _ = sameCitationMultiplicity

citationRole : CitationCase → CitationRole
citationRole sameCitationCountSupportive = evidentiarySupport
citationRole sameCitationCountCriticalOrIncidental = criticalOrIncidentalCitation

citationRoleDefect : INF.NonFactorabilityWitness citationSurface citationRole
citationRoleDefect = INF.nonFactorabilityWitness
  sameCitationCountSupportive sameCitationCountCriticalOrIncidental refl (λ ())

citationCountCannotFactorEvidenceRole :
  INF.FactorsThrough citationSurface citationRole → ⊥
citationCountCannotFactorEvidenceRole =
  INF.witnessRulesOutEveryFlatFactorisation citationRoleDefect

------------------------------------------------------------------------
-- Regression 3: a synthesis/assessment cannot be counted as an additional
-- independent primary observation merely because it has its own DOI/QID.
------------------------------------------------------------------------

data SynthesisCase : Set where
  sameAssessmentIdentityPrimaryObservation sameAssessmentIdentityEvidenceSynthesis : SynthesisCase

data AssessmentIdentitySurface : Set where sameAssessmentDocumentIdentity : AssessmentIdentitySurface
data EvidentiaryRole : Set where primaryObservationRole synthesisRole : EvidentiaryRole

assessmentIdentitySurface : SynthesisCase → AssessmentIdentitySurface
assessmentIdentitySurface _ = sameAssessmentDocumentIdentity

evidentiaryRole : SynthesisCase → EvidentiaryRole
evidentiaryRole sameAssessmentIdentityPrimaryObservation = primaryObservationRole
evidentiaryRole sameAssessmentIdentityEvidenceSynthesis = synthesisRole

assessmentRoleDefect : INF.NonFactorabilityWitness assessmentIdentitySurface evidentiaryRole
assessmentRoleDefect = INF.nonFactorabilityWitness
  sameAssessmentIdentityPrimaryObservation sameAssessmentIdentityEvidenceSynthesis refl (λ ())

assessmentIdentityCannotFactorPrimaryVsSynthesisRole :
  INF.FactorsThrough assessmentIdentitySurface evidentiaryRole → ⊥
assessmentIdentityCannotFactorPrimaryVsSynthesisRole =
  INF.witnessRulesOutEveryFlatFactorisation assessmentRoleDefect

------------------------------------------------------------------------
-- Regression 4: consensus surface cannot recover how many genuinely
-- independent evidence families support it.
------------------------------------------------------------------------

data ConsensusSupportCase : Set where
  sameConsensusManyIndependentFamilies sameConsensusOneDominantLineage : ConsensusSupportCase

data ConsensusSupportSurface : Set where sameConsensusPosition : ConsensusSupportSurface
data EvidenceDiversity : Set where diverseIndependentFamilies concentratedLineage : EvidenceDiversity

consensusSupportSurface : ConsensusSupportCase → ConsensusSupportSurface
consensusSupportSurface _ = sameConsensusPosition

evidenceDiversity : ConsensusSupportCase → EvidenceDiversity
evidenceDiversity sameConsensusManyIndependentFamilies = diverseIndependentFamilies
evidenceDiversity sameConsensusOneDominantLineage = concentratedLineage

consensusDiversityDefect : INF.NonFactorabilityWitness consensusSupportSurface evidenceDiversity
consensusDiversityDefect = INF.nonFactorabilityWitness
  sameConsensusManyIndependentFamilies sameConsensusOneDominantLineage refl (λ ())

consensusCannotFactorEvidenceLineageDiversity :
  INF.FactorsThrough consensusSupportSurface evidenceDiversity → ⊥
consensusCannotFactorEvidenceLineageDiversity =
  INF.witnessRulesOutEveryFlatFactorisation consensusDiversityDefect

------------------------------------------------------------------------
-- Exact reuse of existing boundaries.
------------------------------------------------------------------------

sourceAttributionBoundary : SourceProvenance.SourceAttributionBoundary
sourceAttributionBoundary = SourceProvenance.canonicalSourceAttributionBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

learningReplicationBoundary : LearningMemory.LearningMemoryTraumaReplicationConsensusBoundary
learningReplicationBoundary = LearningMemory.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parents.
------------------------------------------------------------------------

record ProvenanceReverseConstraint : Set where
  constructor provenance-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ProvenanceReverseConstraint public

scienceConstraint : ProvenanceReverseConstraint
scienceConstraint = provenance-reverse-constraint
  "Science / replication / consensus"
  "paper count, replication count, shared data/code/model lineage, independent evidence families, synthesis and consensus remain distinct"
  false

mediaConstraint : ProvenanceReverseConstraint
mediaConstraint = provenance-reverse-constraint
  "Media / information"
  "story count, original reporting, syndicated/copied descendants, common primary source, commentary and evidentiary support remain distinct"
  false

lawConstraint : ProvenanceReverseConstraint
lawConstraint = provenance-reverse-constraint
  "Evidence / corroboration"
  "witness multiplicity, generated testimony, common-source dependence, independent corroboration, admissibility and weight remain distinct"
  false

climateAssessmentConstraint : ProvenanceReverseConstraint
climateAssessmentConstraint = provenance-reverse-constraint
  "Climate / assessment / IPCC"
  "primary observations, model ensembles, literature assessments, working-group synthesis, consensus judgments and institutional report identity remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data MoreSourcesMeanMoreIndependentEvidence : Set where
data CitationCountMeansSupport : Set where
data DOIOrQidMakesPrimaryEvidence : Set where
data SynthesisReportIsIndependentPrimaryStudy : Set where
data ConsensusMeansIndependentEvidenceDiversity : Set where
data ProvenanceCreatesAuthority : Set where

moreSourcesDoNotMeanMoreIndependentEvidence : MoreSourcesMeanMoreIndependentEvidence → ⊥
moreSourcesDoNotMeanMoreIndependentEvidence ()

citationCountDoesNotMeanSupport : CitationCountMeansSupport → ⊥
citationCountDoesNotMeanSupport ()

doiOrQidDoesNotMakePrimaryEvidence : DOIOrQidMakesPrimaryEvidence → ⊥
doiOrQidDoesNotMakePrimaryEvidence ()

synthesisReportDoesNotBecomeIndependentPrimaryStudy : SynthesisReportIsIndependentPrimaryStudy → ⊥
synthesisReportDoesNotBecomeIndependentPrimaryStudy ()

consensusDoesNotCreateEvidenceDiversity : ConsensusMeansIndependentEvidenceDiversity → ⊥
consensusDoesNotCreateEvidenceDiversity ()

provenanceStillDoesNotCreateAuthority : ProvenanceCreatesAuthority → ⊥
provenanceStillDoesNotCreateAuthority ()

record ProvenanceIndependenceEvidenceSynthesisBoundary : Set where
  constructor provenance-independence-evidence-synthesis-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    deweyUnresolvedStatesRetained : Bool
    doiSourceRolesRetained : Bool
    sourceCountSeparatedFromIndependentEvidenceCount : Bool
    citationCountSeparatedFromEvidenceRole : Bool
    synthesisSeparatedFromPrimaryObservation : Bool
    consensusSeparatedFromEvidenceLineageDiversity : Bool
    nativeSourceLayerBoundaryReused : Bool
    testimonyAndReplicationIndependenceReused : Bool
    ipccUsedAsBoundedSynthesisExampleOnly : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ProvenanceIndependenceEvidenceSynthesisBoundary public

canonicalProvenanceIndependenceEvidenceSynthesisBoundary :
  ProvenanceIndependenceEvidenceSynthesisBoundary
canonicalProvenanceIndependenceEvidenceSynthesisBoundary =
  provenance-independence-evidence-synthesis-boundary
    true true true true true true true true true true true false

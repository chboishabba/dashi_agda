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
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis

------------------------------------------------------------------------
-- THIN BIDI SPECIALISATION: META-ANALYTIC OUTPUT <-> SOURCE GENEALOGY
--
-- The general independence, peer-review, consensus and evidence-synthesis
-- semantics already live in Synthesis/Dependency.  This owner pays only the
-- surviving methodological gap: the same pooled/meta-analytic output can arise
-- from evidentiary bases with different within-study/shared-sample/source
-- dependence.  PRISMA/reporting identity and DOI/QID/Dewey attribution travel
-- but do not manufacture independence or truth.
------------------------------------------------------------------------

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = Synthesis.systematicReviewQid

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = Synthesis.metaAnalysisQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = Synthesis.scientificConsensusQid

sourceGenealogyQid : Identity.ExternalIdentityDemand
sourceGenealogyQid = Dependency.sourceIndependenceQid

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Synthesis.systematicReviewDewey

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted; Q815382 identity retained separately"

------------------------------------------------------------------------
-- Source-paid methodological lane.
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
  "reporting guidance for identifying, selecting, appraising and synthesising studies; reporting compliance does not itself establish independence, adequacy or truth"
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
  "methodological treatment of dependent effect sizes within and across studies; supports explicit modelling of dependence rather than naive effect-size counting"
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
  "analysis of dependent effect sizes from shared samples; shared sample/source means multiple effects are not automatically independent evidence lines"
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
  "current workflow for detecting and handling dependence in meta-analysis; methodology source only, not a truth or unbiasedness certificate for any concrete synthesis"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact reuse: no parallel epistemology.
------------------------------------------------------------------------

synthesisBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
synthesisBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

------------------------------------------------------------------------
-- Surviving regression: pooled output cannot recover genealogy/dependence.
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
-- Cross-domain snowball: one dependence grammar, different consumers.
------------------------------------------------------------------------

record ProvenanceDependenceProjection : Set where
  constructor provenance-dependence-projection
  field
    consumer : String
    repeatedSurface : String
    hiddenDependenceCoordinate : String
    attributionMustTravel : Bool
open ProvenanceDependenceProjection public

witnessProjection : ProvenanceDependenceProjection
witnessProjection = provenance-dependence-projection
  "testimony"
  "multiple reports"
  "common interrogation, shared narrative or genuinely independent observation"
  true

memoryProjection : ProvenanceDependenceProjection
memoryProjection = provenance-dependence-projection
  "memory/learning"
  "repeated recall / same public remembered PNF"
  "shared latent memory/update history versus independent external corroboration"
  true

scienceProjection : ProvenanceDependenceProjection
scienceProjection = provenance-dependence-projection
  "meta-analysis/replication"
  "multiple effects/studies/papers"
  "shared sample, dataset, code, lab, instrument or source genealogy"
  true

mediaProjection : ProvenanceDependenceProjection
mediaProjection = provenance-dependence-projection
  "media/OSINT"
  "multiple stories/posts/citations"
  "copying, syndication, shared upstream source or independent firsthand reporting"
  true

------------------------------------------------------------------------
-- Reverse BIDI parent constraints.
------------------------------------------------------------------------

record MetaAnalysisReverseConstraint : Set where
  constructor meta-analysis-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open MetaAnalysisReverseConstraint public

scienceConstraint : MetaAnalysisReverseConstraint
scienceConstraint = meta-analysis-reverse-constraint
  "Science / meta-analysis / consensus"
  "effect-size identity, sample/data genealogy, dependence model, pooled estimate, uncertainty and consensus remain distinct"
  false

informationConstraint : MetaAnalysisReverseConstraint
informationConstraint = meta-analysis-reverse-constraint
  "Bibliography / evidence synthesis"
  "citation/work identity, duplicate/shared source, inclusion, appraisal, dependence and synthesis output remain distinct"
  false

memoryMediaConstraint : MetaAnalysisReverseConstraint
memoryMediaConstraint = meta-analysis-reverse-constraint
  "Memory / testimony / media"
  "surface repetition, common informational origin, social copying and independent corroboration remain distinct"
  false

------------------------------------------------------------------------
-- Attribution/Snowball firewalls.
------------------------------------------------------------------------

data MetaAnalysisMeansIndependentInputs : Set where
data PooledEstimateMeansIndependentEvidence : Set where
data PrismaComplianceMeansTruth : Set where
data QidMeansAdequacy : Set where
data DOIImportsTruth : Set where

metaAnalysisDoesNotCreateIndependentInputs : MetaAnalysisMeansIndependentInputs → ⊥
metaAnalysisDoesNotCreateIndependentInputs ()

pooledEstimateDoesNotCreateIndependentEvidence : PooledEstimateMeansIndependentEvidence → ⊥
pooledEstimateDoesNotCreateIndependentEvidence ()

prismaComplianceDoesNotCreateTruth : PrismaComplianceMeansTruth → ⊥
prismaComplianceDoesNotCreateTruth ()

qidDoesNotCreateAdequacy : QidMeansAdequacy → ⊥
qidDoesNotCreateAdequacy ()

doiDoesNotImportTruth : DOIImportsTruth → ⊥
doiDoesNotImportTruth ()

record ReplicationSourceGenealogyEvidenceSynthesisBoundary : Set where
  constructor replication-source-genealogy-evidence-synthesis-boundary
  field
    existingEvidenceSynthesisOwnerReused : Bool
    existingDependencyOwnerReused : Bool
    qidDeweyDoiAttributionTravels : Bool
    pooledEstimateSeparatedFromSourceGenealogy : Bool
    dependenceModelRetainedAsConsumerCoordinate : Bool
    crossDomainProvenanceProjectionRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open ReplicationSourceGenealogyEvidenceSynthesisBoundary public

canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary :
  ReplicationSourceGenealogyEvidenceSynthesisBoundary
canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary =
  replication-source-genealogy-evidence-synthesis-boundary
    true true true true true true true false

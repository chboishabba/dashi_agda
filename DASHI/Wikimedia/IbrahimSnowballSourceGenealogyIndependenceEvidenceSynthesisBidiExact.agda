module DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact where

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
import DASHI.Wikimedia.IbrahimSnowballReplicationSourceGenealogyEvidenceSynthesisBidiExact as Genealogy
import DASHI.Wikimedia.IbrahimSnowballInformationCascadeEvidenceDependencyHyperfabricBidiExact as Cascade
import DASHI.Wikimedia.IbrahimSnowballDependencySourceQualityAttributionDeltaExact as Quality

------------------------------------------------------------------------
-- THIN DELTA: PRIMARY-SOURCE ROLE / CITATION-BIAS / VISIBILITY
--
-- Dependency, source genealogy, meta-analytic dependence, information cascades,
-- source quality and consensus are already owned by imported modules.  This
-- file adds only what survived quotienting:
--   * exact primary-source QID + bounded role,
--   * DOI/canonical attribution for citation-bias / replicability studies,
--   * citation visibility != replicability/evidential weight,
--   * primary-source role != proposition truth.
--
-- QID, DOI, canonical link and Dewey remain navigation/provenance coordinates.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim primary-source/citation-bias/source-genealogy delta"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, independence, evidentiary weight or source quality")

primarySourceQid : Identity.ExternalIdentityDemand
primarySourceQid = mkQid "primary source" "Q112754"

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = Synthesis.systematicReviewQid

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = Synthesis.metaAnalysisQid

sourceGenealogyQid : Identity.ExternalIdentityDemand
sourceGenealogyQid = Dependency.sourceIndependenceQid

primarySourceDewey : Dewey.DeweyCoordinate
primarySourceDewey = Dewey.mkUnresolvedDewey
  "primary source"
  "Q112754 verified; no exact inspected DDC value promoted in this pass"

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Synthesis.systematicReviewDewey

------------------------------------------------------------------------
-- Source-paid citation/replication lane.
------------------------------------------------------------------------

serraGarciaGneezySource : Attribution.AttributedSource
serraGarciaGneezySource = Attribution.mkDOISource
  "Marta Serra-Garcia; Uri Gneezy"
  "Nonreplicable publications are cited more than replicable ones"
  "Science Advances 7(21), eabd1705"
  "2021"
  "10.1126/sciadv.abd1705"
  "https://doi.org/10.1126/sciadv.abd1705"
  Attribution.academicArticleSource
  "observational analysis of three replication-project corpora finding higher citation of nonreplicable papers and limited acknowledgement of replication failure; citation visibility is not replication success, independence or truth"
  Attribution.publicAttribution

duyxCitationBiasSource : Attribution.AttributedSource
duyxCitationBiasSource = Attribution.mkDOISource
  "Bram Duyx; Miriam J. E. Urlings; Gerard M. H. Swaen; Lex M. Bouter; Maurice P. Zeegers"
  "Scientific citations favor positive results: a systematic review and meta-analysis"
  "Journal of Clinical Epidemiology 88, 92-101"
  "2017"
  "10.1016/j.jclinepi.2017.06.002"
  "https://doi.org/10.1016/j.jclinepi.2017.06.002"
  Attribution.academicArticleSource
  "systematic review/meta-analysis of citation bias; citation frequency is a dissemination signal that may be systematically associated with result direction and is not an independence or truth count"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: citation visibility cannot recover replication status.
------------------------------------------------------------------------

data CitationVisibilityCase : Set where
  sameCitationVisibilityReplicable sameCitationVisibilityNonreplicable : CitationVisibilityCase

data CitationVisibilitySurface : Set where sameCitationVisibility : CitationVisibilitySurface
data ReplicationStatus : Set where replicableResult nonreplicableResult : ReplicationStatus

citationVisibilitySurface : CitationVisibilityCase → CitationVisibilitySurface
citationVisibilitySurface _ = sameCitationVisibility

replicationStatus : CitationVisibilityCase → ReplicationStatus
replicationStatus sameCitationVisibilityReplicable = replicableResult
replicationStatus sameCitationVisibilityNonreplicable = nonreplicableResult

citationReplicationDefect :
  INF.NonFactorabilityWitness citationVisibilitySurface replicationStatus
citationReplicationDefect = INF.nonFactorabilityWitness
  sameCitationVisibilityReplicable sameCitationVisibilityNonreplicable refl (λ ())

citationVisibilityCannotFactorReplicationStatus :
  INF.FactorsThrough citationVisibilitySurface replicationStatus → ⊥
citationVisibilityCannotFactorReplicationStatus =
  INF.witnessRulesOutEveryFlatFactorisation citationReplicationDefect

------------------------------------------------------------------------
-- Regression 2: primary-source role cannot recover proposition truth.
------------------------------------------------------------------------

data PrimaryTruthCase : Set where
  samePrimaryRoleAccurate samePrimaryRoleInaccurate : PrimaryTruthCase

data PrimaryRoleSurface : Set where samePrimarySourceRole : PrimaryRoleSurface
data PropositionTruth : Set where primaryClaimTrue primaryClaimFalse : PropositionTruth

primaryRoleSurface : PrimaryTruthCase → PrimaryRoleSurface
primaryRoleSurface _ = samePrimarySourceRole

primaryTruth : PrimaryTruthCase → PropositionTruth
primaryTruth samePrimaryRoleAccurate = primaryClaimTrue
primaryTruth samePrimaryRoleInaccurate = primaryClaimFalse

primaryTruthDefect : INF.NonFactorabilityWitness primaryRoleSurface primaryTruth
primaryTruthDefect = INF.nonFactorabilityWitness
  samePrimaryRoleAccurate samePrimaryRoleInaccurate refl (λ ())

primarySourceRoleCannotFactorTruth :
  INF.FactorsThrough primaryRoleSurface primaryTruth → ⊥
primarySourceRoleCannotFactorTruth =
  INF.witnessRulesOutEveryFlatFactorisation primaryTruthDefect

------------------------------------------------------------------------
-- Exact reuse: no new dependency/evidence-synthesis ontology.
------------------------------------------------------------------------

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

synthesisBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
synthesisBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

genealogyBoundary : Genealogy.ReplicationSourceGenealogyEvidenceSynthesisBoundary
genealogyBoundary = Genealogy.canonicalReplicationSourceGenealogyEvidenceSynthesisBoundary

cascadeBoundary : Cascade.InformationCascadeEvidenceDependencyHyperfabricBoundary
cascadeBoundary = Cascade.canonicalInformationCascadeEvidenceDependencyHyperfabricBoundary

qualityBoundary : Quality.DependencySourceQualityAttributionBoundary
qualityBoundary = Quality.canonicalDependencySourceQualityAttributionBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record CitationPrimaryReverseConstraint : Set where
  constructor citation-primary-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open CitationPrimaryReverseConstraint public

scienceConstraint : CitationPrimaryReverseConstraint
scienceConstraint = citation-primary-reverse-constraint
  "Science / publication / replication"
  "primary-source role, peer-review status, citation visibility, source quality, replication, dependence, synthesis and truth remain distinct"
  false

informationConstraint : CitationPrimaryReverseConstraint
informationConstraint = citation-primary-reverse-constraint
  "Bibliography / information science"
  "DOI/work identity, citation count, citation genealogy, canonical source, source role and evidentiary weight remain distinct"
  false

investigationConstraint : CitationPrimaryReverseConstraint
investigationConstraint = citation-primary-reverse-constraint
  "OSINT / historical / legal investigation"
  "primary-source designation identifies relation to the event/question; it does not create accuracy, independence, admissibility or proposition truth"
  false

------------------------------------------------------------------------
-- Attribution / no-promotion gates.
------------------------------------------------------------------------

data PrimarySourceMeansTrue : Set where
data CitationCountMeansEvidenceWeight : Set where
data HighlyCitedMeansReplicable : Set where
data DOIProvesIndependence : Set where
data QidProvesSourceQuality : Set where
data DeweyCreatesEvidenceHierarchy : Set where

primarySourceDoesNotMeanTrue : PrimarySourceMeansTrue → ⊥
primarySourceDoesNotMeanTrue ()

citationCountDoesNotMeanEvidenceWeight : CitationCountMeansEvidenceWeight → ⊥
citationCountDoesNotMeanEvidenceWeight ()

highCitationDoesNotMeanReplicable : HighlyCitedMeansReplicable → ⊥
highCitationDoesNotMeanReplicable ()

doiDoesNotProveIndependence : DOIProvesIndependence → ⊥
doiDoesNotProveIndependence ()

qidDoesNotProveSourceQuality : QidProvesSourceQuality → ⊥
qidDoesNotProveSourceQuality ()

deweyDoesNotCreateEvidenceHierarchy : DeweyCreatesEvidenceHierarchy → ⊥
deweyDoesNotCreateEvidenceHierarchy ()

record SourceGenealogyIndependenceEvidenceSynthesisBoundary : Set where
  constructor source-genealogy-independence-evidence-synthesis-boundary
  field
    existingDependencyOwnersReused : Bool
    primarySourceQidAttached : Bool
    primarySourceDeweyUnresolvedExplicitly : Bool
    doiAndCanonicalLinksRetained : Bool
    citationBiasSourcesAttributed : Bool
    citationVisibilitySeparatedFromReplicability : Bool
    primarySourceRoleSeparatedFromTruth : Bool
    qidDoiDeweySeparatedFromEvidenceWeight : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SourceGenealogyIndependenceEvidenceSynthesisBoundary public

canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary :
  SourceGenealogyIndependenceEvidenceSynthesisBoundary
canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary =
  source-genealogy-independence-evidence-synthesis-boundary
    true true true true true true true true true false

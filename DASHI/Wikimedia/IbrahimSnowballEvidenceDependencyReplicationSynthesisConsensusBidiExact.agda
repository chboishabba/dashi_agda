module DASHI.Wikimedia.IbrahimSnowballEvidenceDependencyReplicationSynthesisConsensusBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SourceProvenanceExact as Provenance
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as LearningMemory

------------------------------------------------------------------------
-- IBRAHIM / EVIDENCE DEPENDENCY / REPLICATION / SYNTHESIS / CONSENSUS BIDI
--
-- Multiplicity is not independence.  Evidence synthesis is not raw vote-counting.
-- A citation edge is not an evidentiary-independence edge.  A replication is
-- claim-relative new evidence, not merely a same-procedure label.  Consensus is
-- a community-level epistemic state, not proposition truth by definition.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-dependency/replication/synthesis/consensus BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create provenance independence, evidentiary weight, replication success, consensus truth or causal authority")

corroboratingEvidenceQid : Identity.ExternalIdentityDemand
corroboratingEvidenceQid = Testimony.corroboratingEvidenceQid

reproducibilityQid : Identity.ExternalIdentityDemand
reproducibilityQid = LearningMemory.reproducibilityQid

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = LearningMemory.scientificConsensusQid

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

citationAnalysisQid : Identity.ExternalIdentityDemand
citationAnalysisQid = mkQid "citation analysis" "Q206276"

citationPracticesQid : Identity.ExternalIdentityDemand
citationPracticesQid = mkQid "citation practices" "Q113997140"

commonSourceDependenceQid : Identity.ExternalIdentityDemand
commonSourceDependenceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-dependency/replication/synthesis/consensus BIDI"
  "external concept identity"
  "common-source evidentiary dependence / provenance dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single QID promoted for generic common-source evidentiary dependence; citation, reproducibility and corroboration identities remain separate")

------------------------------------------------------------------------
-- Dewey travels as navigation only.  No uninspected DDC is manufactured.
------------------------------------------------------------------------

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted in this pass"

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted in this pass"

citationAnalysisDewey : Dewey.DeweyCoordinate
citationAnalysisDewey = Dewey.mkUnresolvedDewey
  "citation analysis"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI/source line.
------------------------------------------------------------------------

nosekErringtonReplicationSource : Attribution.AttributedSource
nosekErringtonReplicationSource = Attribution.mkDOISource
  "Brian A. Nosek; Timothy M. Errington"
  "What is replication?"
  "PLOS Biology 18(3), e3000691"
  "2020"
  "10.1371/journal.pbio.3000691"
  "https://doi.org/10.1371/journal.pbio.3000691"
  Attribution.academicArticleSource
  "conceptual account defining replication as a study whose outcomes are diagnostic evidence about a prior claim; supports claim-relative replication rather than equating replication with procedural duplication"
  Attribution.publicAttribution

openScienceReplicationSource : Attribution.AttributedSource
openScienceReplicationSource = Attribution.mkDOISource
  "Open Science Collaboration"
  "Estimating the reproducibility of psychological science"
  "Science 349(6251), aac4716"
  "2015"
  "10.1126/science.aac4716"
  "https://doi.org/10.1126/science.aac4716"
  Attribution.academicArticleSource
  "large coordinated replication project in psychology; supports empirical study of reproducibility while remaining bounded to its sampled studies, designs and replication criteria"
  Attribution.publicAttribution

nosekOpenCultureSource : Attribution.AttributedSource
nosekOpenCultureSource = Attribution.mkDOISource
  "Brian A. Nosek et al."
  "Promoting an open research culture"
  "Science 348(6242), 1422-1425"
  "2015"
  "10.1126/science.aab2374"
  "https://doi.org/10.1126/science.aab2374"
  Attribution.academicArticleSource
  "open-science transparency and incentive framework; openness can improve inspectability but does not itself create truth or independent replication"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact upstream boundaries reused rather than replaced.
------------------------------------------------------------------------

learningMemoryBoundary : LearningMemory.LearningMemoryTraumaReplicationConsensusBoundary
learningMemoryBoundary = LearningMemory.canonicalLearningMemoryTraumaReplicationConsensusBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

sourceProvenanceBoundary : Provenance.SourceAttributionBoundary
sourceProvenanceBoundary = Provenance.canonicalSourceAttributionBoundary

------------------------------------------------------------------------
-- Regression 1: evidence/result count cannot recover dependency structure.
------------------------------------------------------------------------

data EvidenceBundleCase : Set where
  sameCountIndependentOrigins sameCountOneCommonOrigin : EvidenceBundleCase

data EvidenceCountSurface : Set where sameEvidenceMultiplicity : EvidenceCountSurface
data DependencyStructure : Set where provenanceIndependent commonSourceDependent : DependencyStructure

evidenceCountSurface : EvidenceBundleCase → EvidenceCountSurface
evidenceCountSurface _ = sameEvidenceMultiplicity

dependencyStructure : EvidenceBundleCase → DependencyStructure
dependencyStructure sameCountIndependentOrigins = provenanceIndependent
dependencyStructure sameCountOneCommonOrigin = commonSourceDependent

evidenceDependencyDefect : INF.NonFactorabilityWitness evidenceCountSurface dependencyStructure
evidenceDependencyDefect = INF.nonFactorabilityWitness
  sameCountIndependentOrigins sameCountOneCommonOrigin refl (λ ())

evidenceMultiplicityCannotFactorDependency :
  INF.FactorsThrough evidenceCountSurface dependencyStructure → ⊥
evidenceMultiplicityCannotFactorDependency =
  INF.witnessRulesOutEveryFlatFactorisation evidenceDependencyDefect

------------------------------------------------------------------------
-- Regression 2: citation multiplicity cannot recover independent evidence.
------------------------------------------------------------------------

data CitationCase : Set where
  sameCitationCountIndependentEvidence sameCitationCountDerivativeCopying : CitationCase

data CitationSurface : Set where sameCitationMultiplicity : CitationSurface
data EvidentiaryIndependence : Set where independentlyGeneratedEvidence derivativeCitationChain : EvidentiaryIndependence

citationSurface : CitationCase → CitationSurface
citationSurface _ = sameCitationMultiplicity

evidentiaryIndependence : CitationCase → EvidentiaryIndependence
evidentiaryIndependence sameCitationCountIndependentEvidence = independentlyGeneratedEvidence
evidentiaryIndependence sameCitationCountDerivativeCopying = derivativeCitationChain

citationIndependenceDefect : INF.NonFactorabilityWitness citationSurface evidentiaryIndependence
citationIndependenceDefect = INF.nonFactorabilityWitness
  sameCitationCountIndependentEvidence sameCitationCountDerivativeCopying refl (λ ())

citationMultiplicityCannotFactorIndependentEvidence :
  INF.FactorsThrough citationSurface evidentiaryIndependence → ⊥
citationMultiplicityCannotFactorIndependentEvidence =
  INF.witnessRulesOutEveryFlatFactorisation citationIndependenceDefect

------------------------------------------------------------------------
-- Regression 3: procedural similarity cannot recover replication role.
------------------------------------------------------------------------

data ReplicationRoleCase : Set where
  sameProcedureDiagnosticNewData sameProcedureNonDiagnosticReuse : ReplicationRoleCase

data ProcedureSurface : Set where sameProcedureSurface : ProcedureSurface
data ReplicationRole : Set where claimDiagnosticReplication nonDiagnosticReanalysis : ReplicationRole

procedureSurface : ReplicationRoleCase → ProcedureSurface
procedureSurface _ = sameProcedureSurface

replicationRole : ReplicationRoleCase → ReplicationRole
replicationRole sameProcedureDiagnosticNewData = claimDiagnosticReplication
replicationRole sameProcedureNonDiagnosticReuse = nonDiagnosticReanalysis

replicationRoleDefect : INF.NonFactorabilityWitness procedureSurface replicationRole
replicationRoleDefect = INF.nonFactorabilityWitness
  sameProcedureDiagnosticNewData sameProcedureNonDiagnosticReuse refl (λ ())

proceduralSimilarityCannotFactorReplicationRole :
  INF.FactorsThrough procedureSurface replicationRole → ⊥
proceduralSimilarityCannotFactorReplicationRole =
  INF.witnessRulesOutEveryFlatFactorisation replicationRoleDefect

------------------------------------------------------------------------
-- Regression 4: synthesis size cannot recover provenance-adjusted weight.
------------------------------------------------------------------------

data SynthesisCase : Set where
  sameStudyCountIndependentStudies sameStudyCountSharedData : SynthesisCase

data StudyCountSurface : Set where sameIncludedStudyCount : StudyCountSurface
data SynthesisWeight : Set where independentWeighting dependenceAdjustedWeighting : SynthesisWeight

studyCountSurface : SynthesisCase → StudyCountSurface
studyCountSurface _ = sameIncludedStudyCount

synthesisWeight : SynthesisCase → SynthesisWeight
synthesisWeight sameStudyCountIndependentStudies = independentWeighting
synthesisWeight sameStudyCountSharedData = dependenceAdjustedWeighting

synthesisWeightDefect : INF.NonFactorabilityWitness studyCountSurface synthesisWeight
synthesisWeightDefect = INF.nonFactorabilityWitness
  sameStudyCountIndependentStudies sameStudyCountSharedData refl (λ ())

studyCountCannotFactorProvenanceAdjustedWeight :
  INF.FactorsThrough studyCountSurface synthesisWeight → ⊥
studyCountCannotFactorProvenanceAdjustedWeight =
  INF.witnessRulesOutEveryFlatFactorisation synthesisWeightDefect

------------------------------------------------------------------------
-- Regression 5: consensus surface cannot recover dependency quality.
------------------------------------------------------------------------

data ConsensusDependencyCase : Set where
  sameConsensusIndependentBase sameConsensusConcentratedBase : ConsensusDependencyCase

data ConsensusSurface : Set where sameConsensusPosition : ConsensusSurface
data ConsensusDependencyQuality : Set where broadIndependentBase concentratedDependentBase : ConsensusDependencyQuality

consensusSurface : ConsensusDependencyCase → ConsensusSurface
consensusSurface _ = sameConsensusPosition

consensusDependencyQuality : ConsensusDependencyCase → ConsensusDependencyQuality
consensusDependencyQuality sameConsensusIndependentBase = broadIndependentBase
consensusDependencyQuality sameConsensusConcentratedBase = concentratedDependentBase

consensusDependencyDefect : INF.NonFactorabilityWitness consensusSurface consensusDependencyQuality
consensusDependencyDefect = INF.nonFactorabilityWitness
  sameConsensusIndependentBase sameConsensusConcentratedBase refl (λ ())

consensusCannotFactorEvidenceDependencyQuality :
  INF.FactorsThrough consensusSurface consensusDependencyQuality → ⊥
consensusCannotFactorEvidenceDependencyQuality =
  INF.witnessRulesOutEveryFlatFactorisation consensusDependencyDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record EvidenceDependencyReverseConstraint : Set where
  constructor evidence-dependency-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open EvidenceDependencyReverseConstraint public

scienceConstraint : EvidenceDependencyReverseConstraint
scienceConstraint = evidence-dependency-reverse-constraint
  "Science / replication / consensus"
  "claim identity, data origin, method, team, code/material reuse, replication role, result, uncertainty and consensus remain distinct"
  false

mediaConstraint : EvidenceDependencyReverseConstraint
mediaConstraint = evidence-dependency-reverse-constraint
  "Media / fact checking / information"
  "story count, original reporting, syndicated/derivative copying, cited primary source and independent corroboration remain distinct"
  false

legalConstraint : EvidenceDependencyReverseConstraint
legalConstraint = evidence-dependency-reverse-constraint
  "Law / testimony / corroboration"
  "witness count, testimony provenance, common prompting/source, admissibility, corroboration and factual finding remain distinct"
  false

memoryConstraint : EvidenceDependencyReverseConstraint
memoryConstraint = evidence-dependency-reverse-constraint
  "Memory / learning / trauma"
  "repeated report or retrieval, common encoding/post-event information, latent learning state and independent external corroboration remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CitationCountMeansIndependentEvidence : Set where
data ReplicationCountMeansIndependentEvidence : Set where
data SameProcedureMeansReplication : Set where
data MetaAnalysisMeansIndependentStudies : Set where
data SystematicReviewMeansTruth : Set where
data ConsensusMeansIndependentEvidenceBase : Set where
data OpenScienceMeansTruth : Set where
data QidMeansEvidenceWeight : Set where

citationCountDoesNotCreateIndependentEvidence : CitationCountMeansIndependentEvidence → ⊥
citationCountDoesNotCreateIndependentEvidence ()

replicationCountDoesNotCreateIndependentEvidence : ReplicationCountMeansIndependentEvidence → ⊥
replicationCountDoesNotCreateIndependentEvidence ()

sameProcedureDoesNotCreateReplicationRole : SameProcedureMeansReplication → ⊥
sameProcedureDoesNotCreateReplicationRole ()

metaAnalysisDoesNotCreateIndependentStudies : MetaAnalysisMeansIndependentStudies → ⊥
metaAnalysisDoesNotCreateIndependentStudies ()

systematicReviewDoesNotCreateTruth : SystematicReviewMeansTruth → ⊥
systematicReviewDoesNotCreateTruth ()

consensusDoesNotCreateIndependentEvidenceBase : ConsensusMeansIndependentEvidenceBase → ⊥
consensusDoesNotCreateIndependentEvidenceBase ()

openScienceDoesNotCreateTruth : OpenScienceMeansTruth → ⊥
openScienceDoesNotCreateTruth ()

qidDoesNotCreateEvidenceWeight : QidMeansEvidenceWeight → ⊥
qidDoesNotCreateEvidenceWeight ()

record EvidenceDependencyReplicationSynthesisBoundary : Set where
  constructor evidence-dependency-replication-synthesis-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    ambiguousCommonSourceQidRetainedExplicitly : Bool
    deweyUnresolvedStateRetained : Bool
    doiSourceRolesRetained : Bool
    sourceProvenanceLayerReused : Bool
    evidenceMultiplicitySeparatedFromDependency : Bool
    citationMultiplicitySeparatedFromIndependence : Bool
    proceduralSimilaritySeparatedFromReplicationRole : Bool
    synthesisSizeSeparatedFromAdjustedWeight : Bool
    consensusSeparatedFromDependencyQuality : Bool
    traumaMemoryRepeatedSurfaceBoundaryRetained : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceDependencyReplicationSynthesisBoundary public

canonicalEvidenceDependencyReplicationSynthesisBoundary :
  EvidenceDependencyReplicationSynthesisBoundary
canonicalEvidenceDependencyReplicationSynthesisBoundary =
  evidence-dependency-replication-synthesis-boundary
    true true true true true true true true true true true true false

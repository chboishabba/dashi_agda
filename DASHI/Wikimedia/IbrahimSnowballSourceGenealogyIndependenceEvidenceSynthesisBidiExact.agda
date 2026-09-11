module DASHI.Wikimedia.IbrahimSnowballSourceGenealogyIndependenceEvidenceSynthesisBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony

------------------------------------------------------------------------
-- IBRAHIM / SOURCE-GENEALOGY / INDEPENDENCE / EVIDENCE-SYNTHESIS BIDI
--
-- The high-alpha residual after corroboration/replication is genealogy:
-- how many apparently distinct reports, papers, URLs, witnesses or reviews
-- descend from genuinely independent evidentiary origins?
--
-- QID identifies a concept/publication type. DOI/canonical URL identifies a
-- source object. Dewey supplies a library/navigation coordinate when safely
-- inspected. None supplies independence, methodological quality, truth or
-- evidentiary weight. Those remain consumer-indexed Snowball obligations.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim source-genealogy/independence/evidence-synthesis BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create source independence, methodological quality, truth, evidentiary weight or authority")

primarySourceQid : Identity.ExternalIdentityDemand
primarySourceQid = mkQid "primary source" "Q112754"

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
  "Ibrahim source-genealogy/independence/evidence-synthesis BIDI"
  "external concept identity"
  "source genealogy / common-source dependence"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact single Wikidata concept promoted for provenance genealogy/common-source dependence; retain as a Snowball consumer rather than substitute a nearby citation-network concept")

------------------------------------------------------------------------
-- Dewey stays classification/navigation only. No uninspected number is inferred
-- from publication type or QID.
------------------------------------------------------------------------

primarySourceDewey : Dewey.DeweyCoordinate
primarySourceDewey = Dewey.mkUnresolvedDewey
  "primary source"
  "no exact inspected DDC value promoted from Q112754 in this pass"

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted from Q1504425 in this pass"

metaAnalysisDewey : Dewey.DeweyCoordinate
metaAnalysisDewey = Dewey.mkUnresolvedDewey
  "meta-analysis"
  "no exact inspected DDC value promoted from Q815382 in this pass"

------------------------------------------------------------------------
-- Source-bounded evidence about citation/replication distortions.
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
  "observational analysis of three replication-project corpora finding higher citation of nonreplicable papers and limited post-failure acknowledgement; citation count is not treated as replication success, independence or truth"
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
  "systematic review/meta-analysis of citation bias; supports treating citation frequency as a biased dissemination signal rather than an independence or truth count"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: citation multiplicity cannot recover independent origin count.
------------------------------------------------------------------------

data CitationCase : Set where
  sameCitationCountIndependentOrigins sameCitationCountSingleAncestralOrigin : CitationCase

data CitationSurface : Set where sameCitationMultiplicity : CitationSurface
data OriginIndependence : Set where multipleIndependentOrigins commonAncestralOrigin : OriginIndependence

citationSurface : CitationCase → CitationSurface
citationSurface _ = sameCitationMultiplicity

originIndependence : CitationCase → OriginIndependence
originIndependence sameCitationCountIndependentOrigins = multipleIndependentOrigins
originIndependence sameCitationCountSingleAncestralOrigin = commonAncestralOrigin

citationGenealogyDefect : INF.NonFactorabilityWitness citationSurface originIndependence
citationGenealogyDefect = INF.nonFactorabilityWitness
  sameCitationCountIndependentOrigins sameCitationCountSingleAncestralOrigin refl (λ ())

citationMultiplicityCannotFactorIndependentOrigins :
  INF.FactorsThrough citationSurface originIndependence → ⊥
citationMultiplicityCannotFactorIndependentOrigins =
  INF.witnessRulesOutEveryFlatFactorisation citationGenealogyDefect

------------------------------------------------------------------------
-- Regression 2: publication count cannot recover primary-evidence diversity.
------------------------------------------------------------------------

data PublicationCase : Set where
  samePublicationCountIndependentPrimaryStudies samePublicationCountSharedPrimaryStudy : PublicationCase

data PublicationSurface : Set where samePublicationMultiplicity : PublicationSurface
data PrimaryEvidenceDiversity : Set where independentPrimaryEvidence sharedPrimaryEvidence : PrimaryEvidenceDiversity

publicationSurface : PublicationCase → PublicationSurface
publicationSurface _ = samePublicationMultiplicity

primaryEvidenceDiversity : PublicationCase → PrimaryEvidenceDiversity
primaryEvidenceDiversity samePublicationCountIndependentPrimaryStudies = independentPrimaryEvidence
primaryEvidenceDiversity samePublicationCountSharedPrimaryStudy = sharedPrimaryEvidence

publicationPrimaryDefect : INF.NonFactorabilityWitness publicationSurface primaryEvidenceDiversity
publicationPrimaryDefect = INF.nonFactorabilityWitness
  samePublicationCountIndependentPrimaryStudies samePublicationCountSharedPrimaryStudy refl (λ ())

publicationMultiplicityCannotFactorPrimaryEvidenceDiversity :
  INF.FactorsThrough publicationSurface primaryEvidenceDiversity → ⊥
publicationMultiplicityCannotFactorPrimaryEvidenceDiversity =
  INF.witnessRulesOutEveryFlatFactorisation publicationPrimaryDefect

------------------------------------------------------------------------
-- Regression 3: synthesis label cannot recover independence/method quality.
------------------------------------------------------------------------

data SynthesisCase : Set where
  sameMetaAnalysisLabelIndependentInputs sameMetaAnalysisLabelDependentInputs : SynthesisCase

data SynthesisSurface : Set where sameEvidenceSynthesisLabel : SynthesisSurface
data SynthesisIndependence : Set where synthesisInputsIndependent synthesisInputsDependent : SynthesisIndependence

synthesisSurface : SynthesisCase → SynthesisSurface
synthesisSurface _ = sameEvidenceSynthesisLabel

synthesisIndependence : SynthesisCase → SynthesisIndependence
synthesisIndependence sameMetaAnalysisLabelIndependentInputs = synthesisInputsIndependent
synthesisIndependence sameMetaAnalysisLabelDependentInputs = synthesisInputsDependent

synthesisIndependenceDefect : INF.NonFactorabilityWitness synthesisSurface synthesisIndependence
synthesisIndependenceDefect = INF.nonFactorabilityWitness
  sameMetaAnalysisLabelIndependentInputs sameMetaAnalysisLabelDependentInputs refl (λ ())

evidenceSynthesisLabelCannotFactorInputIndependence :
  INF.FactorsThrough synthesisSurface synthesisIndependence → ⊥
evidenceSynthesisLabelCannotFactorInputIndependence =
  INF.witnessRulesOutEveryFlatFactorisation synthesisIndependenceDefect

------------------------------------------------------------------------
-- Regression 4: primary-source classification cannot recover proposition truth.
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
-- Existing boundaries reused: acquisition, archive/history, testimony and
-- replication/consensus remain authoritative for their own consumers.
------------------------------------------------------------------------

acquisitionBoundary : Acquisition.SourceAcquisitionBoundary
acquisitionBoundary = Acquisition.canonicalSourceAcquisitionBoundary

archiveBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

priorReplicationBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorReplicationBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parent nodes.
------------------------------------------------------------------------

record SourceGenealogyReverseConstraint : Set where
  constructor source-genealogy-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SourceGenealogyReverseConstraint public

informationConstraint : SourceGenealogyReverseConstraint
informationConstraint = source-genealogy-reverse-constraint
  "Information science / bibliography"
  "document identity, citation edge, canonical source, source role, acquisition state and ancestral origin remain distinct"
  false

scienceConstraint : SourceGenealogyReverseConstraint
scienceConstraint = source-genealogy-reverse-constraint
  "Science / replication / evidence synthesis"
  "primary study, replication, reused dataset/method, systematic review, meta-analysis, reproducibility and consensus remain distinct"
  false

mediaOsintConstraint : SourceGenealogyReverseConstraint
mediaOsintConstraint = source-genealogy-reverse-constraint
  "Media / OSINT / investigation"
  "different URLs/accounts/posts do not become independent sources until common-origin and copying/republication genealogy are audited"
  false

lawHistoryConstraint : SourceGenealogyReverseConstraint
lawHistoryConstraint = source-genealogy-reverse-constraint
  "Law / history / testimony"
  "multiple exhibits, witnesses or surviving accounts do not become independent corroboration merely by multiplicity; provenance genealogy must survive"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data PrimarySourceMeansTrue : Set where
data SystematicReviewMeansIndependentInputs : Set where
data MetaAnalysisMeansCausalProof : Set where
data CitationCountMeansEvidenceWeight : Set where
data DistinctUrlsMeanIndependentSources : Set where
data DOIProvesMethodIndependence : Set where
data QidProvesSourceRole : Set where
data DeweyCreatesEvidenceHierarchy : Set where

primarySourceDoesNotMeanTrue : PrimarySourceMeansTrue → ⊥
primarySourceDoesNotMeanTrue ()

systematicReviewDoesNotMeanIndependentInputs : SystematicReviewMeansIndependentInputs → ⊥
systematicReviewDoesNotMeanIndependentInputs ()

metaAnalysisDoesNotMeanCausalProof : MetaAnalysisMeansCausalProof → ⊥
metaAnalysisDoesNotMeanCausalProof ()

citationCountDoesNotMeanEvidenceWeight : CitationCountMeansEvidenceWeight → ⊥
citationCountDoesNotMeanEvidenceWeight ()

distinctUrlsDoNotMeanIndependentSources : DistinctUrlsMeanIndependentSources → ⊥
distinctUrlsDoNotMeanIndependentSources ()

doiDoesNotProveMethodIndependence : DOIProvesMethodIndependence → ⊥
doiDoesNotProveMethodIndependence ()

qidDoesNotProveSourceRole : QidProvesSourceRole → ⊥
qidDoesNotProveSourceRole ()

deweyDoesNotCreateEvidenceHierarchy : DeweyCreatesEvidenceHierarchy → ⊥
deweyDoesNotCreateEvidenceHierarchy ()

record SourceGenealogyIndependenceEvidenceSynthesisBoundary : Set where
  constructor source-genealogy-independence-evidence-synthesis-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    unresolvedGenealogyQidRetainedExplicitly : Bool
    deweyUnresolvedStateRetained : Bool
    doiAndCanonicalLinksRetained : Bool
    primarySourceRoleSeparatedFromTruth : Bool
    citationMultiplicitySeparatedFromIndependence : Bool
    publicationMultiplicitySeparatedFromPrimaryDiversity : Bool
    evidenceSynthesisSeparatedFromInputIndependence : Bool
    replicationAndConsensusBoundariesReused : Bool
    sourceAcquisitionAndArchiveBoundariesReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open SourceGenealogyIndependenceEvidenceSynthesisBoundary public

canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary :
  SourceGenealogyIndependenceEvidenceSynthesisBoundary
canonicalSourceGenealogyIndependenceEvidenceSynthesisBoundary =
  source-genealogy-independence-evidence-synthesis-boundary
    true true true true true true true true true true true false

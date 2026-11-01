module DASHI.Wikimedia.IbrahimSnowballDependencySourceQualityAttributionDeltaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballInformationCascadeEvidenceDependencyHyperfabricBidiExact as Cascade

------------------------------------------------------------------------
-- THIN DELTA ONLY.
--
-- The canonical Dependency/Cascade owners already pay:
--   multiplicity != independence,
--   agreement != independent consensus,
--   dependence != zero evidence,
--   dependency topology != evidential contribution.
--
-- This module adds only the surviving source-quality distinction and a fuller
-- attribution receipt for Pilditch-Hahn-Lagnado's version-of-record/preprint
-- relationship.  No parallel dependency ontology is introduced.
------------------------------------------------------------------------

pilditchVersionOfRecord = Dependency.pilditchDependencySource

pilditchPreprintDoi : Identity.ExternalIdentityDemand
pilditchPreprintDoi = Identity.mkOptionalIdentityDemand
  "Pilditch-Hahn-Lagnado dependency attribution"
  "preprint identity retained separately from version of record"
  "The problem of dependency preprint"
  Identity.doi
  (Identity.verified "10.31234/osf.io/d2b6e"
    "preprint DOI reported by the 2025 Synthese version of record; final DOI 10.1007/s11229-025-04969-w remains authoritative bibliographic identity for the published article")

dependencyQid = Dependency.sourceIndependenceQid

dependencyDewey : Dewey.DeweyCoordinate
dependencyDewey = Dependency.sourceDependencyDewey

record PilditchAttributionReceipt : Set where
  constructor pilditch-attribution-receipt
  field
    sourceRole : String
    publisherClassification : String
    finalDoi : String
    finalCanonicalLink : String
    preprintDoi : String
    publicationDate : String
    finalAndPreprintAreNotSilentlyCollapsed : Bool
    citationImportsNormativeAuthority : Bool
open PilditchAttributionReceipt public

pilditchAttribution : PilditchAttributionReceipt
pilditchAttribution = pilditch-attribution-receipt
  "primary theoretical/original-research source for the paper's own analysis of evidential dependence; not primary empirical evidence for every real-world dependency graph"
  "Springer Nature: Original Research"
  "10.1007/s11229-025-04969-w"
  "https://doi.org/10.1007/s11229-025-04969-w"
  "10.31234/osf.io/d2b6e"
  "2025-03-28"
  true
  false

------------------------------------------------------------------------
-- Surviving regression: source independence cannot recover source quality.
--
-- Independence and dependence describe information genealogy. Reliability,
-- measurement validity, relevance, calibration and domain fit remain separate
-- evidential coordinates. Independent sources can all be poor sources.
------------------------------------------------------------------------

data IndependentEvidenceCase : Set where
  independentHighQuality independentLowQuality : IndependentEvidenceCase

data IndependenceSurface : Set where independentlyGenerated : IndependenceSurface
data SourceQuality : Set where comparativelyHighQuality comparativelyLowQuality : SourceQuality

independenceSurface : IndependentEvidenceCase → IndependenceSurface
independenceSurface _ = independentlyGenerated

sourceQuality : IndependentEvidenceCase → SourceQuality
sourceQuality independentHighQuality = comparativelyHighQuality
sourceQuality independentLowQuality = comparativelyLowQuality

independenceQualityDefect : INF.NonFactorabilityWitness independenceSurface sourceQuality
independenceQualityDefect = INF.nonFactorabilityWitness
  independentHighQuality independentLowQuality refl (λ ())

independenceCannotFactorSourceQuality :
  INF.FactorsThrough independenceSurface sourceQuality → ⊥
independenceCannotFactorSourceQuality =
  INF.witnessRulesOutEveryFlatFactorisation independenceQualityDefect

------------------------------------------------------------------------
-- Existing exact boundaries reused.
------------------------------------------------------------------------

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

synthesisBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
synthesisBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

cascadeBoundary : Cascade.InformationCascadeEvidenceDependencyHyperfabricBoundary
cascadeBoundary = Cascade.canonicalInformationCascadeEvidenceDependencyHyperfabricBoundary

------------------------------------------------------------------------
-- Reverse BIDI constraint: independence is one axis, not a quality certificate.
------------------------------------------------------------------------

record SourceQualityReverseConstraint : Set where
  constructor source-quality-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open SourceQualityReverseConstraint public

canonicalSourceQualityConstraint : SourceQualityReverseConstraint
canonicalSourceQualityConstraint = source-quality-reverse-constraint
  "Evidence / source independence / replication"
  "source genealogy, independence, reliability, measurement validity, relevance, calibration, domain fit, evidential contribution and truth remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data IndependenceMeansReliable : Set where
data DependenceMeansWorthless : Set where
data PreprintEqualsVersionOfRecord : Set where
data DOIImportsAuthority : Set where

independenceDoesNotMeanReliable : IndependenceMeansReliable → ⊥
independenceDoesNotMeanReliable ()

dependenceStillDoesNotMeanWorthless : DependenceMeansWorthless → ⊥
dependenceStillDoesNotMeanWorthless ()

preprintDoesNotSilentlyEqualVersionOfRecord : PreprintEqualsVersionOfRecord → ⊥
preprintDoesNotSilentlyEqualVersionOfRecord ()

doiDoesNotImportAuthority : DOIImportsAuthority → ⊥
doiDoesNotImportAuthority ()

record DependencySourceQualityAttributionBoundary : Set where
  constructor dependency-source-quality-attribution-boundary
  field
    canonicalDependencyOwnerReused : Bool
    canonicalCascadeOwnerReused : Bool
    finalDoiRetained : Bool
    canonicalLinkRetained : Bool
    preprintDoiRetainedSeparately : Bool
    exactDependencyQidRemainsUnresolved : Bool
    exactDependencyDeweyRemainsUnresolved : Bool
    primarySourceRoleBounded : Bool
    independenceSeparatedFromReliability : Bool
    dependenceSeparatedFromWorthlessness : Bool
    attributionDoesNotImportAuthority : Bool
    presentAxisVocabularyClaimedComplete : Bool
open DependencySourceQualityAttributionBoundary public

canonicalDependencySourceQualityAttributionBoundary :
  DependencySourceQualityAttributionBoundary
canonicalDependencySourceQualityAttributionBoundary =
  dependency-source-quality-attribution-boundary
    true true true true true true true true true true true false

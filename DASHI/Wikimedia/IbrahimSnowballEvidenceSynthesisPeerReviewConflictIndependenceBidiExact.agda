module DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact where

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
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as MemoryReplication

------------------------------------------------------------------------
-- IBRAHIM / EVIDENCE-SYNTHESIS / PEER-REVIEW / INDEPENDENCE BIDI
--
-- This is a compression layer over the preceding testimony, memory,
-- replication, common-source and consensus owners.  It does not create a new
-- epistemology.  It makes explicit that systematic review, peer review,
-- publication count, consensus, conflict-of-interest and source independence
-- are different coordinates.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/peer-review/independence BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create truth, independence, quality, consensus or evidential authority")

systematicReviewQid : Identity.ExternalIdentityDemand
systematicReviewQid = mkQid "systematic review" "Q1504425"

peerReviewQid : Identity.ExternalIdentityDemand
peerReviewQid = mkQid "peer review" "Q215028"

conflictOfInterestQid : Identity.ExternalIdentityDemand
conflictOfInterestQid = mkQid "conflict of interest" "Q211067"

scientificConsensusQid : Identity.ExternalIdentityDemand
scientificConsensusQid = MemoryReplication.scientificConsensusQid

metaAnalysisQid : Identity.ExternalIdentityDemand
metaAnalysisQid = mkQid "meta-analysis" "Q815382"

evidenceSynthesisQid : Identity.ExternalIdentityDemand
evidenceSynthesisQid = Identity.mkOptionalIdentityDemand
  "Ibrahim evidence-synthesis/peer-review/independence BIDI"
  "external concept identity"
  "evidence synthesis"
  Identity.wikidataQid
  (Identity.unresolved
    "a recently created Wikidata item exists for evidence synthesis, but no mature exact concept identity is promoted here")

systematicReviewDewey : Dewey.DeweyCoordinate
systematicReviewDewey = Dewey.mkUnresolvedDewey
  "systematic review"
  "no exact inspected DDC value promoted in this pass"

peerReviewDewey : Dewey.DeweyCoordinate
peerReviewDewey = Dewey.mkUnresolvedDewey
  "peer review"
  "no exact inspected DDC value promoted in this pass"

conflictOfInterestDewey : Dewey.DeweyCoordinate
conflictOfInterestDewey = Dewey.mkUnresolvedDewey
  "conflict of interest"
  "cross-domain legal/scientific/organizational concept; no exact DDC value promoted"

glaeserResearchIndependenceSource : Attribution.AttributedSource
glaeserResearchIndependenceSource = Attribution.mkDOISource
  "Jochen Gläser; Mitchell Ash; Guido Buenstorf; David Hopf; Lara Hubenschmid; Melike Janßen; Grit Laudel; Uwe Schimank; Marlene Stoll; Torsten Wilholt; Lothar Zechlin; Klaus Lieb"
  "The Independence of Research—A Review of Disciplinary Perspectives and Outline of Interdisciplinary Prospects"
  "Minerva 60, 105-138"
  "2022"
  "10.1007/s11024-021-09451-8"
  "https://doi.org/10.1007/s11024-021-09451-8"
  Attribution.academicArticleSource
  "interdisciplinary review treating research independence as a multidimensional and degree-valued problem; does not reduce independence to one scalar or imply that independence alone establishes truth"
  Attribution.publicAttribution

landesVarietyEvidenceSource : Attribution.AttributedSource
landesVarietyEvidenceSource = Attribution.mkDOISource
  "Jürgen Landes"
  "The variety of evidence thesis and its independence of degrees of independence"
  "Synthese 198, 10611-10641"
  "2021"
  "10.1007/s11229-020-02738-5"
  "https://doi.org/10.1007/s11229-020-02738-5"
  Attribution.academicArticleSource
  "philosophy-of-science analysis separating evidential variety from degrees of independence; source role is formal/epistemological analysis, not a universal empirical weighting rule"
  Attribution.publicAttribution

danchevDecentralizedReplicationSource : Attribution.AttributedSource
danchevDecentralizedReplicationSource = Attribution.mkDOISource
  "Valentin Danchev; Andrey Rzhetsky; James A. Evans"
  "Centralized scientific communities are less likely to generate replicable results"
  "eLife 8:e43094"
  "2019"
  "10.7554/eLife.43094"
  "https://doi.org/10.7554/eLife.43094"
  Attribution.academicArticleSource
  "large biomedical meta-research study relating social, methodological and knowledge independence to replication; bounded to its data and design and not a theorem that decentralization always guarantees truth"
  Attribution.publicAttribution

dependencyBoundary : Dependency.MemoryRepetitionSourceDependencyConsensusBoundary
dependencyBoundary = Dependency.canonicalMemoryRepetitionSourceDependencyConsensusBoundary

memoryReplicationBoundary : MemoryReplication.LearningMemoryTraumaReplicationConsensusBoundary
memoryReplicationBoundary = MemoryReplication.canonicalLearningMemoryTraumaReplicationConsensusBoundary

data ReviewCase : Set where
  sameReviewLabelIndependentCorpus sameReviewLabelCommonSourceCorpus : ReviewCase

data ReviewSurface : Set where sameSystematicReviewSurface : ReviewSurface
data CorpusIndependence : Set where independentlyGeneratedCorpus commonSourceDependentCorpus : CorpusIndependence

reviewSurface : ReviewCase → ReviewSurface
reviewSurface _ = sameSystematicReviewSurface

corpusIndependence : ReviewCase → CorpusIndependence
corpusIndependence sameReviewLabelIndependentCorpus = independentlyGeneratedCorpus
corpusIndependence sameReviewLabelCommonSourceCorpus = commonSourceDependentCorpus

reviewIndependenceDefect : INF.NonFactorabilityWitness reviewSurface corpusIndependence
reviewIndependenceDefect = INF.nonFactorabilityWitness
  sameReviewLabelIndependentCorpus sameReviewLabelCommonSourceCorpus refl (λ ())

systematicReviewCannotFactorCorpusIndependence :
  INF.FactorsThrough reviewSurface corpusIndependence → ⊥
systematicReviewCannotFactorCorpusIndependence =
  INF.witnessRulesOutEveryFlatFactorisation reviewIndependenceDefect

data PeerReviewCase : Set where
  samePeerReviewedClaimTrue samePeerReviewedClaimFalse : PeerReviewCase

data PeerReviewSurface : Set where peerReviewed : PeerReviewSurface
data ClaimTruth : Set where claimTrue claimFalse : ClaimTruth

peerReviewSurface : PeerReviewCase → PeerReviewSurface
peerReviewSurface _ = peerReviewed

claimTruth : PeerReviewCase → ClaimTruth
claimTruth samePeerReviewedClaimTrue = claimTrue
claimTruth samePeerReviewedClaimFalse = claimFalse

peerReviewTruthDefect : INF.NonFactorabilityWitness peerReviewSurface claimTruth
peerReviewTruthDefect = INF.nonFactorabilityWitness
  samePeerReviewedClaimTrue samePeerReviewedClaimFalse refl (λ ())

peerReviewCannotFactorTruth : INF.FactorsThrough peerReviewSurface claimTruth → ⊥
peerReviewCannotFactorTruth = INF.witnessRulesOutEveryFlatFactorisation peerReviewTruthDefect

data ConflictCase : Set where
  sameConflictClaimTrue sameConflictClaimFalse : ConflictCase

data ConflictSurface : Set where declaredConflict : ConflictSurface

conflictSurface : ConflictCase → ConflictSurface
conflictSurface _ = declaredConflict

conflictClaimTruth : ConflictCase → ClaimTruth
conflictClaimTruth sameConflictClaimTrue = claimTrue
conflictClaimTruth sameConflictClaimFalse = claimFalse

conflictTruthDefect : INF.NonFactorabilityWitness conflictSurface conflictClaimTruth
conflictTruthDefect = INF.nonFactorabilityWitness
  sameConflictClaimTrue sameConflictClaimFalse refl (λ ())

conflictOfInterestCannotFactorTruth : INF.FactorsThrough conflictSurface conflictClaimTruth → ⊥
conflictOfInterestCannotFactorTruth = INF.witnessRulesOutEveryFlatFactorisation conflictTruthDefect

data NoConflictCase : Set where
  noDeclaredConflictIndependent noDeclaredConflictDependent : NoConflictCase

data NoConflictSurface : Set where noDeclaredConflict : NoConflictSurface
data IndependenceStatus : Set where independent dependent : IndependenceStatus

noConflictSurface : NoConflictCase → NoConflictSurface
noConflictSurface _ = noDeclaredConflict

independenceStatus : NoConflictCase → IndependenceStatus
independenceStatus noDeclaredConflictIndependent = independent
independenceStatus noDeclaredConflictDependent = dependent

noConflictIndependenceDefect : INF.NonFactorabilityWitness noConflictSurface independenceStatus
noConflictIndependenceDefect = INF.nonFactorabilityWitness
  noDeclaredConflictIndependent noDeclaredConflictDependent refl (λ ())

absenceOfDeclaredConflictCannotFactorIndependence :
  INF.FactorsThrough noConflictSurface independenceStatus → ⊥
absenceOfDeclaredConflictCannotFactorIndependence =
  INF.witnessRulesOutEveryFlatFactorisation noConflictIndependenceDefect

record EvidenceSynthesisReverseConstraint : Set where
  constructor evidence-synthesis-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open EvidenceSynthesisReverseConstraint public

scienceConstraint : EvidenceSynthesisReverseConstraint
scienceConstraint = evidence-synthesis-reverse-constraint
  "Science / scientific method"
  "study count, peer review, methodological diversity, social independence, knowledge independence, replication and proposition truth remain distinct"
  false

knowledgeConstraint : EvidenceSynthesisReverseConstraint
knowledgeConstraint = evidence-synthesis-reverse-constraint
  "Knowledge / evidence synthesis"
  "source inclusion, source genealogy, dependence, evidential variety, weighting, uncertainty and synthesis conclusion remain distinct"
  false

institutionConstraint : EvidenceSynthesisReverseConstraint
institutionConstraint = evidence-synthesis-reverse-constraint
  "Institutions / expertise / governance"
  "conflict declaration, structural dependence, funding/incentives, expertise, review status and truth remain distinct"
  false

memoryConstraint : EvidenceSynthesisReverseConstraint
memoryConstraint = evidence-synthesis-reverse-constraint
  "Memory / learning / social transmission"
  "repetition, common informational origin, retrieval history, social copying and independent acquisition remain distinct"
  false

data SystematicReviewCreatesIndependence : Set where
data PeerReviewCreatesTruth : Set where
data ConflictOfInterestCreatesFalsehood : Set where
data NoConflictCreatesIndependence : Set where
data ConsensusCreatesIndependentEvidence : Set where
data QidCreatesQuality : Set where

systematicReviewDoesNotCreateIndependence : SystematicReviewCreatesIndependence → ⊥
systematicReviewDoesNotCreateIndependence ()

peerReviewDoesNotCreateTruth : PeerReviewCreatesTruth → ⊥
peerReviewDoesNotCreateTruth ()

conflictOfInterestDoesNotCreateFalsehood : ConflictOfInterestCreatesFalsehood → ⊥
conflictOfInterestDoesNotCreateFalsehood ()

noDeclaredConflictDoesNotCreateIndependence : NoConflictCreatesIndependence → ⊥
noDeclaredConflictDoesNotCreateIndependence ()

consensusDoesNotCreateIndependentEvidence : ConsensusCreatesIndependentEvidence → ⊥
consensusDoesNotCreateIndependentEvidence ()

qidDoesNotCreateReviewQuality : QidCreatesQuality → ⊥
qidDoesNotCreateReviewQuality ()

record EvidenceSynthesisPeerReviewIndependenceBoundary : Set where
  constructor evidence-synthesis-peer-review-independence-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    metaAnalysisQidResolved : Bool
    deweyUnresolvedStatesRetained : Bool
    doiAndSourceRoleRetained : Bool
    systematicReviewSeparatedFromCorpusIndependence : Bool
    peerReviewSeparatedFromTruth : Bool
    conflictOfInterestSeparatedFromFalsehood : Bool
    absenceOfConflictSeparatedFromIndependence : Bool
    priorDependencyAndMemoryHyperfabricReused : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open EvidenceSynthesisPeerReviewIndependenceBoundary public

canonicalEvidenceSynthesisPeerReviewIndependenceBoundary : EvidenceSynthesisPeerReviewIndependenceBoundary
canonicalEvidenceSynthesisPeerReviewIndependenceBoundary =
  evidence-synthesis-peer-review-independence-boundary
    true true true true true true true true true true false

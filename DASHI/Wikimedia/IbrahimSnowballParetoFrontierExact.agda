module DASHI.Wikimedia.IbrahimSnowballParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Roadmap
import DASHI.Wikimedia.IbrahimSnowballArchiveHistoriographyCausalityBidiExact as Archive
import DASHI.Wikimedia.IbrahimSnowballSensibLawEvidenceObservationTestimonyCausationBidiExact as Evidence
import DASHI.Wikimedia.IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact as Testimony
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Learning
import DASHI.Wikimedia.IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact as Verification
import DASHI.Wikimedia.IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact as Skepticism
import DASHI.Wikimedia.IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact as Distrust
import DASHI.Wikimedia.IbrahimSnowballQiHexagramWitchDivinationBidiExact as Symbolic

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL PARETO FRONTIER
--
-- This is a navigation/proof-search owner, not a second planner or ontology.
-- It re-baselines the old Ibrahim roadmap after the recent Snowball tranches.
--
-- Priority is qualitative Pareto dominance: prefer a residual when paying it
-- unlocks more already-live consumers while requiring less new ontology.
-- QID/Dewey/DOI/source role are acquisition coordinates; none creates proof.
------------------------------------------------------------------------

data FrontierStatus : Set where
  substantiallyPaid : FrontierStatus
  liveResidual : FrontierStatus
  sourceArchaeologyResidual : FrontierStatus
  opportunisticMetadataResidual : FrontierStatus

record ParetoFrontierLeaf : Set where
  constructor pareto-frontier-leaf
  field
    rank : Nat
    status : FrontierStatus
    surface : String
    paidBy : String
    survivingResidual : String
    completionTest : String
    unlocks : String
    requiresNewOntology : Bool
    qidDebtCanBlockDomainWork : Bool
    deweyDebtCanBlockDomainWork : Bool
    doiDebtCanBlockDomainWork : Bool
open ParetoFrontierLeaf public

------------------------------------------------------------------------
-- Rank 1: provenance independence / common-source dependence.
--
-- This is now the highest-alpha shared residual because it simultaneously
-- constrains witness corroboration, scientific replication, journalism/media,
-- OSINT, archival reconstruction, expert evidence and AI-generated summaries.
------------------------------------------------------------------------

provenanceIndependenceFrontier : ParetoFrontierLeaf
provenanceIndependenceFrontier = pareto-frontier-leaf
  1 liveResidual
  "Corroboration <-> replication <-> provenance independence <-> common-source dependence <-> consensus"
  "IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact; IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact; WitchTrialEvidenceSubjectAttributionExact; SourceAcquisitionGeometryExact"
  "promote provenance genealogy itself to an inspectable cross-domain relation: repeated reports/results may share source, dataset, code, prompt, archive, interrogation lineage or citation ancestry"
  "same multiplicity with independent versus shared provenance is represented without consumer-specific duplication; independence can be inspected before corroboration/replication/consensus promotion"
  "OSINT/Amy; science replication; media copying; expert consensus; historical archives; witness corroboration; AI summaries"
  false false false false

------------------------------------------------------------------------
-- Rank 2: Ibrahim historical-runtime same-object closure.
--
-- Current graph traversal remains navigation-valid even when exact 2014 runtime
-- bytes are unpaid, but historical-edge claims require exact dump/parser
-- identity before promotion.
------------------------------------------------------------------------

historicalRuntimeFrontier : ParetoFrontierLeaf
historicalRuntimeFrontier = pareto-frontier-leaf
  2 sourceArchaeologyResidual
  "Ibrahim English Wikipedia November-2014 runtime identity and parser-equivalent reproduction"
  "WikipediaFirstLinkNetworkExact; current Ibrahim traversal/coverage owners; source-bound 2016/2017 Ibrahim publication attribution"
  "exact November-2014 dump day/file plus parser-equivalent reproduction for historical first-link edges not directly printed in the paper"
  "a claimed historical edge can name exact snapshot bytes and parsing semantics, or remain explicitly current/revision-sensitive"
  "all historically indexed Ibrahim graph claims; prevents current-Wikipedia edges from silently becoming 2014 facts"
  false false false false

------------------------------------------------------------------------
-- Rank 3: correction/revision lineage as a first-class provenance relation.
--
-- We already distinguish addenda/retractions/corrections conceptually.  The
-- remaining leverage is a generic append-only relation across science, media,
-- legal authority and memory/source archaeology.
------------------------------------------------------------------------

revisionLineageFrontier : ParetoFrontierLeaf
revisionLineageFrontier = pareto-frontier-leaf
  3 liveResidual
  "Original source <-> correction/addendum/retraction <-> current interpretation"
  "IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact; IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact; append-only evidence/revision architecture elsewhere in DASHI"
  "one thin cross-domain relation retaining what changed, what stayed, source identity, date and consumer impact without rewriting historical state"
  "later correction is attached append-only and cannot silently mutate the earlier source object; consumers can select current status while retaining provenance"
  "scientific addenda; retractions; legal authority changes; media corrections; OSINT updates; historical reconstruction"
  false false false false

------------------------------------------------------------------------
-- Rank 4: residual QID / Dewey / DOI enrichment.
--
-- Important for navigation and attribution, but deliberately lower than the
-- structural residuals above because unresolved external metadata normally does
-- not block domain proofs.
------------------------------------------------------------------------

externalMetadataFrontier : ParetoFrontierLeaf
externalMetadataFrontier = pareto-frontier-leaf
  4 opportunisticMetadataResidual
  "QID / Dewey / DOI / canonical-source residual cleanup"
  "SnowballExternalIdentityAvailabilityExact; SymbolicVerificationDeweyQidDoiBidiExact; AttributedSourceCore"
  "resolve exact identities only when safe: e.g. common-source dependence, correction/debunking concepts, unresolved Dewey coordinates, exact source identifiers"
  "resolved metadata is retained with source role; unresolved stays explicit; nearest-label substitution is rejected"
  "search/navigation, citation linking, library classification, source archaeology"
  false false false false

------------------------------------------------------------------------
-- Previously high roadmap leaves now substantially paid.
------------------------------------------------------------------------

archiveEvidencePaid : ParetoFrontierLeaf
archiveEvidencePaid = pareto-frontier-leaf
  5 substantiallyPaid
  "Archives / bibliography / source criticism / testimony / causality"
  "IbrahimSnowballArchiveHistoriographyCausalityBidiExact; IbrahimSnowballSensibLawEvidenceObservationTestimonyCausationBidiExact; IbrahimSnowballTestimonyMemoryCredibilityCorroborationExpertBidiExact"
  "no broad ontology gap; only downstream consumer-specific source genealogy or authority questions"
  "new work reuses the existing acquisition/evidence ladders instead of creating another archive/evidence theory"
  "history, law, anthropology, science"
  false false false false

learningMemoryPaid : ParetoFrontierLeaf
learningMemoryPaid = pareto-frontier-leaf
  6 substantiallyPaid
  "Learning / memory / trauma / testimony / replication"
  "DepthWheelMemoryHyperfabric; TraumaMemoryHypervoxelBridge; EarlyLearningChoicePNFHyperfabricBridge; IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact"
  "no generic memory model gap; remaining work is source-/consumer-specific"
  "same public memory can retain different latent state; extinction != erasure; residual != diagnosis; repetition != independence"
  "psychology, education, testimony, trauma-memory, science replication"
  false false false false

skepticismMediaPaid : ParetoFrontierLeaf
skepticismMediaPaid = pareto-frontier-leaf
  7 substantiallyPaid
  "Skepticism / expertise / distrust / alternative media / misinformation"
  "IbrahimSnowballSkepticismExpertiseTrustPropagandaBidiExact; IbrahimSnowballConspiracyDistrustAlternativeMediaBidiExact; IbrahimSnowballFactCheckingVerificationMediaLiteracyCorrectionBidiExact"
  "no generic trust/misinformation ontology gap; remaining questions need proposition/source-specific payment"
  "skepticism != anti-expertise; expertise != truth; distrust != conspiracism; carrier != information status; correction != universal persuasion"
  "climate, media, IDW/manosphere, science, pedagogy"
  false false false false

symbolicPaid : ParetoFrontierLeaf
symbolicPaid = pareto-frontier-leaf
  8 substantiallyPaid
  "Qi / Yijing / witchcraft / divination / symbolic interpretation"
  "IbrahimSnowballQiHexagramWitchDivinationBidiExact; SymbolicVerificationDeweyQidDoiBidiExact; ArchiveHistoriographyCausalityBidiExact"
  "no broad symbolic ontology gap; remaining claims require historical/practitioner/source-specific payment"
  "cultural/symbolic meaning stays distinct from empirical prediction and empirical audit does not erase cultural meaning"
  "religion, anthropology, history, source criticism, verification"
  false false false false

------------------------------------------------------------------------
-- Attribution / external identity policies remain inherited, not redefined.
------------------------------------------------------------------------

attributionBoundary : Attribution.AttributionSnowballBoundary
attributionBoundary = Attribution.canonicalAttributionSnowballBoundary

externalIdentityPolicy : Identity.SnowballExternalIdentityPolicy
externalIdentityPolicy = Identity.canonicalExternalIdentityPolicy

roadmapPolicy : Roadmap.RoadmapPolicy
roadmapPolicy = Roadmap.canonicalRoadmapPolicy

archiveBoundary : Archive.ArchiveHistoriographyCausalityBoundary
archiveBoundary = Archive.canonicalArchiveHistoriographyCausalityBoundary

evidenceBoundary : Evidence.SensibLawEvidenceObservationTestimonyCausationBoundary
evidenceBoundary = Evidence.canonicalSensibLawEvidenceObservationTestimonyCausationBoundary

testimonyBoundary : Testimony.TestimonyMemoryCredibilityBoundary
testimonyBoundary = Testimony.canonicalTestimonyMemoryCredibilityBoundary

learningBoundary : Learning.LearningMemoryTraumaReplicationConsensusBoundary
learningBoundary = Learning.canonicalLearningMemoryTraumaReplicationConsensusBoundary

verificationBoundary : Verification.FactCheckingVerificationMediaLiteracyCorrectionBoundary
verificationBoundary = Verification.canonicalFactCheckingVerificationMediaLiteracyCorrectionBoundary

------------------------------------------------------------------------
-- Pareto policy: structural residuals dominate metadata cleanup.
------------------------------------------------------------------------

record ParetoPolicy : Set where
  constructor pareto-policy
  field
    quotientExistingOwnersFirst : Bool
    preferCrossDomainResiduals : Bool
    preferThinCompositionOverNewOntology : Bool
    provenanceBeforeMultiplicityPromotion : Bool
    attributionTravelsWithEveryPromotedEdge : Bool
    qidDeweyDoiAreNavigationNotTruth : Bool
    unresolvedMetadataBlocksUnrelatedProof : Bool
    oldRoadmapRanksRemainAuthoritativeAfterPayment : Bool
open ParetoPolicy public

canonicalParetoPolicy : ParetoPolicy
canonicalParetoPolicy = pareto-policy
  true true true true true true false false

------------------------------------------------------------------------
-- Compact answer to "what remains?"
------------------------------------------------------------------------

record RemainingFrontier : Set where
  constructor remaining-frontier
  field
    first : ParetoFrontierLeaf
    second : ParetoFrontierLeaf
    third : ParetoFrontierLeaf
    fourth : ParetoFrontierLeaf
    breadthExpansionIsCurrentPriority : Bool
open RemainingFrontier public

canonicalRemainingFrontier : RemainingFrontier
canonicalRemainingFrontier = remaining-frontier
  provenanceIndependenceFrontier
  historicalRuntimeFrontier
  revisionLineageFrontier
  externalMetadataFrontier
  false

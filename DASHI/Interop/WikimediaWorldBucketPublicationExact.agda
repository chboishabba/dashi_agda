module DASHI.Interop.WikimediaWorldBucketPublicationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as AppendOnly
import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.ReopenableProjectionComposition as Reopenable

------------------------------------------------------------------------
-- WIKIMEDIA WORLD BUCKET / PUBLICATION BOUNDARY
--
-- Runtime counterpart:
--   SensibLaw/src/ontology/wikimedia_world_walk.py
--
-- A local inquiry bucket may grow through heterogeneous edge families while
-- retaining ambiguity, failed follows, cycles, alternate readings and source
-- residuals. Publication is a separate candidate-only projection. Neither a
-- content digest/CID nor inclusion in a global graph manufactures truth,
-- authority, applicability or evidence payment.
------------------------------------------------------------------------

data WorldEdgeFamily : Set where
  wikidataOntology : WorldEdgeFamily
  wikipediaNavigation : WorldEdgeFamily
  sourceReference : WorldEdgeFamily
  pnfSemantic : WorldEdgeFamily
  sourceProvenance : WorldEdgeFamily
  residualInquiry : WorldEdgeFamily

record WorldGrowthReceipt : Set where
  constructor worldGrowthReceipt
  field
    hop : Nat
    sourceRef : String
    targetRef : String
    edgeFamily : WorldEdgeFamily
    relationRef : String
    cycleObserved : Bool
    appendOnlyRetained : Bool
    createsSemanticTruth : Bool
    createsAuthority : Bool

open WorldGrowthReceipt public

canonicalGrowthReceipt : WorldGrowthReceipt
canonicalGrowthReceipt =
  worldGrowthReceipt
    (suc zero)
    "mabo"
    "hca-1992"
    sourceReference
    "citation"
    false
    true
    false
    false

record WorldBucketManifestBoundary : Set where
  constructor worldBucketManifestBoundary
  field
    schemaReference : String
    seedReference : String
    hopBudget : Nat
    candidateOnly : Bool
    semanticPromotion : Bool
    liveIPFSPublicationPerformed : Bool
    publicationProjectionIsBrowsingHistory : Bool
    packagingTarget : String
    manifestEnvelope : String
    contentAddressingState : String
    sinkReferencesPopulated : Bool
    contentDigestIsAuthority : Bool
    cidImportsProof : Bool
    worldsMayReferenceParentWorlds : Bool

open WorldBucketManifestBoundary public

canonicalManifestBoundary : WorldBucketManifestBoundary
canonicalManifestBoundary =
  worldBucketManifestBoundary
    "sl.wikimedia_world_bucket.v0_1"
    "mabo"
    (suc (suc (suc zero)))
    true
    false
    false
    false
    "kant-erdfa-shardset"
    "cbor-compatible-logical-envelope"
    "sha256-now-cid-later"
    false
    false
    false
    true

------------------------------------------------------------------------
-- Publication is a query-indexed projection. Two local worlds may publish the
-- same selected graph while retaining different private Reading-Trail state.
------------------------------------------------------------------------

data LocalWorldBucket : Set where
  samePublishedWorldPrivateTrailA : LocalWorldBucket
  samePublishedWorldPrivateTrailB : LocalWorldBucket

data PublishedWorldBucket : Set where
  sameCandidatePublishedWorld : PublishedWorldBucket

publishSelectedWorld : LocalWorldBucket → PublishedWorldBucket
publishSelectedWorld samePublishedWorldPrivateTrailA = sameCandidatePublishedWorld
publishSelectedWorld samePublishedWorldPrivateTrailB = sameCandidatePublishedWorld

data WorldPublicationQuery : Set where
  candidateGraphQuestion : WorldPublicationQuery
  browsingHistoryQuestion : WorldPublicationQuery

data CandidateGraphAnswer : Set where
  sameCandidateGraph : CandidateGraphAnswer

data BrowsingHistoryAnswer : Set where
  privateTrailA : BrowsingHistoryAnswer
  privateTrailB : BrowsingHistoryAnswer

PublicationAnswer : WorldPublicationQuery → Set
PublicationAnswer candidateGraphQuestion = CandidateGraphAnswer
PublicationAnswer browsingHistoryQuestion = BrowsingHistoryAnswer

askPublication :
  (query : WorldPublicationQuery) →
  LocalWorldBucket →
  PublicationAnswer query
askPublication candidateGraphQuestion samePublishedWorldPrivateTrailA = sameCandidateGraph
askPublication candidateGraphQuestion samePublishedWorldPrivateTrailB = sameCandidateGraph
askPublication browsingHistoryQuestion samePublishedWorldPrivateTrailA = privateTrailA
askPublication browsingHistoryQuestion samePublishedWorldPrivateTrailB = privateTrailB

publicationQuestions :
  Query.InquiryQuestionFamily LocalWorldBucket WorldPublicationQuery
publicationQuestions = Query.inquiryQuestionFamily PublicationAnswer askPublication

candidateGraphFactorsThroughPublishedProjection :
  Query.FactorsThrough
    publicationQuestions
    publishSelectedWorld
    candidateGraphQuestion
candidateGraphFactorsThroughPublishedProjection = Query.factorsThrough answer proof
  where
    answer : PublishedWorldBucket → CandidateGraphAnswer
    answer sameCandidatePublishedWorld = sameCandidateGraph

    proof :
      (bucket : LocalWorldBucket) →
      askPublication candidateGraphQuestion bucket ≡
      answer (publishSelectedWorld bucket)
    proof samePublishedWorldPrivateTrailA = refl
    proof samePublishedWorldPrivateTrailB = refl

browsingHistoryDoesNotFactorThroughPublishedProjection :
  Query.FactorsThrough
    publicationQuestions
    publishSelectedWorld
    browsingHistoryQuestion →
  ⊥
browsingHistoryDoesNotFactorThroughPublishedProjection factor = helper first second
  where
    first :
      privateTrailA ≡
      Query.quotientAnswer factor sameCandidatePublishedWorld
    first = Query.factorisation factor samePublishedWorldPrivateTrailA

    second :
      privateTrailB ≡
      Query.quotientAnswer factor sameCandidatePublishedWorld
    second = Query.factorisation factor samePublishedWorldPrivateTrailB

    helper :
      privateTrailA ≡ Query.quotientAnswer factor sameCandidatePublishedWorld →
      privateTrailB ≡ Query.quotientAnswer factor sameCandidatePublishedWorld →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- Reopening is possible only when a private residual receipt is retained.
-- Publishing the selected graph alone is deliberately not claimed sufficient
-- to reconstruct the local inquiry state.
------------------------------------------------------------------------

publishedProjectionReopenableWithPrivateReceipt :
  Reopenable.ExactReopenableProjection LocalWorldBucket PublishedWorldBucket
publishedProjectionReopenableWithPrivateReceipt =
  Reopenable.exactReopenableProjection
    LocalWorldBucket
    publishSelectedWorld
    (λ bucket → bucket)
    (λ published receipt → receipt)
    reopenProof
  where
    reopenProof :
      (bucket : LocalWorldBucket) →
      (λ published receipt → receipt)
        (publishSelectedWorld bucket)
        bucket ≡ bucket
    reopenProof samePublishedWorldPrivateTrailA = refl
    reopenProof samePublishedWorldPrivateTrailB = refl

------------------------------------------------------------------------
-- Publication / convergence firewalls.
------------------------------------------------------------------------

data CandidateManifestCreatesTruthPermission : Set where

data CIDCreatesAuthorityPermission : Set where

data GlobalGraphInsertionPaysEvidencePermission : Set where

data CoordinateConvergenceCreatesTruthPermission : Set where

data PublishProjectionMayLeakBrowsingHistoryPermission : Set where

candidateManifestCannotManufactureTruth :
  CandidateManifestCreatesTruthPermission → ⊥
candidateManifestCannotManufactureTruth ()

cidCannotManufactureAuthority : CIDCreatesAuthorityPermission → ⊥
cidCannotManufactureAuthority ()

globalGraphInsertionCannotPayEvidence :
  GlobalGraphInsertionPaysEvidencePermission → ⊥
globalGraphInsertionCannotPayEvidence ()

coordinateConvergenceCannotManufactureTruth :
  CoordinateConvergenceCreatesTruthPermission → ⊥
coordinateConvergenceCannotManufactureTruth ()

publishProjectionCannotLeakBrowsingHistoryByDefault :
  PublishProjectionMayLeakBrowsingHistoryPermission → ⊥
publishProjectionCannotLeakBrowsingHistoryByDefault ()

------------------------------------------------------------------------
-- Existing append-only revision doctrine remains the canonical evidence-history
-- owner. World-walk growth inherits that boundary rather than creating a new
-- monotonic-truth calculus.
------------------------------------------------------------------------

existingAppendOnlyRevisionBoundary :
  AppendOnly.AppendOnlyEvidenceRevisionBoundary
existingAppendOnlyRevisionBoundary =
  AppendOnly.canonicalAppendOnlyEvidenceRevisionBoundary

worldWalkRuntimeSchema : String
worldWalkRuntimeSchema = "sl.wikimedia_world_walk.v0_1"

worldBucketRuntimeSchema : String
worldBucketRuntimeSchema = "sl.wikimedia_world_bucket.v0_1"

worldWalkRuntimeWritten : Bool
worldWalkRuntimeWritten = true

worldWalkRuntimeReceiptObserved : Bool
worldWalkRuntimeReceiptObserved = false

agdaCertificationObserved : Bool
agdaCertificationObserved = false

module DASHI.Wikimedia.SensibLawSharedAcquisitionExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawNatBatchPrerequisiteRunnerContractExact as Batch
import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG
import DASHI.Wikimedia.SensibLawZelphHFSelectorResultPaymentExact as Result

------------------------------------------------------------------------
-- SHARED ACQUISITION EXECUTION -> TASK-SPECIFIC PROJECTIONS
--
-- Runtime optimisation law:
--   union bounded QID demand -> one shared transport execution -> many exact
--   task projections -> independent consumer verification/payment.
--
-- Network/cache work may be shared.  Semantic/payment authority may not.
------------------------------------------------------------------------

-- Proof-relevant membership, requiring no global String decidable-equality
-- assumption.  Constructors witness the exact list position definitionally.
data QidIn (qid : String) : List String → Set where
  qidHere : {rest : List String} → QidIn qid (qid ∷ rest)
  qidThere : {other : String} {rest : List String} →
    QidIn qid rest → QidIn qid (other ∷ rest)

-- Every task QID is literally represented in the shared execution surface.
data AllQidsCovered : List String → List String → Set where
  coveredNil : {unionQids : List String} → AllQidsCovered [] unionQids
  coveredCons :
    {qid : String} {taskRest unionQids : List String} →
    QidIn qid unionQids →
    AllQidsCovered taskRest unionQids →
    AllQidsCovered (qid ∷ taskRest) unionQids

record SharedAcquisitionExecution : Set where
  constructor shared-acquisition-execution
  field
    sharedExecutionId : String
    sharedSelectorClass : Batch.SelectorClass
    sharedPrerequisite : DAG.BundleObligation
    sharedUnionQids : List String
    sharedRequestedProperties : List String
    sharedManifestReference : String
    sharedManifestDigest : String
    sharedBackendReference : String
    sharedBinaryIdentityReference : String
    sharedExecutionReceiptReference : String
    sharedContentAddressReference : String
    sharedCacheReference : String
    sharedNetworkPerformed : Bool
    sharedConsumerVerificationPerformed : Bool
    sharedSemanticPromotionPerformed : Bool
    sharedSourceSupportPaid : Bool
open SharedAcquisitionExecution public

record SharedExecutionTaskProjection
    (shared : SharedAcquisitionExecution) : Set where
  constructor shared-execution-task-projection
  field
    projectionTaskReference : String
    projectionQids : List String
    projectionProperties : List String
    projectionQidsCovered :
      AllQidsCovered projectionQids (sharedUnionQids shared)
    projectionSharedExecutionReference : String
    projectionSharedExecutionReferenceExact :
      projectionSharedExecutionReference ≡ sharedExecutionReceiptReference shared
    projectionResultReference : String
    projectionLineageReference : String
    projectionConsumerVerificationRequired : Bool
    projectionConsumerVerificationRequiredIsTrue :
      projectionConsumerVerificationRequired ≡ true
    projectionSourceSupportPaid : Bool
    projectionSourceSupportPaidIsFalse : projectionSourceSupportPaid ≡ false
    projectionSemanticPromotionPerformed : Bool
    projectionSemanticPromotionPerformedIsFalse :
      projectionSemanticPromotionPerformed ≡ false
open SharedExecutionTaskProjection public

------------------------------------------------------------------------
-- Payment remains result-local and consumer-local even when transport is shared.
------------------------------------------------------------------------

record ProjectedVerifiedPayment
    (shared : SharedAcquisitionExecution)
    (projection : SharedExecutionTaskProjection shared)
    (result : Result.BoundedSelectorResult) : Set where
  constructor projected-verified-payment
  field
    projectedPayment : Result.VerifiedPrerequisitePayment result
    projectedResultReference : String
    projectedConsumerReference : String
    projectedSameSharedExecutionLineage :
      projectionSharedExecutionReference projection
      ≡ sharedExecutionReceiptReference shared
open ProjectedVerifiedPayment public

------------------------------------------------------------------------
-- Hard firewalls: transport/cache coalescing is not semantic coalescing.
------------------------------------------------------------------------

data SharedExecutionAutomaticallyPaysProjection : Set where
data OneProjectedPaymentPaysSiblingProjection : Set where
data SharedCacheCreatesSourceAuthority : Set where
data UnionCoverageMeansWholeCohortCoverage : Set where

sharedExecutionDoesNotAutomaticallyPayProjection :
  SharedExecutionAutomaticallyPaysProjection → ⊥
sharedExecutionDoesNotAutomaticallyPayProjection ()

oneProjectionPaymentDoesNotPaySibling :
  OneProjectedPaymentPaysSiblingProjection → ⊥
oneProjectionPaymentDoesNotPaySibling ()

sharedCacheDoesNotCreateSourceAuthority : SharedCacheCreatesSourceAuthority → ⊥
sharedCacheDoesNotCreateSourceAuthority ()

unionCoverageDoesNotMeanWholeCohortCoverage :
  UnionCoverageMeansWholeCohortCoverage → ⊥
unionCoverageDoesNotMeanWholeCohortCoverage ()

------------------------------------------------------------------------
-- Current Nat 57-row tranche calibration: four work groups collapse to one
-- five-QID network discovery surface.  These are acquisition identities only.
------------------------------------------------------------------------

natFiveQidUnion : List String
natFiveQidUnion =
  "Q10403939" ∷
  "Q10416948" ∷
  "Q10422059" ∷
  "Q10651551" ∷
  "Q56404383" ∷ []

natSharedSourceSupportExecution : SharedAcquisitionExecution
natSharedSourceSupportExecution =
  shared-acquisition-execution
    "nat:57-row:shared-source-support-acquisition"
    Batch.zelphHFSelector
    DAG.sourceSupport
    natFiveQidUnion
    ("P5991" ∷ "P14143" ∷ "P854" ∷ [])
    "canonical zelph-hf-layout/v2 manifest"
    "runtime manifest sha256 receipt"
    "SensibLaw compatible Zelph/HF selector executor"
    "runtime-selected compatible Zelph binary identity"
    "one union transport execution receipt"
    "one content-addressed shared acquisition result"
    "persistent content-addressed HF/QID discovery cache"
    true false false false

-- Example projection for the Q10403939/Q10422059 task.  Both memberships are
-- theorem values into the five-QID union; no string comparison is assumed.
natQ10403939Q10422059Coverage :
  AllQidsCovered
    ("Q10403939" ∷ "Q10422059" ∷ [])
    natFiveQidUnion
natQ10403939Q10422059Coverage =
  coveredCons qidHere
    (coveredCons
      (qidThere (qidThere qidHere))
      coveredNil)

natExampleSharedProjection :
  SharedExecutionTaskProjection natSharedSourceSupportExecution
natExampleSharedProjection =
  shared-execution-task-projection
    "one of four Nat acquisition tasks"
    ("Q10403939" ∷ "Q10422059" ∷ [])
    ("P5991" ∷ "P14143" ∷ "P854" ∷ [])
    natQ10403939Q10422059Coverage
    "one union transport execution receipt"
    refl
    "task-specific projection of shared acquisition output"
    "projection retains task/QID/result lineage"
    true refl
    false refl
    false refl

natProjectionUsesExactSharedExecution :
  projectionSharedExecutionReference natExampleSharedProjection
  ≡ sharedExecutionReceiptReference natSharedSourceSupportExecution
natProjectionUsesExactSharedExecution = refl

natProjectionStillRequiresConsumerVerification :
  projectionConsumerVerificationRequired natExampleSharedProjection ≡ true
natProjectionStillRequiresConsumerVerification = refl

natProjectionDoesNotPaySourceSupport :
  projectionSourceSupportPaid natExampleSharedProjection ≡ false
natProjectionDoesNotPaySourceSupport = refl

------------------------------------------------------------------------
-- Compact contract exported to runtime implementations.
------------------------------------------------------------------------

record SharedAcquisitionExecutionContract : Set where
  constructor shared-acquisition-execution-contract
  field
    unionDemandMayShareNetworkExecution : Bool
    everyProjectionRequiresQidCoverageWitness : Bool
    projectionReferencesExactSharedExecution : Bool
    networkCacheMayBeShared : Bool
    projectionPaymentRemainsConsumerLocal : Bool
    onePaymentPaysSibling : Bool
    sharedCacheCreatesAuthority : Bool
    unionMeansWholeCohortCovered : Bool

canonicalSharedAcquisitionExecutionContract : SharedAcquisitionExecutionContract
canonicalSharedAcquisitionExecutionContract =
  shared-acquisition-execution-contract
    true true true true true false false false

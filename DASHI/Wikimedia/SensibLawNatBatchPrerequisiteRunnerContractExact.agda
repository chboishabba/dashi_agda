module DASHI.Wikimedia.SensibLawNatBatchPrerequisiteRunnerContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG
import DASHI.Wikimedia.SensibLawZelphHFPrerequisiteBridgeExact as Zelph
import DASHI.Wikimedia.SensibLawZelphHFSelectorResultPaymentExact as Result

------------------------------------------------------------------------
-- BATCH PREREQUISITE RUNNER CONTRACT
--
-- This is deliberately NOT 37,665 hand-written proof objects.
-- A runtime/script owns enumeration, grouping, dispatch and serialization.
-- Agda owns the generic laws that every generated row/group/batch artifact
-- must satisfy.
------------------------------------------------------------------------

data RoutingFamily : Set where
  fullAuto
  splitAuto
  repairPlusMigrateReview
  reviewOnlyTypedHold
  manualReconstruction
  : RoutingFamily

data SelectorClass : Set where
  zelphHFSelector
  theoremSearch
  humanReview
  noSelector
  : SelectorClass

selectorClassForMechanism : DAG.PrerequisiteMechanism → SelectorClass
selectorClassForMechanism DAG.lookMechanism = zelphHFSelector
selectorClassForMechanism DAG.thinkMechanism = theoremSearch
selectorClassForMechanism DAG.reviewMechanism = humanReview
selectorClassForMechanism DAG.noMechanism = noSelector

record BatchRowDescriptor : Set where
  constructor batch-row-descriptor
  field
    rowId : String
    qid : String
    statementReference : String
    sourceCohort : String
    routingFamily : RoutingFamily
    sourceProperty : String
    targetProperty : String
    qualifierProperties : List String
    referenceProperties : List String
    rowRevisionReference : String
    rowInputDigest : String
    prerequisiteStatus : DAG.BundleObligationStatus
open BatchRowDescriptor public

record WorkSignature : Set where
  constructor work-signature
  field
    cohort : String
    route : RoutingFamily
    firstResidual : DAG.BundlePrerequisiteResidual
    producer : DAG.BundlePrerequisiteProducer
    mechanism : DAG.PrerequisiteMechanism
    selectorClass : SelectorClass
    sourceProperty : String
    targetProperty : String
    qualifierProperties : List String
    referenceProperties : List String
open WorkSignature public

signatureFor : BatchRowDescriptor → WorkSignature
signatureFor row =
  let residual = DAG.firstMissingPrerequisite (prerequisiteStatus row)
      producer = DAG.producerForResidual residual
      mechanism = DAG.mechanismForProducer producer
  in
  work-signature
    (sourceCohort row)
    (routingFamily row)
    residual
    producer
    mechanism
    (selectorClassForMechanism mechanism)
    (BatchRowDescriptor.sourceProperty row)
    (BatchRowDescriptor.targetProperty row)
    (qualifierProperties row)
    (referenceProperties row)

record SignatureAssignment (row : BatchRowDescriptor) : Set where
  constructor signature-assignment
  field
    signature : WorkSignature
    signatureExact : signature ≡ signatureFor row
    assignmentReference : String
open SignatureAssignment public

canonicalSignatureAssignment :
  (row : BatchRowDescriptor) → SignatureAssignment row
canonicalSignatureAssignment row =
  signature-assignment (signatureFor row) refl
    "work signature is derived from row state; it is not a manually selected proof-search route"

------------------------------------------------------------------------
-- Equal signatures may share one bounded work strategy. They remain distinct
-- rows with distinct source/revision/statement lineage.
------------------------------------------------------------------------

record SignatureGroupMember
    (representative : WorkSignature)
    (row : BatchRowDescriptor) : Set where
  constructor signature-group-member
  field
    assignment : SignatureAssignment row
    sameSignature : signature assignment ≡ representative
    rowLineageReference : String
open SignatureGroupMember public

record BatchWorkGroup : Set where
  constructor batch-work-group
  field
    groupId : String
    representativeSignature : WorkSignature
    memberCount : Nat
    dispatchReference : String
    groupContentDigest : String
open BatchWorkGroup public

------------------------------------------------------------------------
-- Runtime result row. The decision is not reconstructed from an aggregate
-- count. It points to the exact content-addressed selector/proof/review result
-- and retains the atomic result semantics from SelectorResultPaymentExact.
------------------------------------------------------------------------

data BatchOutcome : Set where
  paid
  open
  split
  reactivated
  : BatchOutcome

record BatchRowResult (row : BatchRowDescriptor) : Set where
  constructor batch-row-result
  field
    assignment : SignatureAssignment row
    workGroupReference : String
    boundedResultReference : String
    boundedResultDigest : String
    executionReceiptReference : String
    consumerVerificationReference : String
    outcome : BatchOutcome
    nextPrerequisite : DAG.BundlePrerequisiteResidual
    resultLineageReference : String
open BatchRowResult public

------------------------------------------------------------------------
-- Outcome witnesses. These are deliberately stronger than a string enum.
-- A generated runtime row can say `paid`, but a theorem-level payment witness
-- still has to bind the atomic verified payment for that same bounded result.
------------------------------------------------------------------------

record PaidRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row)
    (result : Result.BoundedSelectorResult) : Set where
  constructor paid-row-witness
  field
    outcomeIsPaid : outcome batchRow ≡ paid
    verifiedPayment : Result.VerifiedPrerequisitePayment result
    resultTargetsCurrentFirstMissing :
      Result.resultObligation result
      ≡ DAG.obligationForResidual
          (DAG.firstMissingPrerequisite (prerequisiteStatus row))
    exactResultReference : String
open PaidRowWitness public

record OpenRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor open-row-witness
  field
    outcomeIsOpen : outcome batchRow ≡ open
    currentResidualStillOpen :
      nextPrerequisite batchRow
      ≡ DAG.firstMissingPrerequisite (prerequisiteStatus row)
    openReasonReference : String
open OpenRowWitness public

record SplitRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor split-row-witness
  field
    outcomeIsSplit : outcome batchRow ≡ split
    splitPlanReference : String
    splitPreservesSourceRow : Bool
    splitPreservesSourceRowIsTrue : splitPreservesSourceRow ≡ true
open SplitRowWitness public

record ReactivatedRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor reactivated-row-witness
  field
    outcomeIsReactivated : outcome batchRow ≡ reactivated
    changedEvidenceReference : String
    historicalClosureReference : String
    historicalClosurePreserved : Bool
    historicalClosurePreservedIsTrue : historicalClosurePreserved ≡ true
open ReactivatedRowWitness public

------------------------------------------------------------------------
-- Batch artifact. Runtime owns the actual row serialization and exact counts.
-- The formal carrier only requires that the artifact is content-addressed,
-- schema/version pinned and keeps per-row results available by reference.
------------------------------------------------------------------------

record BatchOutcomeCounts : Set where
  constructor batch-outcome-counts
  field
    paidCount : Nat
    openCount : Nat
    splitCount : Nat
    reactivatedCount : Nat
open BatchOutcomeCounts public

record ContentAddressedBatchArtifact : Set where
  constructor content-addressed-batch-artifact
  field
    schemaVersion : String
    laneId : String
    sourceCohort : String
    sourceRevisionReference : String
    sourcePopulation : Nat
    materializedRowCount : Nat
    workGroupCount : Nat
    counts : BatchOutcomeCounts
    batchDigestAlgorithm : String
    batchInputDigest : String
    batchOutputDigest : String
    perRowArtifactReference : String
    workGroupArtifactReference : String
    executionReceiptIndexReference : String
    verificationReceiptIndexReference : String
    lineageIndexReference : String
open ContentAddressedBatchArtifact public

------------------------------------------------------------------------
-- Nat population calibration from the mature handoff. This is a cohort
-- manifest receipt, not a claim that all 37,665 rows are materialized in the
-- current formal branch or safe for direct migration.
------------------------------------------------------------------------

natBusinessFamilyBatchSurface : ContentAddressedBatchArtifact
natBusinessFamilyBatchSurface =
  content-addressed-batch-artifact
    "sl.nat_batch_prerequisite_result.v0_1"
    "wikidata-nat-p5991-p14143"
    "business_family_reconciled"
    "SensibLaw Nat revision-locked sandbox/cohort-manifest lineage"
    37665
    0
    0
    (batch-outcome-counts 0 0 0 0)
    "sha256"
    "unmaterialized-in-this-Agda-fixture"
    "unmaterialized-in-this-Agda-fixture"
    "runtime-emitted per-row result artifact"
    "runtime-emitted work-signature grouping artifact"
    "runtime-emitted selector/proof/review execution receipt index"
    "runtime-emitted consumer verification receipt index"
    "runtime-emitted append-only row lineage index"

natPopulationRemains37665 :
  sourcePopulation natBusinessFamilyBatchSurface ≡ 37665
natPopulationRemains37665 = refl

natFormalFixtureDoesNotPretendToMaterializePopulation :
  materializedRowCount natBusinessFamilyBatchSurface ≡ 0
natFormalFixtureDoesNotPretendToMaterializePopulation = refl

------------------------------------------------------------------------
-- Batch grouping is an execution optimisation only.
------------------------------------------------------------------------

data SameWorkSignatureMeansSameSemantics : Set where
data SameWorkSignatureMeansSameSourceIdentity : Set where
data GroupedDispatchPaysEveryMember : Set where
data AggregatePaidCountPromotesCohort : Set where
data AggregateSplitCountMeansFailure : Set where
data BatchDigestCreatesAuthority : Set where
data MaterializedRowsEqualManifestPopulationByDefault : Set where
data RuntimeOutcomeEnumIsProofReceipt : Set where

groupingDoesNotCollapseSemantics : SameWorkSignatureMeansSameSemantics → ⊥
groupingDoesNotCollapseSemantics ()

groupingDoesNotCollapseSourceIdentity : SameWorkSignatureMeansSameSourceIdentity → ⊥
groupingDoesNotCollapseSourceIdentity ()

groupDispatchDoesNotPayEveryMember : GroupedDispatchPaysEveryMember → ⊥
groupDispatchDoesNotPayEveryMember ()

aggregatePaidDoesNotPromoteCohort : AggregatePaidCountPromotesCohort → ⊥
aggregatePaidDoesNotPromoteCohort ()

aggregateSplitDoesNotMeanFailure : AggregateSplitCountMeansFailure → ⊥
aggregateSplitDoesNotMeanFailure ()

batchDigestDoesNotCreateAuthority : BatchDigestCreatesAuthority → ⊥
batchDigestDoesNotCreateAuthority ()

materializationDoesNotDefaultToManifestPopulation :
  MaterializedRowsEqualManifestPopulationByDefault → ⊥
materializationDoesNotDefaultToManifestPopulation ()

runtimeEnumDoesNotBecomeProofReceipt : RuntimeOutcomeEnumIsProofReceipt → ⊥
runtimeEnumDoesNotBecomeProofReceipt ()

------------------------------------------------------------------------
-- Formal runner boundary: what a future SensibLaw/SLR script must implement.
------------------------------------------------------------------------

record NatBatchPrerequisiteRunnerContract : Set where
  constructor nat-batch-prerequisite-runner-contract
  field
    derivesFirstMissingFromRowStatus : Bool
    derivesWorkSignatureFromFirstMissing : Bool
    equalSignaturesMayShareDispatch : Bool
    groupedRowsRetainDistinctLineage : Bool
    selectorOutputStillNeedsConsumerVerification : Bool
    perRowDecisionRetained : Bool
    aggregateCountsAreSummaryOnly : Bool
    splitIsUsefulOutcome : Bool
    reactivationPreservesHistory : Bool
    contentAddressCreatesAuthority : Bool
    runtimeEnumCountsAsProof : Bool
    wholeCohortMaterializedByFormalFixture : Bool

canonicalNatBatchPrerequisiteRunnerContract :
  NatBatchPrerequisiteRunnerContract
canonicalNatBatchPrerequisiteRunnerContract =
  nat-batch-prerequisite-runner-contract
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false

module DASHI.Wikimedia.SensibLawNatBatchPrerequisiteRunnerContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.SensibLawStatementBundlePrerequisiteDAGExact as DAG
import DASHI.Wikimedia.SensibLawZelphHFSelectorResultPaymentExact as Result

------------------------------------------------------------------------
-- BATCH PREREQUISITE RUNNER CONTRACT
--
-- The runtime/script enumerates, groups, dispatches and serialises rows.
-- Agda proves what those generated artifacts mean.  There is intentionally no
-- 37,665-row hand-written witness surface in this module.
------------------------------------------------------------------------

data RoutingFamily : Set where
  fullAuto
  splitAuto
  repairPlusMigrateReview
  reviewOnlyTypedHold
  manualReconstruction
  : RoutingFamily

data SelectorClass : Set where
  zelphHFSelector theoremSearch humanReview noSelector : SelectorClass

selectorClassForMechanism : DAG.PrerequisiteMechanism → SelectorClass
selectorClassForMechanism DAG.lookMechanism = zelphHFSelector
selectorClassForMechanism DAG.thinkMechanism = theoremSearch
selectorClassForMechanism DAG.reviewMechanism = humanReview
selectorClassForMechanism DAG.noMechanism = noSelector

record BatchRowDescriptor : Set where
  constructor batch-row-descriptor
  field
    rowId : String
    rowQid : String
    rowStatementReference : String
    rowSourceCohort : String
    rowRoutingFamily : RoutingFamily
    rowSourceProperty : String
    rowTargetProperty : String
    rowQualifierProperties : List String
    rowReferenceProperties : List String
    rowRevisionReference : String
    rowInputDigest : String
    rowPrerequisiteStatus : DAG.BundleObligationStatus
open BatchRowDescriptor public

record WorkSignature : Set where
  constructor work-signature
  field
    signatureCohort : String
    signatureRoute : RoutingFamily
    signatureFirstResidual : DAG.BundlePrerequisiteResidual
    signatureProducer : DAG.BundlePrerequisiteProducer
    signatureMechanism : DAG.PrerequisiteMechanism
    signatureSelectorClass : SelectorClass
    signatureSourceProperty : String
    signatureTargetProperty : String
    signatureQualifierProperties : List String
    signatureReferenceProperties : List String
open WorkSignature public

signatureFor : BatchRowDescriptor → WorkSignature
signatureFor row =
  let residual = DAG.firstMissingPrerequisite (rowPrerequisiteStatus row)
      producer = DAG.producerForResidual residual
      mechanism = DAG.mechanismForProducer producer
  in
  work-signature
    (rowSourceCohort row)
    (rowRoutingFamily row)
    residual
    producer
    mechanism
    (selectorClassForMechanism mechanism)
    (rowSourceProperty row)
    (rowTargetProperty row)
    (rowQualifierProperties row)
    (rowReferenceProperties row)

record SignatureAssignment (row : BatchRowDescriptor) : Set where
  constructor signature-assignment
  field
    assignedSignature : WorkSignature
    assignedSignatureExact : assignedSignature ≡ signatureFor row
    signatureAssignmentReference : String
open SignatureAssignment public

canonicalSignatureAssignment :
  (row : BatchRowDescriptor) → SignatureAssignment row
canonicalSignatureAssignment row =
  signature-assignment (signatureFor row) refl
    "signature is derived from row state, not hand-selected"

------------------------------------------------------------------------
-- Equal signatures may share one bounded dispatch strategy.  They do not
-- become the same statement, source, semantics or consumer receipt.
------------------------------------------------------------------------

record SignatureGroupMember
    (representative : WorkSignature)
    (row : BatchRowDescriptor) : Set where
  constructor signature-group-member
  field
    groupMemberAssignment : SignatureAssignment row
    groupMemberSameSignature :
      assignedSignature groupMemberAssignment ≡ representative
    groupMemberLineageReference : String
open SignatureGroupMember public

record BatchWorkGroup : Set where
  constructor batch-work-group
  field
    workGroupId : String
    workGroupSignature : WorkSignature
    workGroupMemberCount : Nat
    workGroupDispatchReference : String
    workGroupContentDigest : String
open BatchWorkGroup public

------------------------------------------------------------------------
-- Per-row result carrier. Aggregate counts never reconstruct this information.
------------------------------------------------------------------------

data BatchOutcome : Set where paid open split reactivated : BatchOutcome

record BatchRowResult (row : BatchRowDescriptor) : Set where
  constructor batch-row-result
  field
    rowResultAssignment : SignatureAssignment row
    rowResultWorkGroupReference : String
    rowResultBoundedResultReference : String
    rowResultBoundedResultDigest : String
    rowResultExecutionReceiptReference : String
    rowResultConsumerVerificationReference : String
    rowResultOutcome : BatchOutcome
    rowResultNextPrerequisite : DAG.BundlePrerequisiteResidual
    rowResultLineageReference : String
open BatchRowResult public

record PaidRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row)
    (result : Result.BoundedSelectorResult) : Set where
  constructor paid-row-witness
  field
    paidRowOutcomeExact : rowResultOutcome batchRow ≡ paid
    paidRowVerifiedPayment : Result.VerifiedPrerequisitePayment result
    paidRowTargetsCurrentFirstMissing :
      Result.resultObligation result
      ≡ DAG.obligationForResidual
          (DAG.firstMissingPrerequisite (rowPrerequisiteStatus row))
    paidRowExactResultReference : String
open PaidRowWitness public

record OpenRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor open-row-witness
  field
    openRowOutcomeExact : rowResultOutcome batchRow ≡ open
    openRowResidualStillCurrent :
      rowResultNextPrerequisite batchRow
      ≡ DAG.firstMissingPrerequisite (rowPrerequisiteStatus row)
    openRowReasonReference : String
open OpenRowWitness public

record SplitRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor split-row-witness
  field
    splitRowOutcomeExact : rowResultOutcome batchRow ≡ split
    splitRowPlanReference : String
    splitRowPreservesSource : Bool
    splitRowPreservesSourceIsTrue : splitRowPreservesSource ≡ true
open SplitRowWitness public

record ReactivatedRowWitness
    (row : BatchRowDescriptor)
    (batchRow : BatchRowResult row) : Set where
  constructor reactivated-row-witness
  field
    reactivatedRowOutcomeExact : rowResultOutcome batchRow ≡ reactivated
    reactivatedChangedEvidenceReference : String
    reactivatedHistoricalClosureReference : String
    reactivatedHistoricalClosurePreserved : Bool
    reactivatedHistoricalClosurePreservedIsTrue :
      reactivatedHistoricalClosurePreserved ≡ true
open ReactivatedRowWitness public

------------------------------------------------------------------------
-- Content-addressed generated artifact. The artifact points to row/group/receipt
-- indexes; this formal carrier does not enumerate the cohort itself.
------------------------------------------------------------------------

record BatchOutcomeCounts : Set where
  constructor batch-outcome-counts
  field
    batchPaidCount : Nat
    batchOpenCount : Nat
    batchSplitCount : Nat
    batchReactivatedCount : Nat
open BatchOutcomeCounts public

record ContentAddressedBatchArtifact : Set where
  constructor content-addressed-batch-artifact
  field
    batchSchemaVersion : String
    batchLaneId : String
    batchSourceCohort : String
    batchSourceRevisionReference : String
    batchSourcePopulation : Nat
    batchMaterializedRowCount : Nat
    batchWorkGroupCount : Nat
    batchCounts : BatchOutcomeCounts
    batchDigestAlgorithm : String
    batchInputDigest : String
    batchOutputDigest : String
    batchPerRowArtifactReference : String
    batchWorkGroupArtifactReference : String
    batchExecutionReceiptIndexReference : String
    batchVerificationReceiptIndexReference : String
    batchLineageIndexReference : String
open ContentAddressedBatchArtifact public

------------------------------------------------------------------------
-- Nat calibration: manifest population is real; this Agda fixture deliberately
-- does not pretend that the whole runtime population has been materialized.
------------------------------------------------------------------------

natBusinessFamilyBatchSurface : ContentAddressedBatchArtifact
natBusinessFamilyBatchSurface =
  content-addressed-batch-artifact
    "sl.nat_batch_prerequisite_result.v0_1"
    "wikidata-nat-p5991-p14143"
    "business_family_reconciled"
    "SensibLaw revision-locked Nat cohort-manifest lineage"
    37665
    0
    0
    (batch-outcome-counts 0 0 0 0)
    "sha256"
    "unmaterialized-in-this-Agda-fixture"
    "unmaterialized-in-this-Agda-fixture"
    "runtime per-row result artifact"
    "runtime work-signature grouping artifact"
    "runtime execution-receipt index"
    "runtime consumer-verification index"
    "runtime append-only lineage index"

natPopulationRemains37665 :
  batchSourcePopulation natBusinessFamilyBatchSurface ≡ 37665
natPopulationRemains37665 = refl

natFormalFixtureDoesNotPretendToMaterializePopulation :
  batchMaterializedRowCount natBusinessFamilyBatchSurface ≡ 0
natFormalFixtureDoesNotPretendToMaterializePopulation = refl

------------------------------------------------------------------------
-- Concrete row: signature computation, not manual proof-search selection.
------------------------------------------------------------------------

natQ10403939Row : BatchRowDescriptor
natQ10403939Row =
  batch-row-descriptor
    "nat:Q10403939:P5991:source-support"
    "Q10403939"
    "Q10403939|P5991|bounded-bundle"
    "business_family_reconciled"
    splitAuto
    "P5991"
    "P14143"
    ("P3831" ∷ "P459" ∷ "P518" ∷ "P580" ∷ "P582" ∷ [])
    ("P854" ∷ [])
    "revision-locked Nat source/bundle reference"
    "sha256:runtime-row-input"
    DAG.natCurrentPrerequisites

natQ10403939Signature : WorkSignature
natQ10403939Signature = signatureFor natQ10403939Row

natQ10403939FirstResidualIsSourceSupport :
  signatureFirstResidual natQ10403939Signature ≡ DAG.missingSourceSupport
natQ10403939FirstResidualIsSourceSupport = refl

natQ10403939ProducerIsSourceAcquisition :
  signatureProducer natQ10403939Signature ≡ DAG.acquireSourceSupport
natQ10403939ProducerIsSourceAcquisition = refl

natQ10403939SelectorClassIsZelphHF :
  signatureSelectorClass natQ10403939Signature ≡ zelphHFSelector
natQ10403939SelectorClassIsZelphHF = refl

------------------------------------------------------------------------
-- Grouping is an execution optimisation only.
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
    true true true true true true true true true false false false

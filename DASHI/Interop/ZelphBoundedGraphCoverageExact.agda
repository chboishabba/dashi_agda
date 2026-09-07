module DASHI.Interop.ZelphBoundedGraphCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.ExternalContextSafetyBoundary as Safety

------------------------------------------------------------------------
-- Zelph/Hugging Face bounded graph transport and query coverage.
--
-- A successful manifest/shard fetch proves only that the requested transport
-- objects were obtained.  It does not prove that every graph fact relevant to
-- a semantic claim was inspected.  Coverage is always relative to a declared
-- query policy and graph revision.
------------------------------------------------------------------------

data TransportStatus : Set where
  transportComplete transportPartial transportFailed : TransportStatus

data QueryCoverageStatus : Set where
  queryCoverageComplete queryCoverageIncomplete queryCoverageInvalid : QueryCoverageStatus

record ZelphTransportReceipt : Set where
  constructor zelph-transport-receipt
  field
    manifestReference : String
    graphRevisionReference : String
    selectedShardReference : String
    transportStatus : TransportStatus
    partialGraphView : Bool
    partialGraphViewIsTrue : partialGraphView ≡ true
    readOnlyView : Bool
    readOnlyViewIsTrue : readOnlyView ≡ true
    inferenceAuthority : Bool
    inferenceAuthorityIsFalse : inferenceAuthority ≡ false
open ZelphTransportReceipt public

record QueryCoveragePolicy : Set where
  constructor query-coverage-policy
  field
    policyReference : String
    graphRevisionReference : String
    subjectCoverageReference : String
    propertyCoverageReference : String
    relationCoverageReference : String
    qualifierCoverageReference : String
    temporalCoverageReference : String
    siblingContextCoverageReference : String
open QueryCoveragePolicy public

record QueryCoverageReceipt : Set where
  constructor query-coverage-receipt
  field
    transport : ZelphTransportReceipt
    policy : QueryCoveragePolicy
    coverageStatus : QueryCoverageStatus
    unresolvedCoverageReference : String
    completenessReceiptReference : String
    coverageIsGlobalCompleteness : Bool
    coverageIsGlobalCompletenessIsFalse : coverageIsGlobalCompleteness ≡ false
open QueryCoverageReceipt public

safetyCoverage : QueryCoverageStatus → Safety.CoverageStatus
safetyCoverage queryCoverageComplete = Safety.coverageComplete
safetyCoverage queryCoverageIncomplete = Safety.coverageIncomplete
safetyCoverage queryCoverageInvalid = Safety.observationInvalid

incompleteQueryCoverageAbstains :
  Safety.dispositionForCoverage (safetyCoverage queryCoverageIncomplete)
  ≡ Safety.abstainForCoverage
incompleteQueryCoverageAbstains = refl

invalidQueryCoverageAbstains :
  Safety.dispositionForCoverage (safetyCoverage queryCoverageInvalid)
  ≡ Safety.abstainForInvalidObservation
invalidQueryCoverageAbstains = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ShardFetchImpliesQueryCoverageComplete : Set where
data PartialNonObservationImpliesGlobalAbsence : Set where
data QueryCoverageCompleteMeansWholeWikidataComplete : Set where

data QueryCoverageReceiptCreatesTruth : Set where

shardFetchDoesNotProveQueryCoverage :
  ShardFetchImpliesQueryCoverageComplete → ⊥
shardFetchDoesNotProveQueryCoverage ()

partialNonObservationDoesNotProveGlobalAbsence :
  PartialNonObservationImpliesGlobalAbsence → ⊥
partialNonObservationDoesNotProveGlobalAbsence ()

queryCoverageIsPolicyRelative :
  QueryCoverageCompleteMeansWholeWikidataComplete → ⊥
queryCoverageIsPolicyRelative ()

queryCoverageDoesNotCreateTruth :
  QueryCoverageReceiptCreatesTruth → ⊥
queryCoverageDoesNotCreateTruth ()

record ZelphBoundedGraphCoverageBoundary : Set where
  constructor zelph-bounded-graph-coverage-boundary
  field
    transportAndSemanticCoverageDistinct : Bool
    partialViewIsReadOnly : Bool
    partialViewHasInferenceAuthority : Bool
    incompleteCoverageAbstains : Bool
    nonObservationCreatesGlobalAbsence : Bool
    coverageIsDeclaredPolicyRelative : Bool
    coverageCreatesTruth : Bool

canonicalZelphBoundedGraphCoverageBoundary : ZelphBoundedGraphCoverageBoundary
canonicalZelphBoundedGraphCoverageBoundary =
  zelph-bounded-graph-coverage-boundary
    true true false true false true false

zelphBoundedGraphCoverageStatement : String
zelphBoundedGraphCoverageStatement =
  "A successful Zelph/HF shard fetch is transport evidence, not semantic completeness. Query coverage is revision- and policy-relative; incomplete or invalid coverage abstains, partial non-observation is not global absence, and no coverage receipt creates truth or promotion authority."

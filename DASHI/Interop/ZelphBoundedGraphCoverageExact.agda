module DASHI.Interop.ZelphBoundedGraphCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ExternalContextSafetyBoundary as Safety

data TransportStatus : Set where
  transportComplete transportPartial transportFailed : TransportStatus

data QueryCoverageStatus : Set where
  queryCoverageComplete
  queryCoverageIncomplete
  queryCoverageUninspected
  queryCoverageInvalid
  : QueryCoverageStatus

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
safetyCoverage queryCoverageUninspected = Safety.propertyNotInspected
safetyCoverage queryCoverageInvalid = Safety.observationInvalid

incompleteQueryCoverageAbstains :
  Safety.dispositionForCoverage (safetyCoverage queryCoverageIncomplete)
  ≡ Safety.abstainForCoverage
incompleteQueryCoverageAbstains = refl

uninspectedQueryCoverageAbstains :
  Safety.dispositionForCoverage (safetyCoverage queryCoverageUninspected)
  ≡ Safety.abstainForCoverage
uninspectedQueryCoverageAbstains = refl

invalidQueryCoverageAbstains :
  Safety.dispositionForCoverage (safetyCoverage queryCoverageInvalid)
  ≡ Safety.abstainForInvalidObservation
invalidQueryCoverageAbstains = refl

data ShardFetchImpliesQueryCoverageComplete : Set where
data PartialNonObservationImpliesGlobalAbsence : Set where
data UninspectedPropertyImpliesPropertyAbsent : Set where
data QueryCoverageCompleteMeansWholeWikidataComplete : Set where
data QueryCoverageReceiptCreatesTruth : Set where

shardFetchDoesNotProveQueryCoverage :
  ShardFetchImpliesQueryCoverageComplete → ⊥
shardFetchDoesNotProveQueryCoverage ()

partialNonObservationDoesNotProveGlobalAbsence :
  PartialNonObservationImpliesGlobalAbsence → ⊥
partialNonObservationDoesNotProveGlobalAbsence ()

uninspectedPropertyDoesNotProveAbsence :
  UninspectedPropertyImpliesPropertyAbsent → ⊥
uninspectedPropertyDoesNotProveAbsence ()

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
    uninspectedCoverageAbstains : Bool
    nonObservationCreatesGlobalAbsence : Bool
    uninspectedCreatesPropertyAbsence : Bool
    coverageIsDeclaredPolicyRelative : Bool
    coverageCreatesTruth : Bool

canonicalZelphBoundedGraphCoverageBoundary : ZelphBoundedGraphCoverageBoundary
canonicalZelphBoundedGraphCoverageBoundary =
  zelph-bounded-graph-coverage-boundary
    true true false true true false false true false

zelphBoundedGraphCoverageStatement : String
zelphBoundedGraphCoverageStatement =
  "A successful Zelph/HF shard fetch is transport evidence, not semantic completeness. Query coverage is revision- and policy-relative with distinct complete, incomplete, uninspected and invalid states. Incomplete/uninspected/invalid coverage abstains; partial or uninspected non-observation is not property absence; no coverage receipt creates truth or promotion authority."

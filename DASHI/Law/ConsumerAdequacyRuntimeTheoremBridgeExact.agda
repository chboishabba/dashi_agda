module DASHI.Law.ConsumerAdequacyRuntimeTheoremBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- Runtime coverage -> theorem-bearing ConsumerAdequate.
--
-- A runtime candidate may report that declared coordinates are present, but
-- the only constructor for theorem-backed adequacy below requires an actual
-- Query.AdequateFor inhabitant.  String theorem refs/digests retain provenance;
-- they are not substitutes for the proof field.
------------------------------------------------------------------------

record RuntimeAdequacyCandidate : Set where
  constructor runtimeAdequacyCandidate
  field
    queryRef : String
    projectionDigest : String
    coordinateComplete : Bool
    coordinateCompleteIsTrue : coordinateComplete ≡ true
    runtimeClaimsFormalFactorisation : Bool
    runtimeClaimsFormalFactorisationIsFalse :
      runtimeClaimsFormalFactorisation ≡ false
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open RuntimeAdequacyCandidate public

record TheoremBackedConsumerAdequacy
    {State Observation QueryType Answer : Set}
    (project : State → Observation)
    (semantics : Query.QuerySemantics State QueryType Answer)
    (query : QueryType) : Set₁ where
  constructor theoremBackedConsumerAdequacy
  field
    runtimeCandidate : RuntimeAdequacyCandidate
    theoremModuleRef : String
    theoremRef : String
    theoremArtifactDigest : String
    factorsThrough :
      Query.AdequateFor project semantics query
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open TheoremBackedConsumerAdequacy public

theoremBackedAdequacyFactorsThrough :
  ∀ {State Observation QueryType Answer}
    {project : State → Observation}
    {semantics : Query.QuerySemantics State QueryType Answer}
    {query : QueryType} →
  TheoremBackedConsumerAdequacy project semantics query →
  Query.AdequateFor project semantics query
theoremBackedAdequacyFactorsThrough =
  factorsThrough

data RuntimeCoordinateCoverageAutomaticallyFactorsThrough : Set where

runtimeCoverageAloneCannotCreateFactorisation :
  RuntimeCoordinateCoverageAutomaticallyFactorsThrough → ⊥
runtimeCoverageAloneCannotCreateFactorisation ()

------------------------------------------------------------------------
-- Concrete exact witness using the existing query-indexed owner.
------------------------------------------------------------------------

demoRuntimeCandidate : RuntimeAdequacyCandidate
demoRuntimeCandidate =
  runtimeAdequacyCandidate
    "query:surface"
    "sha256:demo-projection"
    true refl
    false refl
    true refl
    false refl
    false refl

demoTheoremBackedAdequacy :
  TheoremBackedConsumerAdequacy
    Query.demoProject
    Query.demoSemantics
    Query.surfaceQuery
demoTheoremBackedAdequacy =
  theoremBackedConsumerAdequacy
    demoRuntimeCandidate
    "DASHI.Core.QueryIndexedProjectionAdequacyExact"
    "surfaceQueryAdequate"
    "agda-owner:query-indexed-projection-adequacy"
    Query.surfaceQueryAdequate
    true refl
    false refl
    false refl

demoFormalAdequacyRecovered :
  Query.AdequateFor
    Query.demoProject
    Query.demoSemantics
    Query.surfaceQuery
demoFormalAdequacyRecovered =
  theoremBackedAdequacyFactorsThrough demoTheoremBackedAdequacy

record ConsumerAdequacyRuntimeTheoremBridgeBoundary : Set where
  constructor consumerAdequacyRuntimeTheoremBridgeBoundary
  field
    runtimeCoordinateCompletenessIsFormalAdequacy : Bool
    runtimeCoordinateCompletenessIsFormalAdequacyIsFalse :
      runtimeCoordinateCompletenessIsFormalAdequacy ≡ false

    theoremBackedReceiptRequiresAdequateForInhabitant : Bool
    theoremBackedReceiptRequiresAdequateForInhabitantIsTrue :
      theoremBackedReceiptRequiresAdequateForInhabitant ≡ true

    theoremRefStringAloneIsProof : Bool
    theoremRefStringAloneIsProofIsFalse :
      theoremRefStringAloneIsProof ≡ false

    theoremBackedAdequacyCreatesSemanticAuthority : Bool
    theoremBackedAdequacyCreatesSemanticAuthorityIsFalse :
      theoremBackedAdequacyCreatesSemanticAuthority ≡ false

    theoremBackedAdequacyCreatesClaimTruth : Bool
    theoremBackedAdequacyCreatesClaimTruthIsFalse :
      theoremBackedAdequacyCreatesClaimTruth ≡ false

open ConsumerAdequacyRuntimeTheoremBridgeBoundary public

canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary :
  ConsumerAdequacyRuntimeTheoremBridgeBoundary
canonicalConsumerAdequacyRuntimeTheoremBridgeBoundary =
  consumerAdequacyRuntimeTheoremBridgeBoundary
    false refl
    true refl
    false refl
    false refl
    false refl

module DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LIVE SLR P7d.5 EXECUTION RECEIPT
--
-- Source proposition: operator-supplied and PR-published execution receipt on
-- chboishabba/slr PR #24 at exact head efba015c....  This owner records the
-- observed runtime coordinates without promoting them into Agda proof, legal
-- authority, claim truth, or cross-backend JMD parity.
------------------------------------------------------------------------

slrRepository : String
slrRepository = "chboishabba/slr"

slrP7d5PullRequest : String
slrP7d5PullRequest = "https://github.com/chboishabba/slr/pull/24"

slrP7d5ExecutionReceiptComment : String
slrP7d5ExecutionReceiptComment =
  "https://github.com/chboishabba/slr/pull/24#issuecomment-5708030263"

slrP7d5Head : String
slrP7d5Head = "efba015c78480c324c4f99d7ec8dab4a31020640"

slrP7d5BaseHead : String
slrP7d5BaseHead = "73fc4d5a038ddac9bad4e18cf68143213a73ce6f"

record SlrP7d5ExecutionReceipt : Set where
  constructor slr-p7d5-execution-receipt
  field
    repositoryRef : String
    pullRequestRef : String
    exactHeadRef : String
    stackedBaseRef : String
    candidateProviderTestsGreen : Bool
    proofSearchLoopTestsGreen : Bool
    pgSourceStoreTestsGreen : Bool
    clippyWorkspaceGreen : Bool
    cargoWorkspaceGreen : Bool
    reportedProofSearchUnitTests : Nat
    reportedProofSearchIntegrationTests : Nat
    liveProviderSmokeObserved : Bool
    executionCreatesAgdaProof : Bool
    executionCreatesSemanticAuthority : Bool
    executionCreatesClaimTruth : Bool

open SlrP7d5ExecutionReceipt public

slrP7d5Execution : SlrP7d5ExecutionReceipt
slrP7d5Execution =
  slr-p7d5-execution-receipt
    slrRepository
    slrP7d5PullRequest
    slrP7d5Head
    slrP7d5BaseHead
    true
    true
    true
    true
    true
    92
    13
    true
    false
    false
    false

------------------------------------------------------------------------
-- OBSERVED MABO P710 PROVIDER -> NORMALIZED OBSERVATION COORDINATES
------------------------------------------------------------------------

record LiveMaboP710ObservationReceipt : Set where
  constructor live-mabo-p710-observation-receipt
  field
    p710ObjectRef : String
    p710RelationRef : String
    p710ValueRef : String
    p710RevisionRef : String
    p710ContentDigestRef : String
    p710DirectPropertyCandidates : Nat
    p710CandidateOnly : Bool
    p710CreatesSemanticAuthority : Bool
    p710ClaimTruthPromoted : Bool

open LiveMaboP710ObservationReceipt public

liveMaboP710Observation : LiveMaboP710ObservationReceipt
liveMaboP710Observation =
  live-mabo-p710-observation-receipt
    "Q1501525"
    "P710"
    "Q975866"
    "wikidata:Q1501525:oldid:2333409615"
    "sha256:43681681a832e9d0edf09f745c7d3e71fd4cdb9fd23d4670f25e5b94827b5eba"
    14
    true
    false
    false

------------------------------------------------------------------------
-- LIVE POSTGRESQL IDENTITY-CLASS LINEAGE RECEIPTS
------------------------------------------------------------------------

record LiveDiscoveryIdentityLineageReceipt : Set where
  constructor live-discovery-identity-lineage-receipt
  field
    lineageReceiptSha256 : String
    representationObjectRef : String
    identityClassRef : String
    receiptAuthorityRef : String
    lineageCandidateOnly : Bool
    lineageCreatesSemanticAuthority : Bool
    lineageApplicabilityPromoted : Bool
    lineageClaimTruthPromoted : Bool

open LiveDiscoveryIdentityLineageReceipt public

liveMaboCaseLineage : LiveDiscoveryIdentityLineageReceipt
liveMaboCaseLineage =
  live-discovery-identity-lineage-receipt
    "809c8590b57888ec05c8b9b7d8af385b88ea0703b61a51a861941e81e43457c5"
    "case:[1992]-HCA-23"
    "world-object:mabo-case-1992-hca-23"
    "candidate_world_expansion_only"
    true
    false
    false
    false

liveEddieMaboLineage : LiveDiscoveryIdentityLineageReceipt
liveEddieMaboLineage =
  live-discovery-identity-lineage-receipt
    "081e9065a40ca04f7b9865eb8b8820113089f9d9a1e15f3e2e41b702d257b8d7"
    "https://en.wikipedia.org/wiki/Eddie_Mabo"
    "world-object:eddie-mabo"
    "candidate_world_expansion_only"
    true
    false
    false
    false

------------------------------------------------------------------------
-- PAYMENT INTERPRETATION
--
-- P7d.5a-d are now execution-certified on the native SLR path.  The JMD lane
-- remains optional instrumentation: no cross-backend parity run or challenge
-- replay is inferred from the native SLR receipt.
------------------------------------------------------------------------

record P7d5RuntimePayment : Set where
  constructor p7d5-runtime-payment
  field
    worldIdentityClassRuntimeCertified : Bool
    normalizedObservationRuntimeCertified : Bool
    producerRevisionDigestRuntimeCertified : Bool
    getterParityBridgeCargoCertified : Bool
    identityClassPgLineageObserved : Bool
    crossBackendParityObserved : Bool
    jmdGetterRuntimeObserved : Bool
    jmdChallengeReplayObserved : Bool
    runtimePaymentCreatesAgdaProof : Bool
    runtimePaymentCreatesLegalAuthority : Bool
    runtimePaymentCreatesClaimTruth : Bool

open P7d5RuntimePayment public

slrP7d5Payment : P7d5RuntimePayment
slrP7d5Payment =
  p7d5-runtime-payment
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

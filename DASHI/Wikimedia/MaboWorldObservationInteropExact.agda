module DASHI.Wikimedia.MaboWorldObservationInteropExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.LeanSlrWorldObservationBidiExact as Observation
import DASHI.Wikimedia.SensibLawNatClimateSLRFixtureExact as NatClimate
import DASHI.Wikimedia.MaboWorldObjectIdentityExact as Identity
import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact as Runtime

------------------------------------------------------------------------
-- CONCRETE GOLDEN OBSERVATIONS
--
-- The native SLR Mabo P710 observation is now backed by the exact runtime
-- receipt published on SLR PR #24 at efba015c....  The interop/Lean carrier
-- below remains only a worked ABI fixture until JMD Lean is actually executed.
-- Backend choice is erased by normalization; source revision, content digest,
-- observed object/relation/value remain semantic coordinates.
------------------------------------------------------------------------

maboP710Observation : Observation.WorldObservation
maboP710Observation =
  Observation.mkWorldObservation
    "query:mabo:P710"
    (Runtime.p710ObjectRef Runtime.liveMaboP710Observation)
    (Runtime.p710RelationRef Runtime.liveMaboP710Observation)
    "wikidata"
    (Runtime.p710RevisionRef Runtime.liveMaboP710Observation)
    (Runtime.p710ContentDigestRef Runtime.liveMaboP710Observation)
    (Runtime.p710ValueRef Runtime.liveMaboP710Observation)
    Observation.retrievalSucceeded
    Observation.currentFreshness
    Observation.providerRevisionProvenance

maboSlrGetterFixture : Observation.SlrGetterObservation
maboSlrGetterFixture =
  Observation.mkSlrGetterObservation
    maboP710Observation
    "slr-native@efba015c78480c324c4f99d7ec8dab4a31020640"

maboInteropGetterFixture : Observation.LeanGetterObservation
maboInteropGetterFixture =
  Observation.mkLeanGetterObservation maboP710Observation "interop-worked-example:not-run"

maboNormalizedAgreement :
  Observation.normalizeSlrGetter maboSlrGetterFixture
  ≡ Observation.normalizeLeanGetter maboInteropGetterFixture
maboNormalizedAgreement = refl

maboSlrRuntimeObservationObserved : Bool
maboSlrRuntimeObservationObserved = true

maboInteropRuntimeObservationObserved : Bool
maboInteropRuntimeObservationObserved = false

maboCrossRuntimeParityObserved : Bool
maboCrossRuntimeParityObserved = false

------------------------------------------------------------------------
-- NAT CLIMATE: SECOND REAL TEST FAMILY USING THE SAME ABI.
--
-- The canonical fixture already pins Q10884 and provided_snapshot_2026-04-01,
-- and keeps the P5991 -> P14143 migration review-only/split-required. This
-- observation therefore demonstrates backend-independent ABI reuse without
-- promoting the migration as approved or semantically equivalent.
------------------------------------------------------------------------

natClimateObservation : Observation.WorldObservation
natClimateObservation =
  Observation.mkWorldObservation
    "query:nat-climate:p5991-p14143"
    "Q10884"
    "migration:P5991->P14143"
    "sensiblaw:nat-climate-fixture"
    "provided_snapshot_2026-04-01"
    "fixture-content-hash-not-pinned-in-this-agda-owner"
    "review-required"
    Observation.retrievalSucceeded
    Observation.unknownFreshness
    Observation.providerRevisionProvenance

natClimateSourceUnitReference : String
natClimateSourceUnitReference =
  "unit:wikidata_user_sandbox:nat_wdu:p5991_p14143:2026-04-01"

------------------------------------------------------------------------
-- STRUCTURAL PRODUCER ARTIFACT -> EXPANSION-CANDIDATE PROJECTION
--
-- This pays the field-preservation gap left by the earlier Boolean-only owner.
-- The source artifact is revision/digest-bound before a candidate is formed.
------------------------------------------------------------------------

record AcquiredProducerArtifact : Set where
  constructor acquired-producer-artifact
  field
    artifactObjectReference : String
    artifactRelationReference : String
    artifactValueReference : String
    artifactSourceReference : String
    artifactSourceRevisionReference : String
    artifactContentDigestReference : String
    artifactCandidateOnly : Bool
    artifactCandidateOnlyIsTrue : artifactCandidateOnly ≡ true
    artifactCreatesSemanticAuthority : Bool
    artifactCreatesSemanticAuthorityIsFalse : artifactCreatesSemanticAuthority ≡ false
    artifactCreatesClaimTruth : Bool
    artifactCreatesClaimTruthIsFalse : artifactCreatesClaimTruth ≡ false

open AcquiredProducerArtifact public

record ExpansionCandidateProjection : Set where
  constructor expansion-candidate-projection
  field
    candidateReference : String
    discoveryParentReference : String
    candidateObjectReference : String
    candidateRelationReference : String
    candidateSourceRevisionReference : String
    candidateContentDigestReference : String
    triggeringResidualReference : String
    candidateIdentityClassReference : String
    projectionCreatesSemanticAuthority : Bool
    projectionCreatesSemanticAuthorityIsFalse : projectionCreatesSemanticAuthority ≡ false
    projectionCreatesClaimTruth : Bool
    projectionCreatesClaimTruthIsFalse : projectionCreatesClaimTruth ≡ false

open ExpansionCandidateProjection public

adaptRevisionedArtifact :
  AcquiredProducerArtifact → String → String → String → ExpansionCandidateProjection
adaptRevisionedArtifact artifact candidate residual identityClass =
  expansion-candidate-projection
    candidate
    (artifactObjectReference artifact)
    (artifactValueReference artifact)
    (artifactRelationReference artifact)
    (artifactSourceRevisionReference artifact)
    (artifactContentDigestReference artifact)
    residual
    identityClass
    false refl false refl

maboP710Artifact : AcquiredProducerArtifact
maboP710Artifact =
  acquired-producer-artifact
    (Runtime.p710ObjectRef Runtime.liveMaboP710Observation)
    (Runtime.p710RelationRef Runtime.liveMaboP710Observation)
    (Runtime.p710ValueRef Runtime.liveMaboP710Observation)
    "wikidata"
    (Runtime.p710RevisionRef Runtime.liveMaboP710Observation)
    (Runtime.p710ContentDigestRef Runtime.liveMaboP710Observation)
    true refl false refl false refl

maboP710CandidateProjection : ExpansionCandidateProjection
maboP710CandidateProjection =
  adaptRevisionedArtifact
    maboP710Artifact
    "wikidata:Q1501525:P710:Q975866"
    "residual:mabo:participant-identity"
    (Identity.identityClassReference Identity.eddieMaboIdentity)

maboAdapterPreservesRevision :
  candidateSourceRevisionReference maboP710CandidateProjection
  ≡ artifactSourceRevisionReference maboP710Artifact
maboAdapterPreservesRevision = refl

maboAdapterPreservesObservedObject :
  candidateObjectReference maboP710CandidateProjection
  ≡ artifactValueReference maboP710Artifact
maboAdapterPreservesObservedObject = refl

------------------------------------------------------------------------
-- PARITY DISAGREEMENT IS FRONTIER WORK, NOT A TRUTH JUDGMENT.
------------------------------------------------------------------------

record GetterParityResidualBridge : Set where
  constructor getter-parity-residual-bridge
  field
    parityResidualReference : String
    triggeringObservationReference : String
    proofResidualProducerClass : String
    residualIsOpenResearchWork : Bool
    parityResidualChoosesWorldTruth : Bool
    parityResidualCreatesSemanticAuthority : Bool

open GetterParityResidualBridge public

maboGetterParityResidualBridge : GetterParityResidualBridge
maboGetterParityResidualBridge =
  getter-parity-residual-bridge
    "getter-parity:query:mabo:P710:P710"
    "query:mabo:P710"
    "producer:getter-parity"
    true
    false
    false

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data GetterBackendEqualsObservationSemantics : Set where
data GetterParityResidualEqualsTruthJudgment : Set where
data ReachableWikidataRouteEqualsAcquiredRevisionedEntity : Set where
data RevisionStringWithoutSourceBindingEqualsRevisionReceipt : Set where
data RepresentationStringEqualsIdentityClass : Set where
data NatClimateReviewFixtureEqualsMigrationApproval : Set where

data NativeRuntimeObservationEqualsCrossBackendParity : Set where

getterBackendDoesNotEqualObservationSemantics :
  GetterBackendEqualsObservationSemantics → ⊥
getterBackendDoesNotEqualObservationSemantics ()

getterParityResidualDoesNotEqualTruthJudgment :
  GetterParityResidualEqualsTruthJudgment → ⊥
getterParityResidualDoesNotEqualTruthJudgment ()

reachableWikidataRouteDoesNotEqualAcquiredRevisionedEntity :
  ReachableWikidataRouteEqualsAcquiredRevisionedEntity → ⊥
reachableWikidataRouteDoesNotEqualAcquiredRevisionedEntity ()

revisionStringWithoutSourceBindingDoesNotEqualRevisionReceipt :
  RevisionStringWithoutSourceBindingEqualsRevisionReceipt → ⊥
revisionStringWithoutSourceBindingDoesNotEqualRevisionReceipt ()

representationStringDoesNotEqualIdentityClass :
  RepresentationStringEqualsIdentityClass → ⊥
representationStringDoesNotEqualIdentityClass ()

natClimateReviewFixtureDoesNotEqualMigrationApproval :
  NatClimateReviewFixtureEqualsMigrationApproval → ⊥
natClimateReviewFixtureDoesNotEqualMigrationApproval ()

nativeRuntimeObservationDoesNotEqualCrossBackendParity :
  NativeRuntimeObservationEqualsCrossBackendParity → ⊥
nativeRuntimeObservationDoesNotEqualCrossBackendParity ()

module DASHI.Interop.KantRuntimeObservationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.KantIntrospectiveResidualContractsExact as Kant

------------------------------------------------------------------------
-- KANT RUNTIME OBSERVATION SURFACE
--
-- This is deliberately an observation/conformance ABI, not a crypto proof and
-- not a replacement for the Lean specification under RequestProject/Kant/.
-- It lets the deployed client/relay produce evidence that can be compared with
-- the formal specification without allowing observed runtime behavior to
-- silently become theorem authority.
------------------------------------------------------------------------

record RuntimeVectorObservation : Set where
  constructor runtime-vector-observation
  field
    vectorId : String
    actionReference : String
    inputStateDigest : String
    observedOutputDigest : String
    expectedOutputDigest : String
    runtimeRevision : String
    specRevision : String
    matchesExpected : Bool

open RuntimeVectorObservation public

record RuntimeVectorBatchReceipt : Set where
  constructor runtime-vector-batch-receipt
  field
    vectorSetReference : String
    generatorRevision : String
    runtimeReference : String
    runtimeRevision : String
    specReference : String
    specRevision : String
    observationLogReference : String
    allCoveredVectorsMatched : Bool
    coverageReference : String

open RuntimeVectorBatchReceipt public

batchToConformanceReceipt : RuntimeVectorBatchReceipt → Kant.RuntimeConformanceReceipt
batchToConformanceReceipt batch =
  Kant.runtime-conformance-receipt
    (specReference batch)
    (specRevision batch)
    (runtimeReference batch)
    (runtimeRevision batch)
    (vectorSetReference batch)
    (generatorRevision batch)
    (observationLogReference batch)
    (vectorSetReference batch)
    (coverageReference batch)
    (allCoveredVectorsMatched batch)

------------------------------------------------------------------------
-- Relay diagnostic ladder.
-- H0 alone is health/process reachability.  Higher stages remain separately
-- observable; no lower stage creates the next one by construction.
------------------------------------------------------------------------

record RelayObservationReceipt : Set where
  constructor relay-observation-receipt
  field
    relayReference : String
    relayRevision : String
    healthObservationReference : String
    stateObservationReference : String
    advertiseObservationReference : String
    lookupObservationReference : String
    crossBrowserObservationReference : String
    connectionObservationReference : String
    messageObservationReference : String
    confidentialityObservationReference : String

    h0WorkerReachable : Bool
    h1RelayStateAvailable : Bool
    h2RoomAdvertisementSucceeds : Bool
    h3SecondBrowserFindsRoom : Bool
    h4ConnectionForms : Bool
    h5MessageCrosses : Bool
    h6ConfidentialityAndBindingObserved : Bool

open RelayObservationReceipt public

------------------------------------------------------------------------
-- Storage/publication observation.
------------------------------------------------------------------------

record StoragePublicationObservation : Set where
  constructor storage-publication-observation
  field
    storageNodeReference : String
    collectedArtifactReference : String
    collectedArtifactDigest : String
    rightsReceiptReference : String
    publicationTargetReference : String
    publicationRevision : String
    collectionSucceeded : Bool
    rightsGatePassed : Bool
    publicationSucceeded : Bool

open StoragePublicationObservation public

------------------------------------------------------------------------
-- Runtime observation still does not create theorem/security/rights authority.
------------------------------------------------------------------------

data RuntimeObservationCreatesSpecProofPermission : Set where
data RelayHealthCreatesEndToEndPermission : Set where
data CollectionCreatesPublicationPermission : Set where

data PublicationSuccessCreatesRightsPermission : Set where

runtimeObservationDoesNotCreateSpecProof :
  RuntimeObservationCreatesSpecProofPermission → ⊥
runtimeObservationDoesNotCreateSpecProof ()

relayHealthDoesNotCreateEndToEndSuccess :
  RelayHealthCreatesEndToEndPermission → ⊥
relayHealthDoesNotCreateEndToEndSuccess ()

collectionDoesNotCreatePublicationPermission :
  CollectionCreatesPublicationPermission → ⊥
collectionDoesNotCreatePublicationPermission ()

publicationSuccessDoesNotCreateRights :
  PublicationSuccessCreatesRightsPermission → ⊥
publicationSuccessDoesNotCreateRights ()

record KantRuntimeObservationBoundary : Set where
  constructor kant-runtime-observation-boundary
  field
    vectorsBindSpecAndRuntimeRevisions : Bool
    healthIsNotEndToEnd : Bool
    confidentialityNeedsSeparateObservation : Bool
    collectionAndPublicationAreSeparate : Bool
    publicationNeedsRightsGate : Bool

canonicalKantRuntimeObservationBoundary : KantRuntimeObservationBoundary
canonicalKantRuntimeObservationBoundary =
  kant-runtime-observation-boundary true true true true true

module DASHI.Physics.Closure.HEPDataBridgeWorkerQueue where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataEmpiricalSourceCandidateDiagnostic as Source

------------------------------------------------------------------------
-- W0-owned HEPData bridge worker queue.
--
-- This is a coordination surface only.  It records the next disjoint HEPData
-- lanes after the empirical-source candidate diagnostic.  It does not
-- construct the schema, projection, authority adapter, comparison law, W3
-- receipt, or W8 receipt.

data HEPDataBridgeWorkerLane : Set where
  HEP-A-observable-schema :
    HEPDataBridgeWorkerLane
  HEP-B-observable-selection :
    HEPDataBridgeWorkerLane
  HEP-C-unit-calibration :
    HEPDataBridgeWorkerLane
  HEP-D-projection-rejection :
    HEPDataBridgeWorkerLane
  HEP-E-comparison-authority :
    HEPDataBridgeWorkerLane
  HEP-F-itir-provenance-adapter :
    HEPDataBridgeWorkerLane

canonicalHEPDataBridgeWorkerLanes :
  List HEPDataBridgeWorkerLane
canonicalHEPDataBridgeWorkerLanes =
  HEP-A-observable-schema
  ∷ HEP-B-observable-selection
  ∷ HEP-C-unit-calibration
  ∷ HEP-D-projection-rejection
  ∷ HEP-E-comparison-authority
  ∷ HEP-F-itir-provenance-adapter
  ∷ []

data HEPDataBridgeWorkerQueueStatus : Set where
  assignedAwaitingTypedReceiptsOrDiagnostics :
    HEPDataBridgeWorkerQueueStatus

data HEPDataBridgeWorkerQueueBoundary : Set where
  noSharedDiagramEditsByWorkers :
    HEPDataBridgeWorkerQueueBoundary
  workersReturnDiagramDeltasToW0 :
    HEPDataBridgeWorkerQueueBoundary
  noProviderReceiptFabrication :
    HEPDataBridgeWorkerQueueBoundary
  noProjectionByInference :
    HEPDataBridgeWorkerQueueBoundary
  noAuthorityFromSourcePresenceAlone :
    HEPDataBridgeWorkerQueueBoundary

canonicalHEPDataBridgeWorkerQueueBoundaries :
  List HEPDataBridgeWorkerQueueBoundary
canonicalHEPDataBridgeWorkerQueueBoundaries =
  noSharedDiagramEditsByWorkers
  ∷ workersReturnDiagramDeltasToW0
  ∷ noProviderReceiptFabrication
  ∷ noProjectionByInference
  ∷ noAuthorityFromSourcePresenceAlone
  ∷ []

record HEPDataBridgeWorkerQueue : Setω where
  field
    sourceCandidateDiagnostic :
      Source.HEPDataEmpiricalSourceCandidateDiagnostic

    lanes :
      List HEPDataBridgeWorkerLane

    lanesAreCanonical :
      lanes ≡ canonicalHEPDataBridgeWorkerLanes

    queueStatus :
      HEPDataBridgeWorkerQueueStatus

    boundaries :
      List HEPDataBridgeWorkerQueueBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalHEPDataBridgeWorkerQueueBoundaries

    workerInstructions :
      List String

    nonPromotionBoundary :
      List String

canonicalHEPDataBridgeWorkerQueue :
  HEPDataBridgeWorkerQueue
canonicalHEPDataBridgeWorkerQueue =
  record
    { sourceCandidateDiagnostic =
        Source.canonicalHEPDataEmpiricalSourceCandidateDiagnostic
    ; lanes =
        canonicalHEPDataBridgeWorkerLanes
    ; lanesAreCanonical =
        refl
    ; queueStatus =
        assignedAwaitingTypedReceiptsOrDiagnostics
    ; boundaries =
        canonicalHEPDataBridgeWorkerQueueBoundaries
    ; boundariesAreCanonical =
        refl
    ; workerInstructions =
        "HEP-A owns HEPDataObservable schema/checksum only"
        ∷ "HEP-B owns one observable/table-column selection request or diagnostic only"
        ∷ "HEP-C owns unit/dimension/calibration request or diagnostic only"
        ∷ "HEP-D owns MeasurementSurface projection implementation or typed rejection only"
        ∷ "HEP-E owns comparison law and accepted-authority route request or diagnostic only"
        ∷ "HEP-F owns ITIR provenance adapter diagnostic or binding request only"
        ∷ "Workers must return diagram node/edge deltas to W0; W0 updates shared diagrams"
        ∷ []
    ; nonPromotionBoundary =
        "This queue assigns bridge lanes but constructs no HEPDataObservable schema"
        ∷ "This queue constructs no MeasurementSurface -> DashiState projection"
        ∷ "This queue constructs no comparison law, authority token, W3 receipt, or W8 receipt"
        ∷ []
    }

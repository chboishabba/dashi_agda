module DASHI.ComputerScience.RSA260GNFSStageRunReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GNFSComponentProvenanceExact as Component

------------------------------------------------------------------------
-- STAGE-RUN RECEIPT
--
-- A component provenance edge does not by itself establish that the component
-- executed in the RSA-260 run.  This owner keeps implementation provenance and
-- run participation separate, then records only the stage/run facts explicitly
-- reported by Eric Lu's first-party account.
------------------------------------------------------------------------

record StageRunReceipt : Set where
  constructor stage-run-receipt
  field
    stage : Component.GNFSStage
    implementationReference : String
    runReference : String
    sourceReference : String
    firstPartyReportedExecution : Bool
    independentlyReproduced : Bool
    executableArtifactPubliclyBound : Bool
    exactRevisionBound : Bool
open StageRunReceipt public

rsa260PolyselectRun : StageRunReceipt
rsa260PolyselectRun =
  stage-run-receipt
    Component.polynomialSelectionStage1
    "GPU-adapted CADO-NFS stage-1 polyselect with components from msieve"
    "RSA-260 run reported by Eric Lu"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    true false false false

rsa260LatticeSieveRun : StageRunReceipt
rsa260LatticeSieveRun =
  stage-run-receipt
    Component.latticeSieving
    "GPU-optimized lattice siever based on CADO-NFS las"
    "RSA-260 run reported by Eric Lu"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    true false false false

rsa260FilteringRun : StageRunReceipt
rsa260FilteringRun =
  stage-run-receipt
    Component.filtering
    "parallelized/optimized dup-purge and fused merge-replay path"
    "RSA-260 run reported by Eric Lu"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    true false false false

rsa260LinearAlgebraRun : StageRunReceipt
rsa260LinearAlgebraRun =
  stage-run-receipt
    Component.sparseLinearAlgebra
    "new GPU-optimized block Wiedemann implementation"
    "RSA-260 run reported by Eric Lu"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    true false false false

rsa260SquareRootRun : StageRunReceipt
rsa260SquareRootRun =
  stage-run-receipt
    Component.squareRoot
    "GPU-accelerated sqrt"
    "RSA-260 run reported by Eric Lu"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    true false false false

------------------------------------------------------------------------
-- Non-collapse rules.
------------------------------------------------------------------------

data ProvenanceImpliesExecution : Set where
data ReportedExecutionImpliesIndependentReproduction : Set where
data ReportedExecutionImpliesPublicExecutableArtifact : Set where
data StageExecutionImpliesExactRevision : Set where

provenanceDoesNotCreateRunReceipt : ProvenanceImpliesExecution → ⊥
provenanceDoesNotCreateRunReceipt ()

reportedRunDoesNotCreateIndependentReproduction :
  ReportedExecutionImpliesIndependentReproduction → ⊥
reportedRunDoesNotCreateIndependentReproduction ()

reportedRunDoesNotCreatePublicArtifact :
  ReportedExecutionImpliesPublicExecutableArtifact → ⊥
reportedRunDoesNotCreatePublicArtifact ()

stageRunDoesNotIdentifyExactRevision : StageExecutionImpliesExactRevision → ⊥
stageRunDoesNotIdentifyExactRevision ()

record RSA260StageRunBoundary : Set where
  constructor rsa260-stage-run-boundary
  field
    implementationAndExecutionSeparated : Bool
    firstPartyRunParticipationRecorded : Bool
    independentReproductionPaid : Bool
    executableArtifactPubliclyBound : Bool
    exactRevisionPaid : Bool
open RSA260StageRunBoundary public

canonicalRSA260StageRunBoundary : RSA260StageRunBoundary
canonicalRSA260StageRunBoundary =
  rsa260-stage-run-boundary true true false false false

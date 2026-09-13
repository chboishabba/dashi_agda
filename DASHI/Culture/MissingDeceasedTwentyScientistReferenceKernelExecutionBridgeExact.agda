module DASHI.Culture.MissingDeceasedTwentyScientistReferenceKernelExecutionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceExecutionKernelExact as Execution
import DASHI.Culture.MissingDeceasedTwentyScientistScienceReferenceKernelBidiExact as Reference

------------------------------------------------------------------------
-- THIN BRIDGE: existing all-20 execution surface -> source-coordinate kernels
--
-- The existing execution kernel remains the owner of the twenty science rows.
-- The reference-kernel layer refines four source-replay-ready fibres with
-- deterministic source-coordinate projections.  It does not promote those
-- projections into reproduction of the original paper algorithms.
------------------------------------------------------------------------

executionKernelScientistCount : Nat
executionKernelScientistCount = Execution.scienceExecutionKernelsCount

referenceKernelBindingCount : Nat
referenceKernelBindingCount = Reference.referenceKernelBindingsCount

sourceReplayReadyBaselineCount : Nat
sourceReplayReadyBaselineCount = Execution.scienceSourceReplayReadyCount

referenceKernelRefinesExecutionSurface : Bool
referenceKernelRefinesExecutionSurface = true

referenceKernelReplacesExecutionOwner : Bool
referenceKernelReplacesExecutionOwner = false

referenceProjectionPaysSourceAlgorithm : Bool
referenceProjectionPaysSourceAlgorithm = false

referenceProjectionPaysHistoricalUse : Bool
referenceProjectionPaysHistoricalUse = false

referenceProjectionPaysCustody : Bool
referenceProjectionPaysCustody = false

hiddenProducerStillRoutesProofDebt : Bool
hiddenProducerStillRoutesProofDebt = true

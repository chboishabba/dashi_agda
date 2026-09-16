module DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BScreenReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact as Kernel
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4N3BCharacterAcquisitionExact as Acquisition

------------------------------------------------------------------------
-- FIVE-ORBIT D4 / N(3B) EXECUTION RECEIPT BOUNDARY
--
-- The GAP producer has two explicit stages:
--
--   1. enumerate admissible D4 -> MN3B class fusions and test whether the
--      actual restricted Monster character contains
--
--        theta = (5,5,1,3,3) = 3 A1 + B1 + B2;
--
--   2. construct the existing AtlasRep MN3B group, find a concrete D8 inside
--      a Sylow-2 subgroup, transport the canonical D4 classes through an
--      explicit group isomorphism, and identify the resulting MN3B class
--      fusion by ambient order/class-size invariants.
--
-- Source for both stages is written.  The dedicated shell checker, the existing
-- GAP/CTblLib/AtlasRep workflow wiring and the JSON artifact upload path are
-- also written.  These execution-enablement receipts remain strictly weaker
-- than observing a GAP runtime result on this revision.
------------------------------------------------------------------------

kernelBoundary : Kernel.FiveOrbitD4KernelCharacterBoundary
kernelBoundary = Kernel.currentFiveOrbitD4KernelCharacterBoundary

acquisitionBoundary : Acquisition.FiveOrbitD4N3BCharacterAcquisition
acquisitionBoundary = Acquisition.currentFiveOrbitD4N3BCharacterAcquisition

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SourceScriptCreatesRuntimeReceipt : Set where
data PossibleFusionCreatesActualD4Subgroup : Set where
data CharacterContainmentCreatesSelectedActionWeld : Set where

data ExecutionWiringCreatesRuntimeVerdict : Set where

sourceScriptDoesNotCreateRuntimeReceipt :
  SourceScriptCreatesRuntimeReceipt → ⊥
sourceScriptDoesNotCreateRuntimeReceipt ()

possibleFusionDoesNotCreateActualD4Subgroup :
  PossibleFusionCreatesActualD4Subgroup → ⊥
possibleFusionDoesNotCreateActualD4Subgroup ()

characterContainmentDoesNotCreateSelectedActionWeld :
  CharacterContainmentCreatesSelectedActionWeld → ⊥
characterContainmentDoesNotCreateSelectedActionWeld ()

executionWiringDoesNotCreateRuntimeVerdict :
  ExecutionWiringCreatesRuntimeVerdict → ⊥
executionWiringDoesNotCreateRuntimeVerdict ()

------------------------------------------------------------------------
-- Runtime boundary.
------------------------------------------------------------------------

record FiveOrbitD4N3BScreenReceipt : Set where
  constructor five-orbit-d4-n3b-screen-receipt
  field
    targetCharacterSourceWritten : Bool
    targetCharacterIsThreeA1B1B2 : Bool
    characterTableFusionScreenSourceWritten : Bool
    actualD4RealizationSourceWritten : Bool
    canonicalClassTransportUsedForActualFusion : Bool
    executionCheckerSourceWritten : Bool
    existingGapWorkflowWired : Bool
    jsonArtifactUploadWired : Bool
    possibleFusionCountObserved : Bool
    characterCompatibleFusionCountObserved : Bool
    actualD4SubgroupRuntimeObserved : Bool
    actualD4CharacterCompatibilityObserved : Bool
    gapRuntimeReceiptObserved : Bool
    selectedActionSameObjectPaid : Bool
    selectedActionIntertwinerPaid : Bool
    minimumRuntimeCountsPromotedToTheorem : Bool
    nextResidual : String
open FiveOrbitD4N3BScreenReceipt public

currentFiveOrbitD4N3BScreenReceipt : FiveOrbitD4N3BScreenReceipt
currentFiveOrbitD4N3BScreenReceipt =
  five-orbit-d4-n3b-screen-receipt
    true true true true true
    true true true
    false false false false false
    false false false
    "The producer, dedicated checker, established GAP/CTblLib/AtlasRep workflow hook and JSON artifact upload path are all source-written. Execute the workflow and observe build/monster_3b_five_orbit_d4_n3b_screen.json before promoting any runtime field. First record the exhaustive D4->MN3B character-fusion count and which fusions contain theta=(5,5,1,3,3)=3A1+B1+B2. Separately record whether the constructible MN3B model realizes a concrete D8 whose canonical class fusion is uniquely identified and character-compatible. Even a positive realized subgroup remains weaker than Selected3BNormalizerMonsterActionWeld: the actual selected Monster carrier/action intertwiner must still be paid independently."

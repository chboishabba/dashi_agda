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
--      every compatible fusion is now retained literally, including its
--      five-entry D4 -> MN3B fusion, induced D4 -> Monster class positions,
--      canonical pulled values, D4 multiplicities, and the central r^2 image
--      labelled through the stored MN3B -> Monster fusion and Monster ATLAS
--      class names;
--
--   2. construct the existing AtlasRep MN3B group, find a concrete D8 inside
--      a Sylow-2 subgroup, transport the canonical D4 classes through an
--      explicit group isomorphism, and identify the resulting MN3B class
--      fusion by ambient order/class-size invariants.
--
-- The Python residual scheduler now has a literal-row loader for the same raw
-- JSON artifact. It refuses count-only receipts and keeps the literal MN3B and
-- Monster fusion lists separate. This is source/interface payment only: the
-- updated GAP producer has not been rerun on this revision here, so neither the
-- literal 17-row artifact nor its 2A/2B split is promoted to a runtime receipt.
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
data LiteralRowsSourceCreatesObservedRows : Set where

data CentralClassDerivationSourceCreatesObservedSplit : Set where

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

literalRowsSourceDoesNotCreateObservedRows :
  LiteralRowsSourceCreatesObservedRows → ⊥
literalRowsSourceDoesNotCreateObservedRows ()

centralClassDerivationSourceDoesNotCreateObservedSplit :
  CentralClassDerivationSourceCreatesObservedSplit → ⊥
centralClassDerivationSourceDoesNotCreateObservedSplit ()

------------------------------------------------------------------------
-- Runtime boundary.
------------------------------------------------------------------------

record FiveOrbitD4N3BScreenReceipt : Set where
  constructor five-orbit-d4-n3b-screen-receipt
  field
    targetCharacterSourceWritten : Bool
    targetCharacterIsThreeA1B1B2 : Bool
    characterTableFusionScreenSourceWritten : Bool
    literalCharacterCompatibleFusionRowsSourceWritten : Bool
    centralMonsterClassLabelDerivedFromFusionSourceWritten : Bool
    literalFusionSchedulerLoaderSourceWritten : Bool
    actualD4RealizationSourceWritten : Bool
    canonicalClassTransportUsedForActualFusion : Bool
    failLocatingRuntimeReceiptSourceWritten : Bool
    executionCheckerSourceWritten : Bool
    existingGapWorkflowWired : Bool
    directExecutionBranchPushTriggerWritten : Bool
    failLocatingSummaryClassifierSourceWritten : Bool
    jsonArtifactUploadWired : Bool
    summaryArtifactUploadWired : Bool
    possibleFusionCountObserved : Bool
    characterCompatibleFusionCountObserved : Bool
    literalFusionRowsRuntimeObserved : Bool
    central2A2BSplitRuntimeObserved : Bool
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
    true true true
    true true true
    true true
    true true true true true true true
    false false false false false false false
    false false false
    "The producer now source-writes every compatible D4 -> MN3B fusion row into build/monster_3b_five_orbit_d4_n3b_screen.json, retains the induced D4 -> Monster class positions, derives the central r^2 ATLAS label from the actual stored fusion maps, and exposes a Python scheduler loader that rejects count-only receipts. The updated producer has not been rerun on this revision here, so the literal row artifact, its expected 17-world cardinality, and the 9x2A/8x2B central split remain unobserved runtime coordinates. The next payment is a real GAP rerun followed by exact pytest over the regenerated artifact. If the 17 literal rows and 9/8 split reproduce, schedule on the real fusion rows and derive induced Monster-profile collisions before opening any matrix route. Even a positive realized compatible subgroup remains weaker than Selected3BNormalizerMonsterActionWeld: the actual selected Monster carrier/action intertwiner must still be paid independently."

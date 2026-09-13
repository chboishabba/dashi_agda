module DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionCostComparisonExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionPathBidiExact as Bidi
import DASHI.ComputerScience.HelloWorldBinaryTernaryFramedWordStorageExact as Storage

------------------------------------------------------------------------
-- FIRST CONSUMER-INDEXED BINARY / TERNARY COST COMPARISON
--
-- The execution path is already proved identical.  This module packages the
-- first explicit comparison showing that execution consumers can agree while
-- representation consumers differ.  No physical superiority is inferred.
------------------------------------------------------------------------

record SharedExecutionDifferentRepresentationReceipt : Set where
  constructor sharedExecutionDifferentRepresentationReceipt
  field
    binaryTransitionCost : Nat
    ternaryTransitionCost : Nat
    binaryHeadTravelCost : Nat
    ternaryHeadTravelCost : Nat
    binaryProgramCells : Nat
    ternaryProgramCells : Nat
    binaryDataCells : Nat
    ternaryDataCells : Nat
    transitionsSame : binaryTransitionCost ≡ ternaryTransitionCost
    headTravelSame : binaryHeadTravelCost ≡ ternaryHeadTravelCost
    binaryProgramCellsExact : binaryProgramCells ≡ 126
    ternaryProgramCellsExact : ternaryProgramCells ≡ 42
    binaryDataCellsExact : binaryDataCells ≡ 117
    ternaryDataCellsExact : ternaryDataCells ≡ 39

canonicalSharedExecutionDifferentRepresentationReceipt :
  SharedExecutionDifferentRepresentationReceipt
canonicalSharedExecutionDifferentRepresentationReceipt =
  sharedExecutionDifferentRepresentationReceipt
    Bidi.binaryTransitionCost
    Bidi.ternary27TransitionCost
    Bidi.binaryHeadTravelCost
    Bidi.ternary27HeadTravelCost
    Storage.programBinaryCellCost
    Storage.programTernary27CellCost
    Storage.dataBinaryCellCost
    Storage.dataTernary27CellCost
    Bidi.sameTrajectoryMeansSameTransitionConsumer
    Bidi.sameTrajectoryMeansSameHeadTravelConsumer
    Storage.programBinaryCellCostIs126
    Storage.programTernary27CellCostIs42
    Storage.dataBinaryCellCostIs117
    Storage.dataTernary27CellCostIs39

record ExecutionCostComparisonBoundary : Set where
  constructor executionCostComparisonBoundary
  field
    sameExecutionPathForBothRepresentations : Bool
    sameTransitionCost : Bool
    sameHeadTravelCost : Bool
    sameLogicalRepresentationCellCost : Bool
    logicalCellCountDeterminesSiliconArea : Bool
    logicalCellCountDeterminesEnergy : Bool
    logicalCellCountDeterminesLatency : Bool

canonicalExecutionCostComparisonBoundary : ExecutionCostComparisonBoundary
canonicalExecutionCostComparisonBoundary =
  executionCostComparisonBoundary true true true false false false false

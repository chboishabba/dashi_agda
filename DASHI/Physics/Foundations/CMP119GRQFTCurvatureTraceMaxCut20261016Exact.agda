{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GRQFTCurvatureTraceMaxCut20261016Exact where

------------------------------------------------------------------------
-- REVISED GRQFT / CMP119 MAX-CUT AFTER THE R144 CURVATURE TRACE NO-GO
--
-- The previous frontier charged five leaves.  Three of those were presentation
-- artifacts for the partition-derived stress route:
--
--   * ten independent classical DS[h] callbacks are compiled from CurvatureSix;
--   * the R144 partition observable is definitionally O = 1;
--   * its insertion variation is definitionally DO[h] = 0.
--
-- The classical CurvatureSix sector is also exactly traceless.  Therefore the
-- remaining nonlinear same-object task must NOT identify the whole generated
-- action with that classical sector if a nonzero/negative trace is required.
-- The physically honest terminal split is:
--
--   1. identify the selected CLASSICAL finite D1 sector with CurvatureSix;
--   2. identify the separate NONCLASSICAL trace-producing action sector;
--   3. evaluate/transport the literal finite-measure readouts.
--
-- An inserted-observable connected-numerator calculation may separately choose
-- O and DO[h], but those are not debts of the R144 partition-stress route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Foundations.CMP119GRQFTD1MaxCutExact as Old
import DASHI.Physics.Foundations.CMP119CurvatureWilsonSelectedInsertionCompilerExact as CurvatureCompiler
import DASHI.Physics.Foundations.CMP119R144CurvatureTraceSectorNoGoExact as TraceNoGo
import DASHI.Physics.Foundations.CMP119R144PartitionInsertionTrivialityExact as Partition

------------------------------------------------------------------------
-- Minimal revised leaf set.
------------------------------------------------------------------------

data GRQFTCurvatureTraceLeaf : Set where
  identifySelectedClassicalCurvatureSector : GRQFTCurvatureTraceLeaf
  identifyNonclassicalTraceActionSector : GRQFTCurvatureTraceLeaf
  evaluateLiteralFiniteMeasureReadouts : GRQFTCurvatureTraceLeaf

canonicalGRQFTCurvatureTraceLeaves : List GRQFTCurvatureTraceLeaf
canonicalGRQFTCurvatureTraceLeaves =
  identifySelectedClassicalCurvatureSector
  ∷ identifyNonclassicalTraceActionSector
  ∷ evaluateLiteralFiniteMeasureReadouts
  ∷ []

------------------------------------------------------------------------
-- Retired presentation debts.
------------------------------------------------------------------------

tenIndependentClassicalDSCallbacksStillOpen : Bool
tenIndependentClassicalDSCallbacksStillOpen =
  CurvatureCompiler.tenIndependentActionVariationCallbacksRequired

partitionStressOandDOStillOpen : Bool
partitionStressOandDOStillOpen = false

oldFiveLeafGRQFTRoadmapStillCurrent : Bool
oldFiveLeafGRQFTRoadmapStillCurrent = false

------------------------------------------------------------------------
-- Physical boundary after the trace no-go.
------------------------------------------------------------------------

wholeGeneratedActionMayBeClassicalCurvature : Bool
wholeGeneratedActionMayBeClassicalCurvature =
  TraceNoGo.fullGeneratedActionMayBeClassicalCurvatureWithoutTracePayment

selectedClassicalCurvatureSameObjectSectorStillOpen : Bool
selectedClassicalCurvatureSameObjectSectorStillOpen = true

nonclassicalTraceActionSectorStillOpen : Bool
nonclassicalTraceActionSectorStillOpen =
  TraceNoGo.independentQuantumTraceContributionStillPhysicalPayment

literalFiniteMeasureReadoutEvaluationStillOpen : Bool
literalFiniteMeasureReadoutEvaluationStillOpen =
  Old.tenLiteralGibbsABDZEvaluationsStillOpen

insertedObservableConnectedNumeratorIsSeparateConsumer : Bool
insertedObservableConnectedNumeratorIsSeparateConsumer =
  Partition.insertedObservableConnectedNumeratorRouteStillSeparate

------------------------------------------------------------------------
-- Machine-visible status receipts.
------------------------------------------------------------------------

tenIndependentClassicalDSCallbacksStillOpenIsFalse :
  tenIndependentClassicalDSCallbacksStillOpen ≡ false
tenIndependentClassicalDSCallbacksStillOpenIsFalse = refl

partitionStressOandDOStillOpenIsFalse :
  partitionStressOandDOStillOpen ≡ false
partitionStressOandDOStillOpenIsFalse = refl

wholeGeneratedActionMayBeClassicalCurvatureIsFalse :
  wholeGeneratedActionMayBeClassicalCurvature ≡ false
wholeGeneratedActionMayBeClassicalCurvatureIsFalse = refl

nonclassicalTraceActionSectorStillOpenIsTrue :
  nonclassicalTraceActionSectorStillOpen ≡ true
nonclassicalTraceActionSectorStillOpenIsTrue = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

-- The classical same-object weld still matters: once supplied, it pays all ten
-- classical DS[h] slots simultaneously.  The no-go says only that this weld is
-- a sector identification, not an identification of the entire quantum/
-- generated action when a nonzero trace is demanded.
classicalCurvatureWeldPaysTenSlotsButNotQuantumTrace : Bool
classicalCurvatureWeldPaysTenSlotsButNotQuantumTrace = true

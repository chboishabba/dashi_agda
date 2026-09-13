module DASHI.ComputerScience.RSA260BidiDynamicRankRepairHeldoutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiStructuralFibrePortfolioHeldoutExact as Static
import DASHI.ComputerScience.RSA260BidiKrylovReachableRankExact as Dynamic

------------------------------------------------------------------------
-- HELD-OUT DYNAMIC-RANK REPAIR
--
-- Keep the existing 12 static structural fibres, then add exactly one repair
-- fibre:
--
--   r_80 = rank [ BY , B^2 Y , ... , B^80 Y ]
--
-- under the same width-8 / CADO-shaped 4x4 synthetic consumer used by the
-- prior experiments.
--
-- Same training portfolio: 18 carriers.
-- Same held-out perturbation seed: 271011, six coverage levels.
-- Same ridge label lambda: 0.3.
--
-- Result:
--   static 12-fibre MAE  = 2.328871159849383
--   repaired 13-fibre MAE = 0.5012029340482554
--
-- The surviving 256-row counterexample is materially repaired but not erased:
--   observed d = 64
--   static prediction ~= 56.8277, error ~= 7.1723
--   dynamic prediction ~= 62.3711, error ~= 1.6289.
--
-- Therefore reachable Krylov rank is admitted as a useful local repair fibre,
-- not as a complete recurrence formula or production RSA-260 measurement.
------------------------------------------------------------------------

staticBoundary : Static.StructuralPortfolioInterpretationBoundary
staticBoundary = Static.canonicalStructuralPortfolioInterpretationBoundary

dynamicBoundary : Dynamic.DynamicRankInterpretationBoundary
dynamicBoundary = Dynamic.canonicalDynamicRankInterpretationBoundary

record DynamicRankRepairRuntimeSource : Set where
  constructor dynamic-rank-repair-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    exactCommittedBlobExecuted : Bool
open DynamicRankRepairRuntimeSource public

currentDynamicRankRepairRuntimeSource : DynamicRankRepairRuntimeSource
currentDynamicRankRepairRuntimeSource = dynamic-rank-repair-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_dynamic_rank_repair_heldout.py"
  "4cd6a9120fa11da7acf09e92399cb242c66a93a8"
  "de5ada889c4d06c91b6c5c05f2f966f14d359e51"
  true

record DynamicRankRepairReceipt : Set where
  constructor dynamic-rank-repair-receipt
  field
    staticFibreCount : Nat
    repairedFibreCount : Nat
    trainingPoints : Nat
    heldoutCoverageLevels : Nat
    heldoutSeed : Nat
    dynamicHorizon : Nat
    dynamicBlockWidth : Nat
    ridgeLambdaLabel : String
    staticMAELabel : String
    repairedMAELabel : String
    maeImprovementLabel : String
    targetTouchedRows : Nat
    targetObservedDegree : Nat
    targetStaticPredictionLabel : String
    targetStaticErrorLabel : String
    targetDynamicRank : Nat
    targetDynamicPredictionLabel : String
    targetDynamicErrorLabel : String
open DynamicRankRepairReceipt public

currentDynamicRankRepairReceipt : DynamicRankRepairReceipt
currentDynamicRankRepairReceipt = dynamic-rank-repair-receipt
  12 13
  18 6 271011
  80 8
  "0.3"
  "2.328871159849383"
  "0.5012029340482554"
  "1.8276682258011276"
  256 64
  "56.82772330817217"
  "7.1722766918278325"
  498
  "62.371111138893305"
  "1.6288888611066952"

record DynamicRankRepairBoundary : Set where
  constructor dynamic-rank-repair-boundary
  field
    reachableRankAddedAsOnlyNewRepairFibre : Bool
    sameTrainHeldoutSplitPreserved : Bool
    repairedModelReducesHeldoutMAE : Bool
    repairedModelReducesLargestStaticResidual : Bool
    repairedModelEliminatesLargestResidual : Bool
    reachableRankIsCompleteRecurrenceFormula : Bool
    syntheticRepairIsCausalProof : Bool
    syntheticRepairIsProductionMeasurement : Bool
    repairShouldBeCrossValidatedAcrossPreparationProjectionFibres : Bool
open DynamicRankRepairBoundary public

canonicalDynamicRankRepairBoundary : DynamicRankRepairBoundary
canonicalDynamicRankRepairBoundary = dynamic-rank-repair-boundary
  true true true true false false false false true

data DynamicRankRepairResidual : Set where
  crossValidateRepairAcrossPreparationFibres : DynamicRankRepairResidual
  crossValidateRepairAcrossProjectionFibres : DynamicRankRepairResidual
  inspectSurviving256RowResidual : DynamicRankRepairResidual
  measureRepairOnSameObjectProductionASequence : DynamicRankRepairResidual

firstDynamicRankRepairResidual : DynamicRankRepairResidual
firstDynamicRankRepairResidual = crossValidateRepairAcrossPreparationFibres

data LowerMAEImpliesExactFormula : Set where
data ResidualReductionImpliesResidualElimination : Set where
data SyntheticRepairImpliesProductionMeasurement : Set where

lowerMAEDoesNotCreateExactFormula : LowerMAEImpliesExactFormula → ⊥
lowerMAEDoesNotCreateExactFormula ()

residualReductionDoesNotCreateElimination : ResidualReductionImpliesResidualElimination → ⊥
residualReductionDoesNotCreateElimination ()

syntheticRepairDoesNotCreateProductionMeasurement : SyntheticRepairImpliesProductionMeasurement → ⊥
syntheticRepairDoesNotCreateProductionMeasurement ()

module DASHI.ComputerScience.QwenputerRv32LayerScheduleSourceExact where

-- Recoverable source:
-- Divyansh Agrawal, Qwenputer (2026), v0.1.0.
-- https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md
-- Source P2 11-layer table, not a verified emitted tensor schema.
-- The stage catalogue and sums are a DASHI formalisation of that report.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)

data Layer : Set where
  L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 : Layer

layerIndex : Layer → Nat
layerIndex L1 = 1
layerIndex L2 = 2
layerIndex L3 = 3
layerIndex L4 = 4
layerIndex L5 = 5
layerIndex L6 = 6
layerIndex L7 = 7
layerIndex L8 = 8
layerIndex L9 = 9
layerIndex L10 = 10
layerIndex L11 = 11

data FunctionRole : Set where
  controlBookkeeping : FunctionRole
  instructionAddress : FunctionRole
  programROM : FunctionRole
  registersAndALU : FunctionRole
  digitFileAndArithmetic : FunctionRole
  mainRAMAndArithmetic : FunctionRole
  dromAndDivision : FunctionRole
  quotientComparison : FunctionRole
  outputOwnership : FunctionRole

role : Layer → FunctionRole
role L1 = controlBookkeeping
role L2 = instructionAddress
role L3 = programROM
role L4 = programROM
role L5 = registersAndALU
role L6 = digitFileAndArithmetic
role L7 = mainRAMAndArithmetic
role L8 = mainRAMAndArithmetic
role L9 = dromAndDivision
role L10 = quotientComparison
role L11 = outputOwnership

-- Reported number of key heads for each P2 layer.
-- L3/L4 and L7/L8 split totals are given directly in the source table.
keyHeads : Layer → Nat
keyHeads L1 = 4
keyHeads L2 = 0
keyHeads L3 = 16
keyHeads L4 = 16
keyHeads L5 = 7
keyHeads L6 = 8
keyHeads L7 = 16
keyHeads L8 = 16
keyHeads L9 = 16
keyHeads L10 = 0
keyHeads L11 = 0

reportedKeyHeadTotal : Nat
reportedKeyHeadTotal =
  keyHeads L1 + keyHeads L2 + keyHeads L3 + keyHeads L4
  + keyHeads L5 + keyHeads L6 + keyHeads L7 + keyHeads L8
  + keyHeads L9 + keyHeads L10 + keyHeads L11

keyHeadSumMatchesAuthor : reportedKeyHeadTotal ≡ 99
keyHeadSumMatchesAuthor = refl

-- The original table groups the L3-L4 4,138 decode units.
-- Do NOT fabricate a per-layer allocation for those 4,138 units.
reportedMLPUnits : Layer → Maybe Nat
reportedMLPUnits L1 = just 306
reportedMLPUnits L2 = just 1376
reportedMLPUnits L3 = nothing
reportedMLPUnits L4 = nothing
reportedMLPUnits L5 = just 7876
reportedMLPUnits L6 = just 6621
reportedMLPUnits L7 = just 3751
reportedMLPUnits L8 = just 7923
reportedMLPUnits L9 = just 8149
reportedMLPUnits L10 = just 1074
reportedMLPUnits L11 = just 798

reportedL3L4CombinedDecodeUnits : Nat
reportedL3L4CombinedDecodeUnits = 4138

record SourcePipelineBudget : Set where
  constructor sourcePipelineBudget
  field
    compiledLayers : Nat
    qwenBaseLayers : Nat
    programROMBytes : Nat
    dataROMBytes : Nat
    ramBytes : Nat
    mlpUnitsReported : Nat
    nonzeroWeightsReported : Nat
open SourcePipelineBudget public

-- P2 source reports 256 KiB ROM, 128 KiB DROM, 32 KiB RAM,
-- 42,012 MLP units and 1,040,595 nonzero weights.
p2ReportedBudget : SourcePipelineBudget
p2ReportedBudget =
  sourcePipelineBudget 11 32 262144 131072 32768 42012 1040595

sourceMemoryBudgetIsReported :
  ramBytes p2ReportedBudget ≡ 32768
sourceMemoryBudgetIsReported = refl

p2MLPReportedArithmeticSum :
  306 + 1376 + reportedL3L4CombinedDecodeUnits
  + 7876 + 6621 + 3751 + 7923 + 8149 + 1074 + 798
  ≡ mlpUnitsReported p2ReportedBudget
p2MLPReportedArithmeticSum = refl

-- Do not infer the P3 3968 hidden width from the P2 standalone hidden 2816.
-- P2 and P3 use distinct compiler/build configurations.
data LayerScheduleStatus : Set where
  sourcedFiniteLayout : LayerScheduleStatus
  sameObjectLayerWeightsNotVerified : LayerScheduleStatus

currentLayerScheduleStatus : LayerScheduleStatus
currentLayerScheduleStatus = sourcedFiniteLayout

actualTensorWeldStatus : LayerScheduleStatus
actualTensorWeldStatus = sameObjectLayerWeightsNotVerified

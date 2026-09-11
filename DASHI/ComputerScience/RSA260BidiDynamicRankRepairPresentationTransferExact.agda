module DASHI.ComputerScience.RSA260BidiDynamicRankRepairPresentationTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiDynamicRankRepairHeldoutExact as Repair
import DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact as Coverage

------------------------------------------------------------------------
-- DYNAMIC-RANK REPAIR TRANSFER ACROSS PRESENTATION FIBRES
--
-- Train the existing 12-static / 13-fibre (+r80) models on the canonical
-- training portfolio, then validate against an already-paid independent
-- presentation-cross surface:
--
--   grid4x4 / projection 0
--   grid4x4 / projection 1
--   grid8x4 / projection 0.
--
-- The generator-degree labels on that surface were produced by the earlier
-- exact-byte defect-coverage preparation/projection experiment.  This runtime
-- recomputes static fibres and r80, but does not claim those frozen degree
-- labels as newly executed observations.
--
-- Static -> dynamic MAE:
--   grid4x4/proj0 : 3.5729 -> 0.8908
--   grid4x4/proj1 : 3.1729 -> 0.7038
--   grid8x4/proj0 : 3.1729 -> 0.4505
--
-- The 256-row residual is reduced in all three tested presentations.
------------------------------------------------------------------------

repairBoundary : Repair.DynamicRankRepairBoundary
repairBoundary = Repair.canonicalDynamicRankRepairBoundary

coverageBoundary : Coverage.DefectCoverageInterpretationBoundary
coverageBoundary = Coverage.canonicalDefectCoverageInterpretationBoundary

record PresentationTransferRuntimeSource : Set where
  constructor presentation-transfer-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    dependencyPath : String
    dependencyGitBlob : String
    exactTopLevelBlobExecuted : Bool
    exactDependencyBlobExecuted : Bool
open PresentationTransferRuntimeSource public

currentPresentationTransferRuntimeSource : PresentationTransferRuntimeSource
currentPresentationTransferRuntimeSource = presentation-transfer-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_dynamic_rank_repair_presentation_transfer.py"
  "dbf3155623946f9516f3f169ec59bf2f348f488f"
  "88ea02c78b6fd9e6c78e106d39dbab08a47c81af"
  "rsa260_bidi_dynamic_rank_repair_heldout.py"
  "de5ada889c4d06c91b6c5c05f2f966f14d359e51"
  true true

record PresentationTransferReceipt : Set where
  constructor presentation-transfer-receipt
  field
    testedPresentations : Nat
    validationCoverageLevelsPerPresentation : Nat
    grid4x4Projection0StaticMAE : String
    grid4x4Projection0DynamicMAE : String
    grid4x4Projection1StaticMAE : String
    grid4x4Projection1DynamicMAE : String
    grid8x4Projection0StaticMAE : String
    grid8x4Projection0DynamicMAE : String
    allPresentationsReduceMAE : Bool
    allPresentationsReduce256Residual : Bool
open PresentationTransferReceipt public

currentPresentationTransferReceipt : PresentationTransferReceipt
currentPresentationTransferReceipt = presentation-transfer-receipt
  3 5
  "3.5729129565006494" "0.890753845737202"
  "3.1729129565006495" "0.7037637393446807"
  "3.1729129565006495" "0.45045227549693934"
  true true

record PresentationTransferBoundary : Set where
  constructor presentation-transfer-boundary
  field
    dynamicRepairTransfersAcrossTestedPreparationFibres : Bool
    dynamicRepairTransfersAcrossTestedProjectionFibres : Bool
    frozenDegreeLabelsAreNewExecutionByTransferRuntime : Bool
    transferEstablishesExactDegreeFormula : Bool
    transferEstablishesProductionRSA260Behaviour : Bool
    survivingResidualStillRequiresInspection : Bool
open PresentationTransferBoundary public

canonicalPresentationTransferBoundary : PresentationTransferBoundary
canonicalPresentationTransferBoundary = presentation-transfer-boundary
  true true false false false true

data PresentationTransferResidual : Set where
  inspectSurvivingDynamicResidual : PresentationTransferResidual
  extendTransferToAdditionalPreparationFamilies : PresentationTransferResidual
  acquireSameObjectProductionASequence : PresentationTransferResidual

firstPresentationTransferResidual : PresentationTransferResidual
firstPresentationTransferResidual = inspectSurvivingDynamicResidual

data TransferImprovementImpliesExactFormula : Set where
data FrozenLabelsImplyNewExecution : Set where
data SyntheticTransferImpliesProductionBehaviour : Set where

transferImprovementDoesNotCreateExactFormula : TransferImprovementImpliesExactFormula → ⊥
transferImprovementDoesNotCreateExactFormula ()

frozenLabelsDoNotCreateNewExecution : FrozenLabelsImplyNewExecution → ⊥
frozenLabelsDoNotCreateNewExecution ()

syntheticTransferDoesNotCreateProductionBehaviour : SyntheticTransferImpliesProductionBehaviour → ⊥
syntheticTransferDoesNotCreateProductionBehaviour ()

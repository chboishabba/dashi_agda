module DASHI.Physics.Closure.ClaySprintFortyThreeNS3DTruthBridgeRepairReceipt where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFortyTwoNSDiagnosticHarnessReceipt
  as Sprint42

------------------------------------------------------------------------
-- Sprint 43 NS 3D truth bridge repair.
--
-- This receipt records the repaired executable evidence lane: the harness now
-- reads the 3D truth generator shell convention, uses stored velocity
-- snapshots when present, reports K_star from meta_json, and emits progress
-- ETA for long 3D runs.  It remains diagnostic evidence only.

data ClaySprintFortyThreeNS3DRepairStatus : Set where
  claySprintFortyThreeNS3DRepairRecorded_noPromotion :
    ClaySprintFortyThreeNS3DRepairStatus

data NS3DRepairClosedSurface : Set where
  integerRadiusShellConventionRecorded :
    NS3DRepairClosedSurface
  metaJsonKStarRecorded :
    NS3DRepairClosedSurface
  velocitySnapshotSourceRecorded :
    NS3DRepairClosedSurface
  progressETARecorded :
    NS3DRepairClosedSurface
  n32TruthRunRecorded :
    NS3DRepairClosedSurface
  n64TwoSeedTruthRunsRecorded :
    NS3DRepairClosedSurface

canonicalNS3DRepairClosedSurfaces :
  List NS3DRepairClosedSurface
canonicalNS3DRepairClosedSurfaces =
  integerRadiusShellConventionRecorded
  ∷ metaJsonKStarRecorded
  ∷ velocitySnapshotSourceRecorded
  ∷ progressETARecorded
  ∷ n32TruthRunRecorded
  ∷ n64TwoSeedTruthRunsRecorded
  ∷ []

data NS3DRepairOpenGate : Set where
  gatePositiveResidueClassifier :
    NS3DRepairOpenGate
  gateAdjustedBridgeRatioAvailable :
    NS3DRepairOpenGate
  gateBudgetBeatsHalfDerivative :
    NS3DRepairOpenGate
  gateActualTernaryLineage :
    NS3DRepairOpenGate
  gateStretchAbsorptionProof :
    NS3DRepairOpenGate
  gateNoBlowupProof :
    NS3DRepairOpenGate

canonicalNS3DRepairOpenGates :
  List NS3DRepairOpenGate
canonicalNS3DRepairOpenGates =
  gatePositiveResidueClassifier
  ∷ gateAdjustedBridgeRatioAvailable
  ∷ gateBudgetBeatsHalfDerivative
  ∷ gateActualTernaryLineage
  ∷ gateStretchAbsorptionProof
  ∷ gateNoBlowupProof
  ∷ []

data ClaySprintFortyThreeNS3DPromotion : Set where

sprintFortyThreeNS3DPromotionImpossibleHere :
  ClaySprintFortyThreeNS3DPromotion →
  ⊥
sprintFortyThreeNS3DPromotionImpossibleHere ()

closedSurfaceCount : Nat
closedSurfaceCount = 6

openGateCount : Nat
openGateCount = 6

shellRepairFormula : String
shellRepairFormula =
  "make_truth_3d shell projection is integer-radius; repaired harness records shell_convention=integer-radius and k_star_source=meta_json.k_star"

n32ResultSummary : String
n32ResultSummary =
  "repaired N32 seed0: K_star=7, high-shell support passes, sup_C_K approx 2.5866e11, inf budget approx -0.02572, no promotion"

n64ResultSummary : String
n64ResultSummary =
  "repaired N64 seeds 0 and 1: K_star=7, high-shell support passes, budgets remain below 1/2, no promotion"

bridgeBoundarySummary : String
bridgeBoundarySummary =
  "diagnostic bridge evidence does not prove Q_K <= C Rplus_K concentration_K^theta, actual ternary lineage, stretch absorption, or no finite-time blowup"

usesSprint42Harness :
  Sprint42.ClaySprintFortyTwoStatus →
  ClaySprintFortyThreeNS3DRepairStatus
usesSprint42Harness
  Sprint42.claySprintFortyTwoNSDiagnosticHarnessRecorded_noPromotion =
  claySprintFortyThreeNS3DRepairRecorded_noPromotion

closedSurfaceCountCheck : closedSurfaceCount ≡ 6
closedSurfaceCountCheck = refl

openGateCountCheck : openGateCount ≡ 6
openGateCountCheck = refl

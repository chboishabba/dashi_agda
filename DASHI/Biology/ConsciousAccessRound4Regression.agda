module DASHI.Biology.ConsciousAccessRound4Regression where

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Lift
import DASHI.Biology.TriadicCarryResidualExact as Carry
import DASHI.Biology.PadicCylinderLODReasoningField as LOD
import DASHI.Biology.HallHybridManifoldTreeCarrier as Hall
import DASHI.Biology.HybridPadicReasoningFieldBridgeExact as Hybrid
import DASHI.Biology.CausalHierarchicalChartResidualExact as Chart
import DASHI.Biology.FiniteCrystallisationModeSelectionExact as Modes
import DASHI.Biology.FiniteWaveShellGradientExact as Shell
import DASHI.Biology.FiniteSymmetryStabiliserExact as Symmetry
import DASHI.Biology.FinitePadicCollapseExact as Collapse
import DASHI.Biology.ResourceLimitedCrystallisationExact as Resource
import DASHI.Biology.ReasoningFieldRenderBridgeExact as Render
import DASHI.Biology.PadicCrystallisationResidueExact as PadicCrystal
import DASHI.Biology.CoupledWaveTriadicOrderExact as Coupled
import DASHI.Biology.QuasiperiodicInternalSpaceBoundaryExact as Quasi
import DASHI.Biology.ConsciousAccessRound4SourceAtlas as Sources
import DASHI.Biology.ConsciousAccessRound4FullBoundary as Full

------------------------------------------------------------------------
-- Focused cumulative regression surface.

round4BoundaryExists : Full.ConsciousAccessRound4Boundary
round4BoundaryExists = Full.canonicalConsciousAccessRound4Boundary

round4PromotionBoundaryExists : Full.Round4PromotionBoundary
round4PromotionBoundaryExists = Full.canonicalRound4PromotionBoundary

nineQuotientHasFiveNamedOrbitKinds :
  Lift.quotientNine (Lift.positiveTrit , Lift.negativeTrit)
  ≡
  Lift.oppositeSignOrbit
nineQuotientHasFiveNamedOrbitKinds = refl

triadicSoftLayerExactOnBasis :
  Carry.cyclicConvolution
    (Carry.basisMass Carry.residue1)
    (Carry.basisMass Carry.residue1)
  ≡
  Carry.basisMass Carry.residue2
triadicSoftLayerExactOnBasis = refl

lodParentMassRegression :
  LOD.totalMass LOD.canonicalCoarseField ≡ 9
lodParentMassRegression = refl

hybridCarrierCrossPollinationRegression :
  Hybrid.hybridVoxel3 Hall.habitualChartNeighbour
  ≡
  LOD.voxel3 0 0 1
hybridCarrierCrossPollinationRegression = refl

causalSelectionRegression :
  Chart.candidateObjective Chart.refinedCandidate ≡ 3
causalSelectionRegression = refl

modeCompetitionRegression :
  Modes.branchScore
    Modes.reflectionSymmetricQuarticRegime
    Modes.stripeBranch
  ≡
  1
  ×
  Modes.branchScore
    Modes.resonantTriadCoupledRegime
    Modes.hexagonalBranch
  ≡
  1
modeCompetitionRegression = refl , refl

waveShellRegression :
  Shell.shellPenalty Shell.zeroWaveNumber ≡ 1
  ×
  Shell.shellPenalty Shell.selectedWaveNumber ≡ 0
  ×
  Shell.shellPenalty Shell.highWaveNumber ≡ 9
waveShellRegression = refl , (refl , refl)

stabiliserRegression :
  Symmetry.stabiliserSize Symmetry.constantPattern ≡ 2
  ×
  Symmetry.stabiliserSize Symmetry.asymmetricPattern ≡ 1
stabiliserRegression = refl , refl

collapseRegression :
  Collapse.weightedThickness Collapse.unstructuredResidual ≡ 58
  ×
  Collapse.weightedThickness Collapse.collapsedResidual ≡ 7
collapseRegression = refl , refl

freezeOutRegression :
  Resource.mobility (Resource.resource Resource.afterFreezeOut) ≡ 0
  ×
  Resource.defectCount Resource.afterFreezeOut ≡ 1
freezeOutRegression = refl , refl

renderLossRegression :
  Render.cameraProject Render.voxelA ≡ Render.cameraProject Render.voxelB
renderLossRegression = refl

padicCrystallisationRegression :
  PadicCrystal.shiftOneMismatchCount PadicCrystal.coarseOrderedPattern ≡ 0
  ×
  PadicCrystal.shiftOneMismatchCount PadicCrystal.fineAlternatingPattern ≡ 4
padicCrystallisationRegression = refl , refl

coupledOrderRegression :
  Coupled.gibbsCodeLength
    (Coupled.jointObjective Coupled.alignedHexagonalCandidate)
  ≡
  7
coupledOrderRegression = refl

quasiperiodicProjectionRegression :
  Quasi.projectPhysical Quasi.superspacePointA
  ≡
  Quasi.projectPhysical Quasi.superspacePointB
quasiperiodicProjectionRegression = refl

round4SourceRegression : Sources.canonicalRound4SourceCount ≡ 8
round4SourceRegression = refl

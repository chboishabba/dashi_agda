module DASHI.Mathematics.CrossPollination.FrontierProductiveCompletionRound2GateExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Status gate for the second productive-completion layer.  It records the
-- generic finite constructions added after the first frontier root and keeps
-- them distinct from their infinite, interacting or continuum targets.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.LinearAlgebra.RationalThreeWayHodgeCoordinateUniquenessExact
import DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHodgeBasisExact
import DASHI.Mathematics.Complexity.GenericFiniteRunTableauExact
import DASHI.Moonshine.FiniteDifferentialVertexAlgebraExact
import DASHI.Moonshine.SquareZeroDifferentialVertexAlgebraBridgeExact
import DASHI.Moonshine.RankOneHeisenbergFockWindowExact
import DASHI.Physics.Constructive.FiniteReflectionPositivityExact
import DASHI.Physics.Constructive.FiniteProductClusteringDenominatorClearedExact
import DASHI.Physics.Constructive.FinitePolymerKPBudgetExact
import DASHI.Physics.YangMills.YangMillsFiniteConstructiveLadderExact

data Round2Lane : Set where
  hodgeDirectSumLane
  projectiveSpaceLane
  genericCookLevinLane
  genericDifferentialVertexLane
  heisenbergFockLane
  finiteOS2Lane
  finiteOS4Lane
  finiteKPLane
  finiteUniformGapLane

data Round2Stage : Set where
  exactFiniteConstruction
  proofBearingGenericConstruction
  interactingTheoryBoundary
  infiniteCompletionBoundary
  continuumBoundary

record Round2LaneStatus : Set where
  constructor round2LaneStatus
  field
    lane : Round2Lane
    completedStage : Round2Stage
    remainingStage : Round2Stage

open Round2LaneStatus public

hodgeDirectSumStatus : Round2LaneStatus
hodgeDirectSumStatus = round2LaneStatus
  hodgeDirectSumLane proofBearingGenericConstruction
  infiniteCompletionBoundary

projectiveSpaceStatus : Round2LaneStatus
projectiveSpaceStatus = round2LaneStatus
  projectiveSpaceLane exactFiniteConstruction
  infiniteCompletionBoundary

genericCookLevinStatus : Round2LaneStatus
genericCookLevinStatus = round2LaneStatus
  genericCookLevinLane proofBearingGenericConstruction
  infiniteCompletionBoundary

genericDifferentialVertexStatus : Round2LaneStatus
genericDifferentialVertexStatus = round2LaneStatus
  genericDifferentialVertexLane proofBearingGenericConstruction
  infiniteCompletionBoundary

heisenbergFockStatus : Round2LaneStatus
heisenbergFockStatus = round2LaneStatus
  heisenbergFockLane exactFiniteConstruction
  infiniteCompletionBoundary

finiteOS2Status : Round2LaneStatus
finiteOS2Status = round2LaneStatus
  finiteOS2Lane exactFiniteConstruction
  interactingTheoryBoundary

finiteOS4Status : Round2LaneStatus
finiteOS4Status = round2LaneStatus
  finiteOS4Lane exactFiniteConstruction
  interactingTheoryBoundary

finiteKPStatus : Round2LaneStatus
finiteKPStatus = round2LaneStatus
  finiteKPLane exactFiniteConstruction
  interactingTheoryBoundary

finiteUniformGapStatus : Round2LaneStatus
finiteUniformGapStatus = round2LaneStatus
  finiteUniformGapLane exactFiniteConstruction
  continuumBoundary

allRound2LocalStagesInhabited :
  completedStage hodgeDirectSumStatus ≡ proofBearingGenericConstruction
  × completedStage projectiveSpaceStatus ≡ exactFiniteConstruction
  × completedStage genericCookLevinStatus ≡ proofBearingGenericConstruction
  × completedStage genericDifferentialVertexStatus ≡ proofBearingGenericConstruction
  × completedStage heisenbergFockStatus ≡ exactFiniteConstruction
  × completedStage finiteOS2Status ≡ exactFiniteConstruction
  × completedStage finiteOS4Status ≡ exactFiniteConstruction
  × completedStage finiteKPStatus ≡ exactFiniteConstruction
  × completedStage finiteUniformGapStatus ≡ exactFiniteConstruction
allRound2LocalStagesInhabited =
  refl , refl , refl , refl , refl , refl , refl , refl , refl

finiteOSModelsRemainInteractingBoundaries :
  remainingStage finiteOS2Status ≡ interactingTheoryBoundary
  × remainingStage finiteOS4Status ≡ interactingTheoryBoundary
  × remainingStage finiteKPStatus ≡ interactingTheoryBoundary
finiteOSModelsRemainInteractingBoundaries = refl , refl , refl

finiteGapRemainsContinuumBoundary :
  remainingStage finiteUniformGapStatus ≡ continuumBoundary
finiteGapRemainsContinuumBoundary = refl

finiteConstructionIsNotContinuumClosure :
  exactFiniteConstruction ≡ continuumBoundary → ⊥
finiteConstructionIsNotContinuumClosure ()

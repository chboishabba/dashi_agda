module DASHI.Biology.Microbiology.BaldEyesalveLiveSetSchedulerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualConditionedExperimentPortfolioExact as Portfolio
import DASHI.Core.ExpectedFibreReductionCostExact as Reduction
import DASHI.Core.ActionFibreClosureStoppingExact as Stop
import DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact as Existing

------------------------------------------------------------------------
-- BALD'S EYESALVE: LIVE-FIBRE NEXT-EXPERIMENT SCHEDULER
------------------------------------------------------------------------

data MechanismWorld : Set where
  sulfurDominant : MechanismWorld
  recoveryBuffered : MechanismWorld
  quorumDominant : MechanismWorld
  matrixDominant : MechanismWorld
  mixedPositive : MechanismWorld

data Experiment : Set where
  sulfurSpeciation : Experiment
  thiolFunctionPanel : Experiment
  recoveryPanel : Experiment
  quorumPerturbation : Experiment
  matrixSpatialPanel : Experiment

data ResidualStage : Set where
  chemistryOpen : ResidualStage
  chemistryClosedThiolRecoveryLive : ResidualStage
  quorumCollision : ResidualStage
  matrixCollision : ResidualStage
  actionClosed : ResidualStage

record SchedulerRoute : Set where
  constructor schedulerRoute
  field
    stage : ResidualStage
    selected : Experiment
    liveCollisionReference : String
    whyNow : String
    whyNotRepeatUpstream : String
    authorityReference : String

open SchedulerRoute public

chemistryFirst : SchedulerRoute
chemistryFirst = schedulerRoute chemistryOpen sulfurSpeciation
  "sulfur-dominant versus non-sulfur worlds remain live"
  "BE-X1 directly splits the current upstream chemical-identity collision"
  "not applicable: chemistry is still unresolved"
  "analytical measurement admission required"

thiolRecoveryNext : SchedulerRoute
thiolRecoveryNext = schedulerRoute chemistryClosedThiolRecoveryLive recoveryPanel
  "thiol-damage-dominant and recovery-buffered worlds remain live after chemistry closure"
  "measure effective BSH/BrxAB/YpdA/MerA recovery and restoration, not merely marker presence"
  "repeating sulfur speciation is stale if it no longer separates the live thiol/recovery collision"
  "recovery measurement admission required; no perturbation authority inferred"

quorumNext : SchedulerRoute
quorumNext = schedulerRoute quorumCollision quorumPerturbation
  "regulatory association and causal quorum mediation remain colliding"
  "matched perturbation/rescue is the declared discriminator"
  "additional chemistry alone does not split this regulatory causal collision"
  "perturbation authority is independent of measurement authority"

matrixNext : SchedulerRoute
matrixNext = schedulerRoute matrixCollision matrixSpatialPanel
  "intracellular-dominant and spatial/matrix-dominant explanations remain live"
  "spatial exposure/matrix measurement discriminates structured-biofilm mechanisms"
  "bulk concentration repetition need not resolve spatial exposure"
  "spatial assay calibration/admission required"

record BaldEyesalveLiveSetSchedulerBoundary : Set where
  constructor baldEyesalveLiveSetSchedulerBoundary
  field
    fixedExperimentOrderAlwaysOptimal : Bool
    fixedExperimentOrderAlwaysOptimalIsFalse : fixedExperimentOrderAlwaysOptimal ≡ false
    resolvedChemistryMustBeRepeatedBeforeEveryDownstreamProbe : Bool
    resolvedChemistryMustBeRepeatedBeforeEveryDownstreamProbeIsFalse : resolvedChemistryMustBeRepeatedBeforeEveryDownstreamProbe ≡ false
    currentLiveCollisionShouldDetermineNextProbe : Bool
    currentLiveCollisionShouldDetermineNextProbeIsTrue : currentLiveCollisionShouldDetermineNextProbe ≡ true
    sameEndpointConsumerMayStopBeforeUniqueMechanism : Bool
    sameEndpointConsumerMayStopBeforeUniqueMechanismIsTrue : sameEndpointConsumerMayStopBeforeUniqueMechanism ≡ true

canonicalBaldEyesalveLiveSetSchedulerBoundary : BaldEyesalveLiveSetSchedulerBoundary
canonicalBaldEyesalveLiveSetSchedulerBoundary =
  baldEyesalveLiveSetSchedulerBoundary false refl false refl true refl true refl

existingPortfolioBoundary : Portfolio.ResidualConditionedPortfolioBoundary
existingPortfolioBoundary = Portfolio.canonicalResidualConditionedPortfolioBoundary

existingReductionBoundary : Reduction.ExpectedFibreReductionCostBoundary
existingReductionBoundary = Reduction.canonicalExpectedFibreReductionCostBoundary

existingStoppingBoundary : Stop.ActionFibreClosureBoundary
existingStoppingBoundary = Stop.canonicalActionFibreClosureBoundary

existingExperimentSelection : Existing.TK.ExperimentSelection
existingExperimentSelection = Existing.canonicalMechanismExperimentSelection

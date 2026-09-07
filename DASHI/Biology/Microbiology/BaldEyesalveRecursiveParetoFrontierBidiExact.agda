module DASHI.Biology.Microbiology.BaldEyesalveRecursiveParetoFrontierBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact as Experiments
import DASHI.Biology.Microbiology.BaldEyesalveLiveSetSchedulerBidiExact as Live
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive

------------------------------------------------------------------------
-- BALD'S EYESALVE RECURSIVE PARETO FRONTIER
--
-- Existing X1/X2/X2F/X3/X4 candidates are retained.  The recursive view says
-- only that a residual may refine one mechanism lane into a richer coordinate
-- family; it does not require all downstream chemistry, thiolome, function,
-- recovery, quorum and matrix coordinates to be materialised simultaneously.
------------------------------------------------------------------------

data MechanismFrontierLane : Set where
  chemistryLane : MechanismFrontierLane
  thiolLane : MechanismFrontierLane
  functionCellStateLane : MechanismFrontierLane
  recoveryLane : MechanismFrontierLane
  quorumLane : MechanismFrontierLane
  matrixTransportLane : MechanismFrontierLane
  mediationLane : MechanismFrontierLane


laneReference : MechanismFrontierLane → String
laneReference chemistryLane = "fresh-to-day-9 sulfur trajectory"
laneReference thiolLane = "target-preparation S-thioallylation / low-MW thiol state"
laneReference functionCellStateLane = "protein function plus coupled cell state"
laneReference recoveryLane = "BSH/BrxAB/YpdA/MerA recovery capacity"
laneReference quorumLane = "organism-appropriate quorum/virulence output"
laneReference matrixTransportLane = "biofilm matrix / penetration / spatial exposure"
laneReference mediationLane = "branch-selective perturbation/rescue mediation"

record LaneRefinement : Set where
  constructor laneRefinement
  field
    liveLane : MechanismFrontierLane
    selectedExperimentReference : String
    residualReference : String
    openedCoordinateReference : String
    samePreparationRequired : Bool
    sameOrganismRequired : Bool
    protocolReceiptRequired : Bool

open LaneRefinement public

chemistryRefinement : LaneRefinement
chemistryRefinement = laneRefinement
  chemistryLane
  "BE-X1 time-resolved sulfur speciation fresh-to-day-9"
  "chemical trajectory unresolved"
  "time x sulfur-species x target-preparation concentration"
  true true true

thiolRecoveryRefinement : LaneRefinement
thiolRecoveryRefinement = laneRefinement
  recoveryLane
  "BE-X2 plus BE-X2F matched thiol/recovery/function panel"
  "thiol damage and effective recovery remain collided"
  "damage occupancy x recovery flux x functional restoration"
  true true true

quorumMediationRefinement : LaneRefinement
quorumMediationRefinement = laneRefinement
  mediationLane
  "BE-X3 association followed by BE-X4 perturbation/rescue when admitted"
  "quorum association versus causal mediation collision"
  "reporter x viability x rescue x biofilm phenotype"
  true true true

record BaldEyesalveRecursiveParetoBoundary : Set where
  constructor baldEyesalveRecursiveParetoBoundary
  field
    allMechanismCoordinatesMustBeMeasuredAtOnce : Bool
    allMechanismCoordinatesMustBeMeasuredAtOnceIsFalse :
      allMechanismCoordinatesMustBeMeasuredAtOnce ≡ false
    currentResidualMaySelectMechanismSpecificRefinement : Bool
    currentResidualMaySelectMechanismSpecificRefinementIsTrue :
      currentResidualMaySelectMechanismSpecificRefinement ≡ true
    protocolReceiptStillRequiredAfterParetoSelection : Bool
    protocolReceiptStillRequiredAfterParetoSelectionIsTrue :
      protocolReceiptStillRequiredAfterParetoSelection ≡ true
    mixedMechanismIsFallbackForUnresolvedFrontier : Bool
    mixedMechanismIsFallbackForUnresolvedFrontierIsFalse :
      mixedMechanismIsFallbackForUnresolvedFrontier ≡ false

canonicalBaldEyesalveRecursiveParetoBoundary : BaldEyesalveRecursiveParetoBoundary
canonicalBaldEyesalveRecursiveParetoBoundary =
  baldEyesalveRecursiveParetoBoundary false refl true refl true refl false refl

existingExperimentOrderingBoundary : Experiments.ExperimentOrderingBoundary
existingExperimentOrderingBoundary = Experiments.canonicalExperimentOrderingBoundary

existingRecursiveBoundary : Recursive.RecursiveParetoFrontierBoundary
existingRecursiveBoundary = Recursive.canonicalRecursiveParetoFrontierBoundary

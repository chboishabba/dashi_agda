module DASHI.Biology.Microbiology.BaldEyesalvePerturbationDiscriminatorBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ResidualActionInterventionDiscriminatorExact as Intervene
import DASHI.Biology.Microbiology.BaldEyesalveMechanismDiscriminationBidiExact as Disc

------------------------------------------------------------------------
-- BALD'S EYESALVE BRANCH-SELECTIVE PERTURBATION ATLAS
--
-- These are high-level experiment-design obligations only.  They do not encode
-- wet-lab procedures or authorise execution.  Each candidate names the
-- mechanistic collision it is intended to discriminate and the matched readout
-- needed afterwards.
------------------------------------------------------------------------

data PerturbationLane : Set where
  sulfurReactivityPerturbation
  thiolCompetitionPerturbation
  recoveryCapacityPerturbation
  quorumSignalRescuePerturbation
  matrixTransportPerturbation
  : PerturbationLane

record BranchSelectivePerturbation : Set where
  constructor branchSelectivePerturbation
  field
    lane : PerturbationLane
    requestedAction : Action.ResidualActionKind
    targetCollision : String
    controlledChange : String
    matchedReadout : String
    expectedDiscriminator : String
    sameObjectRequirement : String
    executionAuthorityRequirement : String

open BranchSelectivePerturbation public

sulfurReactivityCandidate : BranchSelectivePerturbation
sulfurReactivityCandidate = branchSelectivePerturbation
  sulfurReactivityPerturbation Action.perturb
  "reactive-sulfur-dominant versus non-sulfur/matrix-regulatory explanation"
  "selectively alter reactive-sulfur availability while keeping the declared preparation context otherwise matched"
  "chemical profile + thiolome + protein function + phenotype"
  "if the thiol/function/phenotype signature tracks the sulfur change, the reactive-sulfur lane gains causal support"
  "same preparation family, organism, exposure geometry and matched time window"
  "independent laboratory/physical promotion receipt"

thiolCompetitionCandidate : BranchSelectivePerturbation
thiolCompetitionCandidate = branchSelectivePerturbation
  thiolCompetitionPerturbation Action.perturb
  "thiol-reactivity mediation versus parallel regulatory/transport explanation"
  "introduce a declared thiol-reactivity control or competing-thiol condition"
  "target modification + function + viability/biofilm phenotype"
  "selective attenuation of thiol modification with corresponding phenotype attenuation supports mediation"
  "same target system and matched exposure controls"
  "independent chemical/laboratory safety and perturbation admission"

recoveryCapacityCandidate : BranchSelectivePerturbation
recoveryCapacityCandidate = branchSelectivePerturbation
  recoveryCapacityPerturbation Action.perturb
  "damage-dominant versus recovery-buffered explanation"
  "compare declared states differing in thiol-homeostasis/recovery capacity"
  "damage occupancy + recovery flux + function + phenotype"
  "divergence in phenotype at similar initial damage but different recovery supports the buffering lane"
  "same exposure chemistry and observation window"
  "genetic/biological perturbation authority remains independently required"

quorumRescueCandidate : BranchSelectivePerturbation
quorumRescueCandidate = branchSelectivePerturbation
  quorumSignalRescuePerturbation Action.perturb
  "quorum/regulatory mediation versus direct killing or matrix explanation"
  "apply an organism-appropriate signal/regulatory rescue or orthogonal pathway perturbation"
  "QS/virulence reporter + viability + biofilm phenotype"
  "restoring regulatory output without restoring phenotype weakens quorum mediation; matched phenotype rescue strengthens it"
  "same organism, exposure and viability controls"
  "independent experimental and biosafety admission"

matrixTransportCandidate : BranchSelectivePerturbation
matrixTransportCandidate = branchSelectivePerturbation
  matrixTransportPerturbation Action.perturb
  "matrix/penetration mediation versus intracellular mechanism"
  "alter declared matrix/transport context while holding bulk chemical exposure matched"
  "spatial exposure + matrix state + structured/planktonic phenotype"
  "phenotype tracking spatial exposure/matrix change beyond bulk concentration supports this lane"
  "same chemical batch and matched bulk exposure"
  "independent physical/experimental admission"

record BaldEyesalvePerturbationBoundary : Set where
  constructor baldEyesalvePerturbationBoundary
  field
    proposedPerturbationIsEstablishedMechanism : Bool
    proposedPerturbationIsEstablishedMechanismIsFalse :
      proposedPerturbationIsEstablishedMechanism ≡ false
    perturbationWithoutMatchedReadoutDiscriminatesModels : Bool
    perturbationWithoutMatchedReadoutDiscriminatesModelsIsFalse :
      perturbationWithoutMatchedReadoutDiscriminatesModels ≡ false
    branchSelectivePerturbationCanSeparateMechanismCollisions : Bool
    branchSelectivePerturbationCanSeparateMechanismCollisionsIsTrue :
      branchSelectivePerturbationCanSeparateMechanismCollisions ≡ true
    sameObjectControlsAreRequiredForCausalPromotion : Bool
    sameObjectControlsAreRequiredForCausalPromotionIsTrue :
      sameObjectControlsAreRequiredForCausalPromotion ≡ true
    experimentDesignDoesNotCreateExecutionAuthority : Bool
    experimentDesignDoesNotCreateExecutionAuthorityIsTrue :
      experimentDesignDoesNotCreateExecutionAuthority ≡ true

canonicalBaldEyesalvePerturbationBoundary : BaldEyesalvePerturbationBoundary
canonicalBaldEyesalvePerturbationBoundary =
  baldEyesalvePerturbationBoundary false refl false refl true refl true refl true refl

existingInterventionBoundary : Intervene.ResidualInterventionDiscriminatorBoundary
existingInterventionBoundary = Intervene.canonicalResidualInterventionDiscriminatorBoundary

existingDiscriminationBoundary : Disc.BaldEyesalveDiscriminationBoundary
existingDiscriminationBoundary = Disc.canonicalBaldEyesalveDiscriminationBoundary

module DASHI.Biology.Microbiology.BaldEyesalveResidualActionPolicyBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Chemistry.MechanismDiscriminationExact as MD
import DASHI.Chemistry.TransitionKernel as TK
import DASHI.Biology.Microbiology.BaldEyesalveMechanismDiscriminationBidiExact as Disc
import DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact as Experiments

------------------------------------------------------------------------
-- BALD'S EYESALVE RESIDUAL -> ACTION BIDI
--
-- This is intentionally not an automated wet-lab controller.  It maps each
-- discriminating mechanism lane to a least-privilege next-action template and
-- names the missing authority/validation receipt that must be supplied before
-- the action is promoted.
------------------------------------------------------------------------

data ResidualLane : Set where
  sulfurIdentityLane : ResidualLane
  thiolDamageLane : ResidualLane
  recoveryLane : ResidualLane
  functionCellStateLane : ResidualLane
  quorumLane : ResidualLane
  matrixPenetrationLane : ResidualLane
  mixedMechanismLane : ResidualLane
  unresolvedLane : ResidualLane


record EyesalveActionRecommendation : Set where
  constructor eyesalveActionRecommendation
  field
    lane : ResidualLane
    action : Action.ResidualActionKind
    targetCarrier : String
    preferredExperiment : String
    requiredAdmission : String
    interpretation : String

open EyesalveActionRecommendation public

sulfurIdentityAction : EyesalveActionRecommendation
sulfurIdentityAction = eyesalveActionRecommendation
  sulfurIdentityLane
  Action.measure
  "fresh-to-day-9 sulfur-speciation trajectory"
  "BE-X1 time-resolved sulfur speciation"
  "same-batch analytical protocol, compound identity and calibration receipt"
  "resolve target-preparation molecular identity before downstream mediation claims"

thiolDamageAction : EyesalveActionRecommendation
thiolDamageAction = eyesalveActionRecommendation
  thiolDamageLane
  Action.measure
  "reactive sulfur exposure -> protein/LMW-thiol modification -> target function"
  "BE-X2 plus BE-X2F"
  "same-exposure S. aureus thiolome and same-target functional-assay receipt"
  "a phenotype without the predicted thiol/function pattern reopens this lane rather than the whole model"

recoveryAction : EyesalveActionRecommendation
recoveryAction = eyesalveActionRecommendation
  recoveryLane
  Action.measure
  "BSH/BrxAB/YpdA/MerA recovery kinetics"
  "BE-X2 plus recovery-state readout"
  "same-exposure recovery-flux and functional-restoration receipt"
  "marker induction is not effective recovery; measure restoration dynamics"

functionStateAction : EyesalveActionRecommendation
functionStateAction = eyesalveActionRecommendation
  functionCellStateLane
  Action.measure
  "protein function -> proteome/RNA/metabolic/coupled-cell-state carrier"
  "BE-X2F protein-function and coupled-cell-state panel"
  "same-target function and same-time cell-state receipt"
  "modification does not promote directly to whole-cell mechanism"

quorumAction : EyesalveActionRecommendation
quorumAction = eyesalveActionRecommendation
  quorumLane
  Action.perturb
  "organism-appropriate quorum/virulence regulatory carrier"
  "BE-X3 followed by BE-X4 signal/genetic perturbation or rescue"
  "target-system reporter plus perturbation/rescue and viability-control receipt"
  "reporter shift can motivate perturbation but cannot by itself establish mediation"

matrixAction : EyesalveActionRecommendation
matrixAction = eyesalveActionRecommendation
  matrixPenetrationLane
  Action.measure
  "biofilm matrix / spatial exposure / penetration carrier"
  "matched structured-biofilm spatial exposure panel"
  "spatial calibration and structured-versus-planktonic comparison receipt"
  "biofilm-selective activity may reopen transport/matrix rather than intracellular chemistry"

mixedAction : EyesalveActionRecommendation
mixedAction = eyesalveActionRecommendation
  mixedMechanismLane
  Action.perturb
  "two-or-more admitted mechanism lanes"
  "BE-X4 branch-selective perturbation/rescue panel"
  "positive multi-lane evidence plus single-lane insufficiency receipt"
  "mixed is admitted only after evidence for more than one necessary/contributing lane"

unresolvedAction : EyesalveActionRecommendation
unresolvedAction = eyesalveActionRecommendation
  unresolvedLane
  Action.hold
  "current mechanism classification"
  "next discriminator chosen from the unresolved carrier"
  "same-object/context validation and discriminator-admissibility receipt"
  "insufficient discrimination is a hold/re-measure state, not a forced mechanism label"

------------------------------------------------------------------------
-- Explicit reuse of existing discriminating and experimental carriers.
------------------------------------------------------------------------

existingThiolReopen : MD.ReopenTarget
existingThiolReopen = Disc.reopenThiolLane

existingRecoveryReopen : MD.ReopenTarget
existingRecoveryReopen = Disc.reopenRecoveryLane

existingQuorumReopen : MD.ReopenTarget
existingQuorumReopen = Disc.reopenQuorumLane

existingMatrixReopen : MD.ReopenTarget
existingMatrixReopen = Disc.reopenMatrixLane

existingExperimentSelection : TK.ExperimentSelection
existingExperimentSelection = Experiments.canonicalMechanismExperimentSelection

record BaldEyesalveResidualActionBoundary : Set where
  constructor baldEyesalveResidualActionBoundary
  field
    residualAutomaticallyAuthorisesWetLabPerturbation : Bool
    residualAutomaticallyAuthorisesWetLabPerturbationIsFalse :
      residualAutomaticallyAuthorisesWetLabPerturbation ≡ false

    unresolvedResidualForcesMixedMechanismLabel : Bool
    unresolvedResidualForcesMixedMechanismLabelIsFalse :
      unresolvedResidualForcesMixedMechanismLabel ≡ false

    quorumReporterShiftAloneAuthorisesCausalPromotion : Bool
    quorumReporterShiftAloneAuthorisesCausalPromotionIsFalse :
      quorumReporterShiftAloneAuthorisesCausalPromotion ≡ false

    laneSpecificResidualCanSelectLaneSpecificNextAction : Bool
    laneSpecificResidualCanSelectLaneSpecificNextActionIsTrue :
      laneSpecificResidualCanSelectLaneSpecificNextAction ≡ true

    holdPreservesNonRefutationWhenEvidenceIsInsufficient : Bool
    holdPreservesNonRefutationWhenEvidenceIsInsufficientIsTrue :
      holdPreservesNonRefutationWhenEvidenceIsInsufficient ≡ true

canonicalBaldEyesalveResidualActionBoundary : BaldEyesalveResidualActionBoundary
canonicalBaldEyesalveResidualActionBoundary =
  baldEyesalveResidualActionBoundary false refl false refl false refl true refl true refl

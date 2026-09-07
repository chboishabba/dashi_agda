module DASHI.Biology.Microbiology.BaldEyesalveAdaptiveResidualLoopBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.ResidualActionAdaptiveLoopExact as Loop
import DASHI.Biology.Microbiology.BaldEyesalveResidualActionPolicyBidiExact as Policy
import DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact as Experiments
import DASHI.Biology.Microbiology.BaldEyesalveEvidenceRevisionBidiExact as Revision

------------------------------------------------------------------------
-- BALD'S EYESALVE ADAPTIVE RESIDUAL LOOP
--
-- Each next-action template now carries the observation required to feed back
-- into the mechanism residual.  The wet-lab programme therefore has an explicit
-- measure/perturb -> observe -> update -> selectively reopen/stop cycle.
-- Evidence is retained append-only even when the favoured interpretation or
-- next action changes.
------------------------------------------------------------------------

record EyesalveFeedbackRoute : Set where
  constructor eyesalveFeedbackRoute
  field
    lane : Policy.ResidualLane
    action : Action.ResidualActionKind
    experimentReference : String
    requiredPostActionReadout : String
    residualUpdateTarget : String
    causalPromotionCondition : String
    authorityBoundary : String

open EyesalveFeedbackRoute public

sulfurRoute : EyesalveFeedbackRoute
sulfurRoute = eyesalveFeedbackRoute
  Policy.sulfurIdentityLane Action.measure
  "BE-X1 time-resolved sulfur speciation"
  "compound-resolved fresh/day-9 concentration/speciation with batch and calibration provenance"
  "chemical-identity / preparation-trajectory residual"
  "chemical identity alone does not close phenotype mediation"
  "analytical measurement admission remains separate from downstream perturbation authority"

thiolRoute : EyesalveFeedbackRoute
thiolRoute = eyesalveFeedbackRoute
  Policy.thiolDamageLane Action.measure
  "BE-X2 + BE-X2F"
  "matched S. aureus S-thioallylome/LMW-thiol state plus same-target functional readout"
  "thiol-damage and protein-function residual"
  "promotion requires the function/phenotype pattern to track the molecular modification under the same exposure"
  "target-system assay validation and provenance are required"

recoveryRoute : EyesalveFeedbackRoute
recoveryRoute = eyesalveFeedbackRoute
  Policy.recoveryLane Action.measure
  "BE-X2 recovery kinetics"
  "BSH/BrxAB/YpdA/MerA activity/state plus restoration of function/viability"
  "recovery-buffering residual"
  "marker induction is insufficient; effective recovery must be observed"
  "recovery assay admission does not imply intervention authority"

quorumRoute : EyesalveFeedbackRoute
quorumRoute = eyesalveFeedbackRoute
  Policy.quorumLane Action.perturb
  "BE-X3 -> BE-X4 signal/genetic perturbation or rescue"
  "matched reporter, viability and biofilm phenotype before/after admitted perturbation"
  "quorum/regulatory mediation residual"
  "causal promotion requires perturbation/rescue to move the declared phenotype in the predicted direction"
  "reporter evidence does not itself authorise genetic/wet-lab perturbation"

matrixRoute : EyesalveFeedbackRoute
matrixRoute = eyesalveFeedbackRoute
  Policy.matrixPenetrationLane Action.measure
  "structured-biofilm spatial exposure panel"
  "spatial compound exposure, matrix state and structured-versus-planktonic phenotype"
  "matrix/penetration residual"
  "promotion requires structured-context effect to track spatial/matrix change beyond bulk exposure alone"
  "spatial assay calibration remains independently required"

mixedRoute : EyesalveFeedbackRoute
mixedRoute = eyesalveFeedbackRoute
  Policy.mixedMechanismLane Action.perturb
  "BE-X4 branch-selective perturbation/rescue panel"
  "joint post-perturbation panel across at least two independently admitted lanes"
  "multi-lane residual"
  "mixed promotion requires positive multi-lane evidence and failure of admitted single-lane explanations"
  "mixed is not licensed merely because individual lanes remain unresolved"

holdRoute : EyesalveFeedbackRoute
holdRoute = eyesalveFeedbackRoute
  Policy.unresolvedLane Action.hold
  "no forced intervention; select next discriminator from unresolved carrier"
  "same-object/context validation or additional discriminator evidence"
  "unresolved-classification residual"
  "no causal promotion while discrimination remains insufficient"
  "holding preserves non-refutation and does not silently narrow the hypothesis set"

record BaldEyesalveAdaptiveResidualBoundary : Set where
  constructor baldEyesalveAdaptiveResidualBoundary
  field
    perturbationOccurrenceProvesMediation : Bool
    perturbationOccurrenceProvesMediationIsFalse :
      perturbationOccurrenceProvesMediation ≡ false
    reporterChangeWithoutPhenotypeTrackingProvesQuorumMediation : Bool
    reporterChangeWithoutPhenotypeTrackingProvesQuorumMediationIsFalse :
      reporterChangeWithoutPhenotypeTrackingProvesQuorumMediation ≡ false
    postActionPanelCanRefineMechanismResidual : Bool
    postActionPanelCanRefineMechanismResidualIsTrue :
      postActionPanelCanRefineMechanismResidual ≡ true
    unresolvedLaneMayRemainHold : Bool
    unresolvedLaneMayRemainHoldIsTrue :
      unresolvedLaneMayRemainHold ≡ true
    causalPromotionNeedsSameObjectPostActionEvidence : Bool
    causalPromotionNeedsSameObjectPostActionEvidenceIsTrue :
      causalPromotionNeedsSameObjectPostActionEvidence ≡ true
    retainedEvidenceMaySupportRevisedMechanismDisposition : Bool
    retainedEvidenceMaySupportRevisedMechanismDispositionIsTrue :
      retainedEvidenceMaySupportRevisedMechanismDisposition ≡ true

canonicalBaldEyesalveAdaptiveResidualBoundary : BaldEyesalveAdaptiveResidualBoundary
canonicalBaldEyesalveAdaptiveResidualBoundary =
  baldEyesalveAdaptiveResidualBoundary
    false refl false refl true refl true refl true refl true refl

existingLoopBoundary : Loop.ResidualActionAdaptiveLoopBoundary
existingLoopBoundary = Loop.canonicalResidualActionAdaptiveLoopBoundary

existingExperimentSelection : Experiments.TK.ExperimentSelection
existingExperimentSelection = Experiments.canonicalMechanismExperimentSelection

existingEvidenceRevisionBoundary : Revision.BaldEyesalveEvidenceRevisionBoundary
existingEvidenceRevisionBoundary = Revision.canonicalBaldEyesalveEvidenceRevisionBoundary

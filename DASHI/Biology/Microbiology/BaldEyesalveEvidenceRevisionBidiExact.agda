module DASHI.Biology.Microbiology.BaldEyesalveEvidenceRevisionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.ResidualActionSalienceExact as Salience
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Biology.Microbiology.BaldEyesalveResidualActionPolicyBidiExact as Policy
import DASHI.Biology.Microbiology.BaldEyesalveMechanismDiscriminationBidiExact as Disc

------------------------------------------------------------------------
-- BALD'S EYESALVE EVIDENCE REVISION BIDI
--
-- Target-system evidence is accumulated without rewriting history.  New
-- chemistry, thiolome, recovery, quorum/rescue or spatial evidence can revise
-- which mechanism lane is salient and which action is warranted while keeping
-- earlier observations available for other consumers.
------------------------------------------------------------------------

data EyesalveEvidenceStage : Set where
  phenotypeStage
  chemistryStage
  thiolStage
  recoveryStage
  quorumStage
  matrixStage
  : EyesalveEvidenceStage

data MechanismDisposition : Set where
  unresolvedDisposition
  candidateDisposition
  reopenedDisposition
  supportedForConsumerDisposition
  : MechanismDisposition

data StageExtension : EyesalveEvidenceStage → EyesalveEvidenceStage → Set where
  phenotypeToChemistry : StageExtension phenotypeStage chemistryStage
  chemistryToThiol : StageExtension chemistryStage thiolStage
  thiolToRecovery : StageExtension thiolStage recoveryStage
  recoveryToQuorum : StageExtension recoveryStage quorumStage
  quorumToMatrix : StageExtension quorumStage matrixStage

record EyesalveStageReceipt : Set where
  constructor eyesalveStageReceipt
  field
    stage : EyesalveEvidenceStage
    retainedEvidenceReference : String
    newEvidenceReference : String
    mechanismLane : Policy.ResidualLane
    disposition : MechanismDisposition
    nextAction : Action.ResidualActionKind
    consumerReference : String

open EyesalveStageReceipt public

thiolCandidateStage : EyesalveStageReceipt
thiolCandidateStage = eyesalveStageReceipt
  thiolStage
  "phenotype + preparation chemistry retained"
  "matched S. aureus thiol-modification evidence"
  Policy.thiolDamageLane
  candidateDisposition
  Action.measure
  "mechanism-identification consumer"

recoveryReopensThiolDominance : EyesalveStageReceipt
recoveryReopensThiolDominance = eyesalveStageReceipt
  recoveryStage
  "phenotype + chemistry + thiol evidence retained"
  "recovery-capacity / functional-restoration evidence"
  Policy.thiolDamageLane
  reopenedDisposition
  Action.measure
  "dominance-mechanism consumer"

recoveryBecomesSalient : EyesalveStageReceipt
recoveryBecomesSalient = eyesalveStageReceipt
  recoveryStage
  "earlier thiol evidence remains available"
  "BSH/BrxAB/YpdA/MerA recovery evidence"
  Policy.recoveryLane
  candidateDisposition
  Action.measure
  "damage-versus-recovery discrimination consumer"

quorumReporterWithoutMediation : EyesalveStageReceipt
quorumReporterWithoutMediation = eyesalveStageReceipt
  quorumStage
  "chemistry/thiol/recovery evidence retained"
  "quorum/virulence reporter evidence without completed mediation receipt"
  Policy.quorumLane
  reopenedDisposition
  Action.perturb
  "causal-mediation consumer"

matrixEvidenceReopensIntracellularDominance : EyesalveStageReceipt
matrixEvidenceReopensIntracellularDominance = eyesalveStageReceipt
  matrixStage
  "all earlier target-system evidence retained"
  "structured-biofilm spatial exposure / matrix evidence"
  Policy.matrixPenetrationLane
  candidateDisposition
  Action.measure
  "biofilm-context mechanism consumer"

------------------------------------------------------------------------
-- Finite non-monotonicity fixture: additional recovery evidence does not erase
-- the thiol observation, but it changes the disposition of a thiol-dominant
-- interpretation from candidate to reopened.
------------------------------------------------------------------------

candidateIsNotReopened :
  candidateDisposition ≡ reopenedDisposition → ⊥
candidateIsNotReopened ()

thiolDispositionChangesWithRetainedHistory :
  disposition thiolCandidateStage ≡ disposition recoveryReopensThiolDominance → ⊥
thiolDispositionChangesWithRetainedHistory ()

------------------------------------------------------------------------
-- Salience adapter.  One retained evidence body can be highly salient for a
-- scientific mechanism consumer while a different consumer remains at hold or
-- accepts a robust endpoint without claiming unique mechanism identity.
------------------------------------------------------------------------

record EyesalveSalienceRoute : Set where
  constructor eyesalveSalienceRoute
  field
    lane : Policy.ResidualLane
    context : Salience.SalienceContext
    salience : Salience.SalienceClass
    action : Action.ResidualActionKind
    basis : String

open EyesalveSalienceRoute public

thiolMechanismSalience : EyesalveSalienceRoute
thiolMechanismSalience = eyesalveSalienceRoute
  Policy.thiolDamageLane
  (Salience.salienceContext
    "mechanism-identification consumer"
    "thiol/recovery/matrix hypotheses live"
    "chemical -> thiol -> function -> phenotype dependency"
    "measurement authority only")
  Salience.discriminatingForConsumer
  Action.measure
  "same evidence remains worth refining for the mechanism consumer"

endpointConsumerHold : EyesalveSalienceRoute
endpointConsumerHold = eyesalveSalienceRoute
  Policy.unresolvedLane
  (Salience.salienceContext
    "bounded endpoint-description consumer"
    "multiple mechanisms remain live"
    "mechanism identity is not required by this consumer"
    "no perturbation authority inferred")
  Salience.relevantSalience
  Action.hold
  "mechanism ambiguity need not be resolved merely to retain a bounded phenotype statement"

record BaldEyesalveEvidenceRevisionBoundary : Set where
  constructor baldEyesalveEvidenceRevisionBoundary
  field
    moreTargetEvidenceMonotonicallyStrengthensOneMechanism : Bool
    moreTargetEvidenceMonotonicallyStrengthensOneMechanismIsFalse :
      moreTargetEvidenceMonotonicallyStrengthensOneMechanism ≡ false

    failedMediationErasesChemicalPresenceEvidence : Bool
    failedMediationErasesChemicalPresenceEvidenceIsFalse :
      failedMediationErasesChemicalPresenceEvidence ≡ false

    newRecoveryEvidenceMayReopenDamageDominance : Bool
    newRecoveryEvidenceMayReopenDamageDominanceIsTrue :
      newRecoveryEvidenceMayReopenDamageDominance ≡ true

    newMatrixEvidenceMayReopenIntracellularDominance : Bool
    newMatrixEvidenceMayReopenIntracellularDominanceIsTrue :
      newMatrixEvidenceMayReopenIntracellularDominance ≡ true

    unresolvedEvidenceForcesMixedMechanism : Bool
    unresolvedEvidenceForcesMixedMechanismIsFalse :
      unresolvedEvidenceForcesMixedMechanism ≡ false

    sameEndpointAcrossEvidenceStagesImpliesSameMechanism : Bool
    sameEndpointAcrossEvidenceStagesImpliesSameMechanismIsFalse :
      sameEndpointAcrossEvidenceStagesImpliesSameMechanism ≡ false

canonicalBaldEyesalveEvidenceRevisionBoundary : BaldEyesalveEvidenceRevisionBoundary
canonicalBaldEyesalveEvidenceRevisionBoundary =
  baldEyesalveEvidenceRevisionBoundary
    false refl false refl true refl true refl false refl false refl

existingRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
existingRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

existingSalienceBoundary : Salience.ResidualActionSalienceBoundary
existingSalienceBoundary = Salience.canonicalResidualActionSalienceBoundary

existingDiscriminationBoundary : Disc.BaldEyesalveDiscriminationBoundary
existingDiscriminationBoundary = Disc.canonicalBaldEyesalveDiscriminationBoundary

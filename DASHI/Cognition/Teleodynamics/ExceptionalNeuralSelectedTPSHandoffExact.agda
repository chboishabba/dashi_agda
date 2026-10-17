module DASHI.Cognition.Teleodynamics.ExceptionalNeuralSelectedTPSHandoffExact where

------------------------------------------------------------------------
-- TELEODYNAMICS / LILA -> SELECTED-TPS EXCEPTIONAL NEURAL HANDOFF
--
-- Sibling PR #1106 already owns the substantive selected-TPS protocol for
-- exceptional neural tests, cross-pollinated from the quantum-mereology lane.
-- This local owner does not duplicate that protocol.  It records the exact
-- obligations that a Michels/LILA/Brain-IT empirical bridge must inherit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record ExceptionalNeuralSelectedTPSHandoff : Set where
  constructor exceptional-neural-selected-tps-handoff
  field
    sourceSiblingPR : Nat
    selectedTPSProtocolReported : Bool
    quantumMereologySelectionDonorReported : Bool
    brainITObservationDonorReported : Bool
    propofolInterventionDonorReported : Bool

    sameSelectedSubsystemRequired : Bool
    selectionRulePredeclaredRequired : Bool
    scannerPreprocessingFixedRequired : Bool
    exceptionalFeaturePredeclaredRequired : Bool
    nuisanceMatchedBaselineRequired : Bool
    heldOutPredictionRequired : Bool
    competingModelRequired : Bool
    geometrySensitiveCollisionAuditRequired : Bool

    postHocDecoderCoordinatesCanPayGeometry : Bool
    brainITClusterLabelsAloneCanPaySubsystemIdentity : Bool
    stateInterventionAloneCanPayExceptionalGeometry : Bool
    exceptionalFitCreatesConsciousnessMechanism : Bool
    localRawExceptionalNeuralRealizationPaid : Bool
    siblingReceiptCountsAsLocalKernelProof : Bool
    note : String
open ExceptionalNeuralSelectedTPSHandoff public

canonicalExceptionalNeuralSelectedTPSHandoff :
  ExceptionalNeuralSelectedTPSHandoff
canonicalExceptionalNeuralSelectedTPSHandoff =
  exceptional-neural-selected-tps-handoff
    1106
    true true true true
    true true true true true true true true
    false false false false false false
    "Exceptional neural geometry must be tested on the same predeclared selected subsystem/TPS with fixed acquisition/preprocessing, nuisance controls, held-out predictions and competing models. Brain-IT cluster labels are observation coordinates rather than automatic subsystem identity; propofol supplies an intervention rather than exceptional geometry. Post-hoc coordinate switching does not pay the same-geometry test."

record TeleodynamicNeuralExceptionalAssay : Set where
  constructor teleodynamic-neural-exceptional-assay
  field
    predeclareSelectedSubsystem : Bool
    predeclareCandidateGroupOrRootGeometry : Bool
    fitGeneratorActionOnTrainingSplit : Bool
    evaluateHeldOutWeylOrTitsWords : Bool
    preserveSubjectScannerCheckpointHoldouts : Bool
    compareRandomAndLearnedGeometryControls : Bool
    evaluateDecoderCompatibility : Bool
    evaluateFutureConsumerBehaviour : Bool
    reportSelectionCollisions : Bool
open TeleodynamicNeuralExceptionalAssay public

canonicalTeleodynamicNeuralExceptionalAssay : TeleodynamicNeuralExceptionalAssay
canonicalTeleodynamicNeuralExceptionalAssay =
  teleodynamic-neural-exceptional-assay
    true true true true true true true true true

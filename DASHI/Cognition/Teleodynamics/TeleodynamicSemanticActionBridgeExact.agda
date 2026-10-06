module DASHI.Cognition.Teleodynamics.TeleodynamicSemanticActionBridgeExact where

------------------------------------------------------------------------
-- TELEODYNAMICS x SEMANTIC-INTERVENTION WELD
--
-- DASHI SYNTHESIS.
--
-- This module consumes, without re-authoring:
--   * the teleodynamic / LILA / LLM experiment surfaces;
--   * the generic semantic-intervention/equivariance machinery;
--   * the geometric candidate/composition diagnostics;
--   * the T5 243 = 3 + 240 E8 recognition gate.
--
-- It strengthens the empirical endpoint from "similar representations" to the
-- ordered evidence chain
--
-- pair correctness
--   -> fitted latent action
--   -> decoder compatibility / model equivariance
--   -> held-out composition
--   -> future-language outcome.
--
-- None of these steps promotes an empirical fit to mechanism, consciousness,
-- nonlocal transmission, or exceptional-group same-object recognition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SemanticInterventionEquivarianceExact as Intervention
import DASHI.Reasoning.GeometricReasoningCandidateSelectionExact as Candidate
import DASHI.Reasoning.T5E8RelativeComplementCandidateExact as T5E8
import DASHI.Cognition.Teleodynamics.TeleodynamicExperimentProtocolExact as Protocol
import DASHI.Cognition.Teleodynamics.TeleodynamicInteractionDynamicsExact as Dynamics
import DASHI.Cognition.Teleodynamics.TeleodynamicLearningTransferExact as Learning
import DASHI.Cognition.Teleodynamics.LLMGeometricPriorBridgeExact as LLM

------------------------------------------------------------------------
-- 1. A teleodynamic semantic-action experiment is representation-facing.
------------------------------------------------------------------------

record TeleodynamicSemanticActionExperiment
    (X Y Z : Set)
    (model : X → Y)
    (intervention : Intervention.SemanticIntervention X Y) : Set₁ where
  constructor teleodynamic-semantic-action-experiment
  field
    representationWitness :
      Intervention.RepresentationEquivariance {X} {Y} {Z} model intervention

    CandidateAction : Set
    candidateActionLabel : CandidateAction
    candidateGeometryLabel : String

    HeldOutCompositionReceipt : Set
    heldOutCompositionReceipt : HeldOutCompositionReceipt

    FutureLanguageReceipt : Set
    futureLanguageReceipt : FutureLanguageReceipt

    currentPairFitLabel : String
    representationActionFitLabel : String
    compositionFitLabel : String
    futureLanguageComparisonLabel : String
    provenance : String

open TeleodynamicSemanticActionExperiment public

teleodynamicRepresentationWitnessImpliesModelEquivariance :
  ∀ {X Y Z : Set}
    {model : X → Y}
    {intervention : Intervention.SemanticIntervention X Y} →
  TeleodynamicSemanticActionExperiment X Y Z model intervention →
  Intervention.ModelEquivariance model intervention
teleodynamicRepresentationWitnessImpliesModelEquivariance experiment =
  Intervention.representationEquivarianceImpliesModelEquivariance
    (representationWitness experiment)

------------------------------------------------------------------------
-- 2. Evidence grades are ordered conceptually, not collapsed definitionally.
------------------------------------------------------------------------

data SemanticActionEvidenceGrade : Set where
  currentPairCorrectness : SemanticActionEvidenceGrade
  latentActionFit : SemanticActionEvidenceGrade
  decoderCompatibleEquivariance : SemanticActionEvidenceGrade
  heldOutComposition : SemanticActionEvidenceGrade
  futureLanguageSeparation : SemanticActionEvidenceGrade
  sameObjectActionRecognition : SemanticActionEvidenceGrade

record SemanticActionEvidenceLedger : Set₁ where
  constructor semantic-action-evidence-ledger
  field
    GradeReceipt : SemanticActionEvidenceGrade → Set
    receipt : (grade : SemanticActionEvidenceGrade) → GradeReceipt grade
    sourcePairSet : String
    heldOutPairSet : String
    heldOutCompositionSet : String
    futureTraceSet : String

------------------------------------------------------------------------
-- 3. Existing teleodynamic controls remain orthogonal to action fitting.
------------------------------------------------------------------------

record TeleodynamicSemanticActionControls : Set where
  constructor teleodynamic-semantic-action-controls
  field
    scrambleControl : Bool
    crossFamilyControl : Bool
    noBackpropControl : Bool
    modelHoldout : Bool
    temporalHoldout : Bool
    nuisanceInvarianceControl : Bool
    compositionHoldout : Bool

canonicalSemanticActionControls : TeleodynamicSemanticActionControls
canonicalSemanticActionControls =
  teleodynamic-semantic-action-controls
    true true true true true true true

------------------------------------------------------------------------
-- 4. T5/E8 and learned-action recognition remain explicit promotions.
------------------------------------------------------------------------

record ExceptionalActionRecognitionPromotion : Set₁ where
  constructor exceptional-action-recognition-promotion
  field
    relativeRecognition : T5E8.E8RelativeComplementRecognition
    semanticInterventionActionUsesSameAction : Bool
    representationActionIntertwiningObserved : Bool
    heldOutCompositionObserved : Bool
    justification : String

-- Merely having the 243 = 3 + 240 split cannot inhabit the record above;
-- T5E8's own recognition object still requires two-sided carrier recovery and
-- action intertwining.

------------------------------------------------------------------------
-- 5. Cross-stack availability receipts.
------------------------------------------------------------------------

record CrossStackDonorReceipt : Set where
  constructor cross-stack-donor-receipt
  field
    teleodynamicProtocolReused : Bool
    dynamicTraceDisciplineReused : Bool
    gradientVsICLDisciplineReused : Bool
    llmFutureSufficiencyDisciplineReused : Bool
    semanticInterventionTheoremReused : Bool
    geometricCandidateComparisonReused : Bool
    t5E8RecognitionGateReused : Bool

canonicalCrossStackDonorReceipt : CrossStackDonorReceipt
canonicalCrossStackDonorReceipt =
  cross-stack-donor-receipt true true true true true true true

------------------------------------------------------------------------
-- 6. Fail-closed interpretation boundary.
------------------------------------------------------------------------

record TeleodynamicSemanticActionBoundary : Set where
  constructor teleodynamic-semantic-action-boundary
  field
    pairAccuracyCreatesLatentAction : Bool
    latentActionFitCreatesDecoderCompatibility : Bool
    heldOutCompositionRequired : Bool
    futureLanguageOutcomeSeparate : Bool
    successfulActionFitCreatesMechanism : Bool
    successfulActionFitCreatesNonlocalTransmission : Bool
    successfulActionFitCreatesPhenomenology : Bool
    e8CarrierCountCreatesRecognition : Bool
    e8ActionIntertwiningRequired : Bool

canonicalSemanticActionBoundary : TeleodynamicSemanticActionBoundary
canonicalSemanticActionBoundary =
  teleodynamic-semantic-action-boundary
    false false true true false false false false true

------------------------------------------------------------------------
-- Attribution boundary:
-- * Michels remains source for Principia-II scientific proposals.
-- * LILA implementations remain external engineering evidence.
-- * Monster/exceptional-group source mathematics retains its own provenance.
-- * the evidence ladder and this cross-stack weld are DASHI formalisation.
------------------------------------------------------------------------

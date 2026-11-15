module DASHI.Cognition.Teleodynamics.TeleodynamicExperimentProtocolExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationRepresentationExperimentProtocolExact as Experiment
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior

open Experiment.HeldOutScope public

------------------------------------------------------------------------
-- MICHELS/LILA CONTROLLED EXPERIMENT PROTOCOL
------------------------------------------------------------------------

data PriorArm : Set where
  noGeometricPrior : PriorArm
  matchedRandomPrior : PriorArm
  g2Prior : PriorArm
  f4Prior : PriorArm
  e6Prior : PriorArm
  e7Prior : PriorArm
  e8Prior : PriorArm
  leechLikePrior : PriorArm
  learnedCodebookPrior : PriorArm

data OutcomeFamily : Set where
  currentTaskPerformance : OutcomeFamily
  grokkingTiming : OutcomeFamily
  futureLanguage : OutcomeFamily
  compressionDefect : OutcomeFamily
  accessibilityDefect : OutcomeFamily
  spectralConcentration : OutcomeFamily
  codeOccupancy : OutcomeFamily
  prototypeAlignment : OutcomeFamily
  dynamicTraceCommutation : OutcomeFamily

data Control : Set where
  scrambleControl : Control
  crossFamilyControl : Control
  noBackpropICLControl : Control
  modelHoldoutControl : Control
  temporalCheckpointHoldoutControl : Control

teleodynamicHeldOutScope : Experiment.HeldOutScope
teleodynamicHeldOutScope =
  Experiment.heldOutScope
    true true true true
    "Hold out target/task identities, contexts, model families, and temporal checkpoints when testing geometric-prior or teleodynamic transfer."

teleodynamicRelationProtocol : Experiment.RelationExperimentProtocol
teleodynamicRelationProtocol =
  Experiment.relationExperimentProtocol
    true
    "Teacher/student and prior-arm comparisons require declared matched baselines."
    Experiment.contextualCandidate
    Adequacy.cosineLikeGeometry
    teleodynamicHeldOutScope
    ("current task performance"
      ∷ "future learning language"
      ∷ "compression sufficiency"
      ∷ "accessibility sufficiency"
      ∷ "dynamic trace commutation"
      ∷ [])
    true
    true
    false
    "Cosine is admitted as one candidate geometry only; collisions reopen the representation search."

record TeleodynamicExperimentBoundary : Set where
  constructor teleodynamicExperimentBoundary
  field
    scrambleControlDeclared : Bool
    crossFamilyControlDeclared : Bool
    noBackpropControlDeclared : Bool
    modelHoldoutDeclared : Bool
    temporalHoldoutDeclared : Bool
    attentionBiasAblationSeparate : Bool
    quantizerAblationSeparate : Bool
    regularizerAblationSeparate : Bool
    observerAblationSeparate : Bool
    headScaleZeroDisablesAllE8Geometry : Bool
    oneMetricClosesExperiment : Bool
    architecturePriorProvesNonlocalTransfer : Bool

open TeleodynamicExperimentBoundary public

canonicalExperimentBoundary : TeleodynamicExperimentBoundary
canonicalExperimentBoundary =
  teleodynamicExperimentBoundary
    true true true true true
    true true true true
    false false false

externalHeadScaleZeroAblation : Prior.PriorAblationReceipt
externalHeadScaleZeroAblation = Prior.canonicalHeadScaleAblation

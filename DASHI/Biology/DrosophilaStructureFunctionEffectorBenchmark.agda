module DASHI.Biology.DrosophilaStructureFunctionEffectorBenchmark where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly
import DASHI.Biology.DrosophilaConnectomeFunctionalRegistrationBridge as Reg

------------------------------------------------------------------------
-- Sources
------------------------------------------------------------------------

turnerBenchmarkSource : Fly.ScientificSourceReceipt
turnerBenchmarkSource = Reg.turnerSource

gautheyFunctionalSource : Fly.ScientificSourceReceipt
gautheyFunctionalSource = Fly.wholeBrainCalciumSource

maleCNSStructuralSource : Fly.ScientificSourceReceipt
maleCNSStructuralSource = Fly.maleCNSSource

benchmarkSources : List Fly.ScientificSourceReceipt
benchmarkSources =
  turnerBenchmarkSource
  ∷ gautheyFunctionalSource
  ∷ maleCNSStructuralSource
  ∷ []

------------------------------------------------------------------------
-- Structure -> function benchmark.
--
-- Direct structural weight, multi-step/path-aware structure, and a DASHI
-- predictor are compared against held-out registered functional observations.
-- A better DASHI residual is an empirical target, not a theorem.
------------------------------------------------------------------------

data StructuralPredictorKind : Set where
  directEdgeBaseline : StructuralPredictorKind
  pathAwareBaseline : StructuralPredictorKind
  dashiPredictor : StructuralPredictorKind

data BenchmarkBoundary : Set where
  noStructureEqualsFunction : BenchmarkBoundary
  noFunctionalCorrelationEqualsSynapse : BenchmarkBoundary
  noRegistrationLeakage : BenchmarkBoundary
  noDASHIImprovementAssumed : BenchmarkBoundary
  noEffectorPredictionWithoutBodyReceipt : BenchmarkBoundary
  noTrainingOnHeldOutLabels : BenchmarkBoundary

record StructureFunctionBenchmark : Set₁ where
  field
    StructuralUnit : Set
    FunctionalUnit : Set
    StructuralFeature : Set
    FunctionalAssociation : Set
    Prediction : Set
    Residual : Set
    Fold : Set
    RegistrationConfidence : Set

    directStructuralFeature :
      StructuralUnit → StructuralUnit → StructuralFeature

    pathStructuralFeature :
      StructuralUnit → StructuralUnit → StructuralFeature

    predict :
      StructuralPredictorKind →
      StructuralFeature →
      Prediction

    observedFunctionalAssociation :
      FunctionalUnit → FunctionalUnit → FunctionalAssociation

    residual :
      Prediction → FunctionalAssociation → Residual

    registrationConfidence :
      FunctionalUnit → RegistrationConfidence

    trainingFold heldOutFold : Fold

    foldsDisjoint : Set

    trainingUsesHeldOutLabels : Bool
    trainingUsesHeldOutLabelsIsFalse :
      trainingUsesHeldOutLabels ≡ false

    improvementIsAssumption : Bool
    improvementIsAssumptionIsFalse :
      improvementIsAssumption ≡ false

    benchmarkReceipt : Fly.ScientificSourceReceipt

open StructureFunctionBenchmark public

record PredictorComparison
    (B : StructureFunctionBenchmark) : Set₁ where
  field
    Pair : Set
    pairStructuralFeature : Pair → StructuralFeature B
    pairObservedFunction : Pair → FunctionalAssociation B

    directResidual : Pair → Residual B
    pathResidual : Pair → Residual B
    dashiResidual : Pair → Residual B

    Better : Residual B → Residual B → Set

    dashiBeatsDirectTarget : Set
    dashiBeatsPathTarget : Set

    targetReading : String

open PredictorComparison public

------------------------------------------------------------------------
-- Forward continuation: registered functional state -> descending/VNC drive ->
-- effector ROM -> observed behaviour.
------------------------------------------------------------------------

record FunctionalToEffectorBenchmark : Set₁ where
  field
    RegisteredFunctionalState : Set
    DescendingVNCState : Set
    MotorDrive : Set
    EffectorState : Set
    EffectorCoefficient : Set
    BodyState : Set
    BehaviourObservation : Set
    BehaviourResidual : Set

    inferDescendingVNC :
      RegisteredFunctionalState → DescendingVNCState

    inferMotorDrive :
      DescendingVNCState → MotorDrive

    inferEffectorState :
      MotorDrive → EffectorState

    projectEffector :
      EffectorState → EffectorCoefficient

    bodyFromEffector :
      EffectorState → BodyState

    predictBehaviour :
      BodyState → BehaviourObservation

    observedBehaviour :
      RegisteredFunctionalState → BehaviourObservation

    behaviourResidual :
      BehaviourObservation → BehaviourObservation → BehaviourResidual

    connectomeReceipt : Fly.ScientificSourceReceipt
    functionalReceipt : Fly.ScientificSourceReceipt
    actuationReceipt : Fly.ScientificSourceReceipt
    biomechanicsReceipt : Fly.ScientificSourceReceipt
    behaviourReceipt : Fly.ScientificSourceReceipt

    allDownstreamReceiptsPresent : Bool

    functionalStateEqualsEffectorStateClaim : Bool
    functionalStateEqualsEffectorStateClaimIsFalse :
      functionalStateEqualsEffectorStateClaim ≡ false

open FunctionalToEffectorBenchmark public

------------------------------------------------------------------------
-- Joint closed-loop benchmark target.
------------------------------------------------------------------------

record JointDrosophilaSystemIdentificationBenchmark : Set₁ where
  field
    structureFunction : StructureFunctionBenchmark
    functionalEffector : FunctionalToEffectorBenchmark

    structureFunctionSources : List Fly.ScientificSourceReceipt
    effectorSources : List Fly.ScientificSourceReceipt
    boundaries : List BenchmarkBoundary

    jointTargetReading : String

open JointDrosophilaSystemIdentificationBenchmark public

canonicalBenchmarkBoundaries : List BenchmarkBoundary
canonicalBenchmarkBoundaries =
  noStructureEqualsFunction
  ∷ noFunctionalCorrelationEqualsSynapse
  ∷ noRegistrationLeakage
  ∷ noDASHIImprovementAssumed
  ∷ noEffectorPredictionWithoutBodyReceipt
  ∷ noTrainingOnHeldOutLabels
  ∷ []

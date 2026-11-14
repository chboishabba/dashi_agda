module DASHI.Cognition.Teleodynamics.TeleodynamicGeometricCandidateBridgeExact where

------------------------------------------------------------------------
-- TELEODYNAMIC PRIOR ARMS -> GEOMETRIC-REASONING CANDIDATES
--
-- DASHI synthesis.  This is an experiment-routing bridge, not an ontology map.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.GeometricReasoningCandidateSelectionExact as Reasoning
import DASHI.Cognition.Teleodynamics.ExceptionalPriorFamilyExact as Exceptional
import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior

------------------------------------------------------------------------
-- 1. Combined experiment-arm vocabulary.
------------------------------------------------------------------------

data TeleodynamicGeometricArm : Set where
  noPriorArm : TeleodynamicGeometricArm
  randomMatchedArm : TeleodynamicGeometricArm
  g2RootArm : TeleodynamicGeometricArm
  f4RootArm : TeleodynamicGeometricArm
  e6RootArm : TeleodynamicGeometricArm
  e7RootArm : TeleodynamicGeometricArm
  e8RootArm : TeleodynamicGeometricArm
  leechLikeArm : TeleodynamicGeometricArm
  learnedCodebookArm : TeleodynamicGeometricArm
  monster3AArm : TeleodynamicGeometricArm
  monster3BArm : TeleodynamicGeometricArm
  monster3CArm : TeleodynamicGeometricArm

reasoningCandidate :
  TeleodynamicGeometricArm → Reasoning.GeometricReasoningCandidate
reasoningCandidate noPriorArm = Reasoning.unstructuredBaseline
reasoningCandidate randomMatchedArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate g2RootArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate f4RootArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate e6RootArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate e7RootArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate e8RootArm = Reasoning.lilaE8RootPrior
reasoningCandidate leechLikeArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate learnedCodebookArm = Reasoning.genericFiniteActionGeometry
reasoningCandidate monster3AArm = Reasoning.monster3ALocalGeometry
reasoningCandidate monster3BArm = Reasoning.monster3BHeisenbergGeometry
reasoningCandidate monster3CArm = Reasoning.monster3CLocalGeometry

------------------------------------------------------------------------
-- 2. Exceptional-family metadata remain distinct from candidate class.
------------------------------------------------------------------------

record ExceptionalArmReceipt : Set where
  constructor exceptional-arm-receipt
  field
    arm : TeleodynamicGeometricArm
    familyLabel : String
    rootRank : String
    rootCount : String
    representationCarrierDimension : String
    rootModeDistinctFromRepresentationMode : Bool

-- The routing above intentionally maps G2/F4/E6/E7 through the generic finite
-- action candidate because the reasoning donor only has a dedicated LILA-E8
-- constructor.  Their exceptional-family identities continue to live in the
-- teleodynamic exceptional-prior owner rather than being erased by this route.

------------------------------------------------------------------------
-- 3. Comparison must include action/composition/residual diagnostics.
------------------------------------------------------------------------

record TeleodynamicCandidateEvaluation : Set₁ where
  constructor teleodynamic-candidate-evaluation
  field
    arm : TeleodynamicGeometricArm
    reasoningReceipt : Reasoning.CandidateEvaluationReceipt
    currentTaskMetricLabel : String
    representationActionFitLabel : String
    compositionDefectLabel : String
    nuisanceResponseLabel : String
    futureLanguageLabel : String
    compressionLossLabel : String
    accessibilityLossLabel : String
    dynamicCommutationLabel : String
    provenance : String

record TeleodynamicCandidateComparison : Set₁ where
  constructor teleodynamic-candidate-comparison
  field
    left right : TeleodynamicCandidateEvaluation
    reasoningComparison : Reasoning.CandidateComparisonReceipt
    matchedParameterBudget : Bool
    matchedOptimizer : Bool
    matchedDataAndSeeds : Bool
    modelHeldOut : Bool
    temporalHeldOut : Bool
    compositionHeldOut : Bool

------------------------------------------------------------------------
-- 4. Fail-closed boundary.
------------------------------------------------------------------------

record TeleodynamicGeometricCandidateBoundary : Set where
  constructor teleodynamic-geometric-candidate-boundary
  field
    exceptionalFamiliesRemainDistinct : Bool
    rootAndRepresentationModesRemainDistinct : Bool
    e8HasDedicatedLilaCandidate : Bool
    monster3A3B3CRemainDistinct : Bool
    cosineSimilarityAloneClosesCandidateSelection : Bool
    lowestResidualCreatesOntology : Bool
    bestCandidateCreatesMechanism : Bool
    bestCandidateCreatesPhenomenology : Bool

canonicalCandidateBridgeBoundary : TeleodynamicGeometricCandidateBoundary
canonicalCandidateBridgeBoundary =
  teleodynamic-geometric-candidate-boundary
    true true true true false false false false

------------------------------------------------------------------------
-- Attribution: the combined routing/comparison surface is DASHI formalisation;
-- source identities and mathematical ownership remain with their own donors.
------------------------------------------------------------------------

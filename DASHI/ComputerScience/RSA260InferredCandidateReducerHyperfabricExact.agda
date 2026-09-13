module DASHI.ComputerScience.RSA260InferredCandidateReducerHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260DataDrivenReducerInferenceExact as Prior
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Sources

------------------------------------------------------------------------
-- INFERRED-CANDIDATE REDUCER HYPERFABRIC
--
-- This removes the previous fixed pair-fibre assumption from the synthetic
-- reduction pipeline.  Stable NDim graph-refinement classes of size two become
-- candidate transpositions; candidate identity is therefore inferred before
-- requirement/conflict inference.  Equal refinement colour remains only a
-- candidate relation and never constitutes an automorphism proof.
------------------------------------------------------------------------

record InferredCandidateSource : Set where
  constructor inferred-candidate-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    language : String
open InferredCandidateSource public

currentInferredCandidateSource : InferredCandidateSource
currentInferredCandidateSource = inferred-candidate-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_inferred_candidate_reducer_hyperfabric_256_oracle.c"
  "3c0c84972aa9458cb8b9359a179064363ed53ac7"
  "C11"

record InferredCandidateReducerReceipt : Set where
  constructor inferred-candidate-reducer-receipt
  field
    carrierCoordinates : Nat
    ndimRefinementUsedForCandidateDiscovery : Bool
    genericStableClassCount : Nat
    genericInferredPairCandidateCount : Nat
    genericFailsClosedWithoutCandidate : Bool
    equivariantStableClassCount : Nat
    equivariantInferredPairCandidateCount : Nat
    candidatePairingWasPredeclared : Bool
    requirementEdgesThenInferredFromOperator : Bool
    inferredRequirementComponents : Nat
    consumerConflictsThenInferred : Bool
    selectedClosedComponents : Nat
    selectedLocalReducers : Nat
    quotientCoordinateCount : Nat
    globalMPEqualsPMCheckedInSource : Bool
    exactGitBlobExecuted : Bool
    productionRSA260MatrixUsed : Bool
open InferredCandidateReducerReceipt public

currentInferredCandidateReducerReceipt : InferredCandidateReducerReceipt
currentInferredCandidateReducerReceipt = inferred-candidate-reducer-receipt
  256 true
  256 0 true
  128 128 false
  true 8 true
  3 48 208 true
  false false

record CandidateInferencePromotionBoundary : Set where
  constructor candidate-inference-promotion-boundary
  field
    sourceAttributionSeparated : Bool
    conceptIdentitySeparated : Bool
    candidateDiscoverySeparatedFromAutomorphism : Bool
    executionSeparatedFromSourceIdentity : Bool
    productionApplicabilitySeparated : Bool
open CandidateInferencePromotionBoundary public

canonicalCandidateInferencePromotionBoundary : CandidateInferencePromotionBoundary
canonicalCandidateInferencePromotionBoundary = candidate-inference-promotion-boundary
  true true true true true

sourceBoundary : Sources.SnowballAttributionBoundary
sourceBoundary = Sources.canonicalSnowballAttributionBoundary

priorBoundary : Prior.DataDrivenInferencePromotionBoundary
priorBoundary = Prior.currentDataDrivenInferencePromotionBoundary

data InferredCandidateResidual : Set where
  executeExactCommittedBlob : InferredCandidateResidual
  inferCandidateActionsBeyondSizeTwoClasses : InferredCandidateResidual
  inferProductionObserver : InferredCandidateResidual
  inferProductionLiftConstraints : InferredCandidateResidual
  runOnProductionMatrix : InferredCandidateResidual
  compareReducedAndFullReplay : InferredCandidateResidual

firstInferredCandidateResidual : InferredCandidateResidual
firstInferredCandidateResidual = executeExactCommittedBlob

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data EqualRefinementClassImpliesAutomorphism : Set where
data SizeTwoClassImpliesValidReducer : Set where
data CandidateInferenceImpliesProductionReduction : Set where
data DOIOrQIDImpliesAlgorithmicValidity : Set where

refinementClassDoesNotCreateAutomorphism : EqualRefinementClassImpliesAutomorphism → ⊥
refinementClassDoesNotCreateAutomorphism ()

sizeTwoClassDoesNotCreateReducerValidity : SizeTwoClassImpliesValidReducer → ⊥
sizeTwoClassDoesNotCreateReducerValidity ()

candidateInferenceDoesNotCreateProductionReduction : CandidateInferenceImpliesProductionReduction → ⊥
candidateInferenceDoesNotCreateProductionReduction ()

doiOrQidDoesNotCreateAlgorithmicValidity : DOIOrQIDImpliesAlgorithmicValidity → ⊥
doiOrQidDoesNotCreateAlgorithmicValidity ()

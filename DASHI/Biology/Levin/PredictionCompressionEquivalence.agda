module DASHI.Biology.Levin.PredictionCompressionEquivalence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ContextualEntropyRateBoundary as Contextual
import DASHI.Biology.Levin.ObserverRelativePolycomputation as Poly
import DASHI.Biology.Levin.SubstrateConstrainedComputation as Substrate

------------------------------------------------------------------------
-- Prediction/compression bridge.
--
-- A probabilistic predictor can induce code lengths, and a coding scheme can
-- induce an implicit predictive distribution, only relative to a coding rule
-- and normalization witness.  The equivalence is operational, not semantic.

record PredictiveModel : Set₁ where
  field
    Token : Set
    Context : Set
    probabilityAssigned : Context → Token → Bool
    normalizedAtEachContext : Bool
    outOfSampleEvaluated : Bool

record CrossEntropyBoundary : Set where
  field
    dataSourceSpecified : Bool
    modelDistributionSpecified : Bool
    supportMismatchHandled : Bool
    expectedNegativeLogLikelihoodDefined : Bool
    empiricalEstimatorSpecified : Bool
    generalizationGapTracked : Bool
    interpretation : String

record PredictionCompressionBridge : Set where
  field
    contextualBoundary : Contextual.MessageProbabilityBoundary
    polycomputationBoundary : Poly.PolycomputationBoundary
    substrateBoundary : Substrate.SubstrateComputationBoundary
    probabilityToCodeLengthWitness : Bool
    codeLengthToProbabilityWitness : Bool
    arithmeticCoderOrEquivalentWitness : Bool
    finitePrecisionOverheadBound : Bool
    expectedLogLossEqualsExpectedCodeLength : Bool
    modelMismatchAppearsAsExcessLength : Bool

canonicalCrossEntropyBoundary : CrossEntropyBoundary
canonicalCrossEntropyBoundary = record
  { dataSourceSpecified = true
  ; modelDistributionSpecified = true
  ; supportMismatchHandled = true
  ; expectedNegativeLogLikelihoodDefined = true
  ; empiricalEstimatorSpecified = true
  ; generalizationGapTracked = true
  ; interpretation = "Cross-entropy measures expected code length under a model-relative code and separates irreducible source uncertainty from model mismatch"
  }

PredictionEqualsCompressionWithoutCodingModel : Bool
PredictionEqualsCompressionWithoutCodingModel = false

LowerCrossEntropyImpliesGeneralIntelligence : Bool
LowerCrossEntropyImpliesGeneralIntelligence = false

module DASHI.Biology.Levin.ContextualEntropyRateBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Context-indexed source models and entropy-rate obligations.

record ContextualSource : Set₁ where
  field
    Symbol : Set
    Context : Set
    nextContext : Context → Symbol → Context
    conditionalProbabilitySpecified : Context → Symbol → Bool
    normalizedAtEachContext : Bool
    initialContextSpecified : Bool

record MessageProbabilityBoundary : Set where
  field
    chainRuleSpecified : Bool
    contextDependenceRetained : Bool
    zeroProbabilityHandlingSpecified : Bool
    finiteMessageProbabilityDefined : Bool
    logProductToSumWitness : Bool
    interpretation : String

record EntropyRateBoundary : Set where
  field
    stochasticProcessSpecified : Bool
    stationaryAssumptionDeclared : Bool
    ergodicAssumptionDeclared : Bool
    blockEntropyDefined : Bool
    normalizedBlockLimitExists : Bool
    conditionalEntropyLimitExists : Bool
    twoLimitDefinitionsProvedEquivalent : Bool
    operationalCompressionMeaningProved : Bool

canonicalMessageProbabilityBoundary : MessageProbabilityBoundary
canonicalMessageProbabilityBoundary = record
  { chainRuleSpecified = true
  ; contextDependenceRetained = true
  ; zeroProbabilityHandlingSpecified = true
  ; finiteMessageProbabilityDefined = true
  ; logProductToSumWitness = false
  ; interpretation = "The information of a message decomposes into contextual symbol surprisals only after the probability chain rule and logarithmic additivity are supplied"
  }

canonicalEntropyRateBoundary : EntropyRateBoundary
canonicalEntropyRateBoundary = record
  { stochasticProcessSpecified = true
  ; stationaryAssumptionDeclared = false
  ; ergodicAssumptionDeclared = false
  ; blockEntropyDefined = true
  ; normalizedBlockLimitExists = false
  ; conditionalEntropyLimitExists = false
  ; twoLimitDefinitionsProvedEquivalent = false
  ; operationalCompressionMeaningProved = false
  }

CorpusFrequencyIsTrueLanguageDistribution : Bool
CorpusFrequencyIsTrueLanguageDistribution = false

LongerContextAlwaysImprovesPrediction : Bool
LongerContextAlwaysImprovesPrediction = false

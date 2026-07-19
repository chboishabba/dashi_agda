module DASHI.Biology.Levin.CompressionIntelligenceBoundaryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PrefixFreeCodingBoundary as Prefix
import DASHI.Biology.Levin.ShannonInformationEntropyBoundary as Shannon
import DASHI.Biology.Levin.ContextualEntropyRateBoundary as Contextual
import DASHI.Biology.Levin.PredictionCompressionEquivalence as Bridge
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as Hidden
import DASHI.Biology.Levin.ProblemSpaceAgency as ProblemSpace
import DASHI.Biology.Levin.PolycomputationBiologyAdapter as Poly

------------------------------------------------------------------------
-- Integrated boundary for the slogan "compression is intelligence".
--
-- Compression can witness predictive structure relative to a source model,
-- representation, code class, and evaluator.  It does not definitionally
-- supply goals, action, autonomy, transfer, semantics, or consciousness.

record CompressionCapabilityProfile : Set where
  field
    sourceModelSpecified : Bool
    representationSpecified : Bool
    codeClassSpecified : Bool
    heldOutCompressionMeasured : Bool
    computeBudgetAccounted : Bool
    decoderSharedOrCharged : Bool
    transferAcrossDistributionsMeasured : Bool
    actionAndGoalCapacityMeasured : Bool
    semanticTaskPerformanceMeasured : Bool

record CompressionIntelligenceBoundary : Set where
  field
    prefixBoundary : Prefix.CodingOptimalityBoundary
    codingTheoremBoundary : Shannon.NoiselessCodingTheoremBoundary
    entropyRateBoundary : Contextual.EntropyRateBoundary
    predictionCompressionBridge : Bridge.PredictionCompressionBridge
    hiddenStateType : Set
    problemSpaceBoundary : ProblemSpace.ProblemSpaceAgencyBoundary
    polycomputationAdapter : Poly.PolycomputationBiologyAdapter
    betterCompressionWitnessesBetterModelRelativePrediction : Bool
    compressionNotSufficientForAgency : Bool
    compressionNotSufficientForConsciousness : Bool
    incompressibilityNotAbsenceOfStructure : Bool
    randomLookingOutputNotProofOfOptimality : Bool
    intelligenceClaimRequiresTaskFamily : Bool
    interpretation : String

canonicalCompressionCapabilityProfile : CompressionCapabilityProfile
canonicalCompressionCapabilityProfile = record
  { sourceModelSpecified = true
  ; representationSpecified = true
  ; codeClassSpecified = true
  ; heldOutCompressionMeasured = true
  ; computeBudgetAccounted = true
  ; decoderSharedOrCharged = true
  ; transferAcrossDistributionsMeasured = false
  ; actionAndGoalCapacityMeasured = false
  ; semanticTaskPerformanceMeasured = false
  }

canonicalCompressionIntelligenceBoundary : CompressionIntelligenceBoundary
canonicalCompressionIntelligenceBoundary = record
  { prefixBoundary = Prefix.canonicalCodingOptimalityBoundary
  ; codingTheoremBoundary = Shannon.canonicalNoiselessCodingBoundary
  ; entropyRateBoundary = Contextual.canonicalEntropyRateBoundary
  ; predictionCompressionBridge = Bridge.canonicalPredictionCompressionBridge
  ; hiddenStateType = Hidden.HiddenStateNonrecurrenceBoundary
  ; problemSpaceBoundary = ProblemSpace.canonicalProblemSpaceAgencyBoundary
  ; polycomputationAdapter = Poly.canonicalPolycomputationBiologyAdapter
  ; betterCompressionWitnessesBetterModelRelativePrediction = true
  ; compressionNotSufficientForAgency = true
  ; compressionNotSufficientForConsciousness = true
  ; incompressibilityNotAbsenceOfStructure = true
  ; randomLookingOutputNotProofOfOptimality = true
  ; intelligenceClaimRequiresTaskFamily = true
  ; interpretation = "Compression and prediction are operationally linked through model-relative code lengths; intelligence remains a broader capacity profile involving transfer, goals, action, adaptation, and task-indexed competence"
  }

CompressionIsIntelligence : Bool
CompressionIsIntelligence = false

CompressionIsRelevantToIntelligence : Bool
CompressionIsRelevantToIntelligence = true

module DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawComparisonReceipt where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.ContinuousOscillatorUpdateLawAttributionExact as Attribution

producerScriptPathText : String
producerScriptPathText =
  "scripts/run_continuous_oscillator_update_law_discrimination.py"

record ContinuousOscillatorUpdateLawComparisonReceipt : Set where
  constructor continuous-oscillator-update-law-comparison-receipt
  field
    producerScriptPath : String
    producerScriptPathIsCanonical : producerScriptPath ≡ producerScriptPathText
    comparesThreeSixNine : Bool
    comparesThreeSixNineIsTrue : comparesThreeSixNine ≡ true
    currentGradientRecorded : Bool
    currentGradientRecordedIsTrue : currentGradientRecorded ≡ true
    hebbianStyleComparatorRecorded : Bool
    hebbianStyleComparatorRecordedIsTrue : hebbianStyleComparatorRecorded ≡ true
    ojaComparatorRecorded : Bool
    ojaComparatorRecordedIsTrue : ojaComparatorRecorded ≡ true
    kuramotoComparatorRecorded : Bool
    kuramotoComparatorRecordedIsTrue : kuramotoComparatorRecorded ≡ true
    sharedCoordinateGateRetained : Bool
    sharedCoordinateGateRetainedIsTrue : sharedCoordinateGateRetained ≡ true
    exactReductionPromoted : Bool
    exactReductionPromotedIsFalse : exactReductionPromoted ≡ false
    mechanismIdentityPromoted : Bool
    mechanismIdentityPromotedIsFalse : mechanismIdentityPromoted ≡ false
open ContinuousOscillatorUpdateLawComparisonReceipt public

canonicalContinuousOscillatorUpdateLawComparisonReceipt :
  ContinuousOscillatorUpdateLawComparisonReceipt
canonicalContinuousOscillatorUpdateLawComparisonReceipt =
  continuous-oscillator-update-law-comparison-receipt
    producerScriptPathText refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

sourceBoundaryRetained : Attribution.OscillatorUpdateLawSourceBoundary
sourceBoundaryRetained = Attribution.canonicalOscillatorUpdateLawSourceBoundary

record ContinuousOscillatorUpdateLawComparisonBoundary : Set where
  constructor continuous-oscillator-update-law-comparison-boundary
  field
    localCosineSimilarityCreatesGlobalReduction : Bool
    bestScalarProjectionCreatesEquationIdentity : Bool
    sharedAmplitudeCoordinateCreatesHebbianIdentity : Bool
    sharedAmplitudeCoordinateCreatesOjaIdentity : Bool
    sharedPhaseCoordinateCreatesKuramotoIdentity : Bool
    nonComparedFrequencyMayBeSilentlyCoerced : Bool
    sourceAttributionBoundaryRetained : Bool
open ContinuousOscillatorUpdateLawComparisonBoundary public

canonicalContinuousOscillatorUpdateLawComparisonBoundary :
  ContinuousOscillatorUpdateLawComparisonBoundary
canonicalContinuousOscillatorUpdateLawComparisonBoundary =
  continuous-oscillator-update-law-comparison-boundary
    false false false false false false true

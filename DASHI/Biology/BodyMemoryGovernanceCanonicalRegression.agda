module DASHI.Biology.BodyMemoryGovernanceCanonicalRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.BodyMemoryBiologyRegression as BodyMemory
import DASHI.Biology.BraidedEmotionCanonicalIntegration as Emotion
import DASHI.Biology.BodyMemoryMeasurementGovernanceIntegration as Measurement
import DASHI.Biology.NeurodivergentAtlasGovernanceIntegration as Neurodivergent
import DASHI.Biology.RelationalQiGovernanceIntegration as Relational
import DASHI.Biology.FormalLayerExplanationIntegration as Explanation

record BodyMemoryGovernanceCanonicalRegression : Set where
  constructor mkBodyMemoryGovernanceCanonicalRegression
  field
    bodyMemoryRegistry : BodyMemory.BodyMemoryRegistry
    emotionIntegration : Emotion.BraidedEmotionCanonicalIntegration
    measurementIntegration : Measurement.BodyMemoryMeasurementGovernanceIntegration
    neurodivergentIntegration : Neurodivergent.NeurodivergentAtlasGovernanceIntegration
    relationalIntegration : Relational.RelationalQiGovernanceIntegration
    explanationIntegration : Explanation.FormalLayerExplanationIntegration
    governanceIntegrated : Bool
    governanceIntegratedIsTrue : governanceIntegrated ≡ true
    noClinicalPromotion : Bool
    noClinicalPromotionIsFalse : noClinicalPromotion ≡ false

open BodyMemoryGovernanceCanonicalRegression public

canonicalBodyMemoryGovernanceCanonicalRegression : BodyMemoryGovernanceCanonicalRegression
canonicalBodyMemoryGovernanceCanonicalRegression =
  mkBodyMemoryGovernanceCanonicalRegression
    BodyMemory.canonicalBodyMemoryRegistry
    Emotion.canonicalBraidedEmotionCanonicalIntegration
    Measurement.canonicalBodyMemoryMeasurementGovernanceIntegration
    Neurodivergent.canonicalNeurodivergentAtlasGovernanceIntegration
    Relational.canonicalRelationalQiGovernanceIntegration
    Explanation.canonicalFormalLayerExplanationIntegration
    true refl false refl

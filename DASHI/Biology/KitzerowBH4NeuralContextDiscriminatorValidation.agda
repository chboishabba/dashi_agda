module DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as Neural

poolRestorationDoesNotGuaranteeFunctionalRescue :
  Neural.brainBH4RestoredWithoutMonoamineRescue Neural.canonicalNeuralContextBoundary ≡ true
  × Neural.brainBH4RestoredWithoutDopamineRescue Neural.canonicalNeuralContextBoundary ≡ true
poolRestorationDoesNotGuaranteeFunctionalRescue = refl , refl

stateHistoryAndRegionRemainCausalCoordinates :
  Neural.enzymeAbundanceStateMatters Neural.canonicalNeuralContextBoundary ≡ true
  × Neural.brainRegionContextMatters Neural.canonicalNeuralContextBoundary ≡ true
  × Neural.developmentalTimingMatters Neural.canonicalNeuralContextBoundary ≡ true
stateHistoryAndRegionRemainCausalCoordinates = refl , (refl , refl)

neuralEvidenceConstrainsSimpleAllocatorWithoutClosingWholeModel :
  Neural.simpleCurrentPoolSufficiencySupported Neural.canonicalNeuralContextBoundary ≡ false
  × Neural.contextSpecificArchitectureSupportedAsLiveAlternative Neural.canonicalNeuralContextBoundary ≡ true
  × Neural.neuralEvidenceProvesWholeKitzerowModel Neural.canonicalNeuralContextBoundary ≡ false
neuralEvidenceConstrainsSimpleAllocatorWithoutClosingWholeModel = refl , (refl , refl)

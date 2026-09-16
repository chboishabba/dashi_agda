module DASHI.Reasoning.PlatoSymposiumProofSearchExperimentRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Reasoning.PlatoSymposiumProofSearchExperimentExact as Bridge

currentUtteranceDoesNotFixNextProbe :
  Bridge.currentUtteranceDeterminesNextProbe
    Bridge.canonicalPlatoProofSearchExperimentBoundary ≡ false
currentUtteranceDoesNotFixNextProbe = refl

supportCountDoesNotFixInquiryState :
  Bridge.supportCountDeterminesInquiryState
    Bridge.canonicalPlatoProofSearchExperimentBoundary ≡ false
supportCountDoesNotFixInquiryState = refl

consensusDoesNotFixConsumerResolution :
  Bridge.consensusDeterminesConsumerRelevantResolution
    Bridge.canonicalPlatoProofSearchExperimentBoundary ≡ false
consensusDoesNotFixConsumerResolution = refl

questionSequenceIsNotFixedScript :
  Bridge.nextQuestionMayDependOnObservedOutcome
    Bridge.canonicalPlatoProofSearchExperimentBoundary ≡ true
questionSequenceIsNotFixedScript = refl

proofValidityStaysSeparateFromSearchPolicy :
  Bridge.searchStrategyCreatesProofValidity
    Bridge.canonicalPlatoProofSearchExperimentBoundary ≡ false
proofValidityStaysSeparateFromSearchPolicy = refl

existingSearchOwnersAreReused :
  Bridge.existingProofSearchOwnersReused ≡ true
existingSearchOwnersAreReused = refl

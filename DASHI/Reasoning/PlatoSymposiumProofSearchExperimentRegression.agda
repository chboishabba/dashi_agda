module DASHI.Reasoning.PlatoSymposiumProofSearchExperimentRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Reasoning.PlatoSymposiumProofSearchExperimentExact as Bridge

currentUtteranceDoesNotFixNextProbe :
  Query.FactorsThrough
    Bridge.nextProbeQuestions
    Bridge.currentUtteranceProjection
    Bridge.nextUsefulProbeQuestion → ⊥
currentUtteranceDoesNotFixNextProbe =
  Bridge.currentUtteranceDoesNotDetermineNextProbe

supportCountDoesNotFixInquiryState :
  Query.FactorsThrough
    Bridge.inquiryStateQuestions
    Bridge.supportCountProjection
    Bridge.inquiryStateQuestion → ⊥
supportCountDoesNotFixInquiryState =
  Bridge.supportCountDoesNotDetermineInquiryState

consensusDoesNotFixConsumerResolution :
  Query.FactorsThrough
    Bridge.consumerResolutionQuestions
    Bridge.consensusStatusProjection
    Bridge.consumerResolutionQuestion → ⊥
consensusDoesNotFixConsumerResolution =
  Bridge.consensusDoesNotDetermineConsumerResolution

questionSequenceIsNotFixedScript :
  Bridge.sequentialExperimentMayDependOnPriorOutcome
    Bridge.canonicalPlatoSymposiumProofSearchBoundary ≡ true
questionSequenceIsNotFixedScript = refl

proofValidityStaysSeparateFromSearchPolicy :
  Bridge.proofValidityRemainsSeparatelyOwned
    Bridge.canonicalPlatoSymposiumProofSearchBoundary ≡ true
proofValidityStaysSeparateFromSearchPolicy = refl

pluralDialogueIsNotProofSearchAlgorithm :
  Bridge.symposiumDialogueIsProofSearchAlgorithm
    Bridge.canonicalPlatoSymposiumProofSearchBoundary ≡ false
pluralDialogueIsNotProofSearchAlgorithm = refl

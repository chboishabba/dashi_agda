module DASHI.Cognition.PNF.GrokkingMeasureStrataExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok

------------------------------------------------------------------------
-- TRAINING / TASK / MECHANISM MASS ARE DIFFERENT NORMALIZATIONS
--
-- The Cantor bridge requires every "1" to name its measure.  Grokking gives a
-- concrete neural example: complete training fit does not imply complete task
-- coverage, and latent mechanism mass may become visible before behavioural
-- generalization moves.
------------------------------------------------------------------------

trainingMass : Grok.LearningState → Nat
trainingMass state with Grok.trainingFit state
... | true = 1
... | false = 0

taskMass : Grok.LearningState → Nat
taskMass state with Grok.generalizationVisible state
... | true = 1
... | false = 0

mechanismMass : Grok.LearningState → Nat
mechanismMass state with Grok.latentAlgorithmicProgress state
... | true = 1
... | false = 0

memorizerHasUnitTrainingMass : trainingMass Grok.memorizerBefore ≡ 1
memorizerHasUnitTrainingMass = refl

memorizerHasZeroTaskMass : taskMass Grok.memorizerBefore ≡ 0
memorizerHasZeroTaskMass = refl

trainingUnitDoesNotImplyTaskUnit :
  taskMass Grok.memorizerBefore ≡ 1 → ⊥
trainingUnitDoesNotImplyTaskUnit ()

structuredLatentMechanismAlreadyUnit :
  mechanismMass Grok.structuredBefore ≡ 1
structuredLatentMechanismAlreadyUnit = refl

structuredTaskObservableStillZeroBeforeTransition :
  taskMass Grok.structuredBefore ≡ 0
structuredTaskObservableStillZeroBeforeTransition = refl

latentMechanismUnitCanPrecedeVisibleTaskUnit :
  taskMass Grok.structuredBefore ≡ mechanismMass Grok.structuredBefore → ⊥
latentMechanismUnitCanPrecedeVisibleTaskUnit ()

structuredTaskMassBecomesUnitAfterContinuation :
  taskMass Grok.structuredAfter ≡ 1
structuredTaskMassBecomesUnitAfterContinuation = refl

------------------------------------------------------------------------
-- Exact boundary: these Nat values are normalized finite indicators, not a
-- claim that production-network mechanism strength is literally a probability
-- measure.  The theorem is that the three declared notions of unit mass need
-- not coincide.
------------------------------------------------------------------------

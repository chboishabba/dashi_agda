module DASHI.Environment.BiocontrolCostedExperimentChoiceRegression where

import DASHI.Environment.BiocontrolCostedExperimentChoiceExact as Costed

------------------------------------------------------------------------
-- Regression surface for the consumer-indexed experiment-cost weld.
------------------------------------------------------------------------

cheapestOxygenProbe : Costed.OxygenChoiceReceipt
cheapestOxygenProbe = Costed.canonicalOxygenChoice

cheapestNutrientProbe : Costed.NutrientChoiceReceipt
cheapestNutrientProbe = Costed.canonicalNutrientChoice

cheapestCommunityProbe : Costed.CommunityChoiceReceipt
cheapestCommunityProbe = Costed.canonicalCommunityChoice

cheapestAgentInteractionProbe : Costed.AgentInteractionChoiceReceipt
cheapestAgentInteractionProbe = Costed.canonicalAgentInteractionChoice

cheaperProbeNeedNotResolveDifferentConsumer : Costed.CrossConsumerCostBoundary
cheaperProbeNeedNotResolveDifferentConsumer = Costed.canonicalCrossConsumerCostBoundary

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

------------------------------------------------------------------------
-- RED regression: each costed choice must now retain the concrete collision
-- and a separating experiment-bundle witness, rather than only an abstract
-- obstruction constructor.
------------------------------------------------------------------------

oxygenChoiceIsCollisionBacked : Costed.OxygenCollisionBackedChoiceReceipt
oxygenChoiceIsCollisionBacked = Costed.canonicalOxygenCollisionBackedChoice

reboundChoiceIsCollisionBacked : Costed.ReboundCollisionBackedChoiceReceipt
reboundChoiceIsCollisionBacked = Costed.canonicalReboundCollisionBackedChoice

restorationChoiceIsCollisionBacked : Costed.RestorationCollisionBackedChoiceReceipt
restorationChoiceIsCollisionBacked = Costed.canonicalRestorationCollisionBackedChoice

agentChoiceIsCollisionBacked : Costed.AgentCollisionBackedChoiceReceipt
agentChoiceIsCollisionBacked = Costed.canonicalAgentCollisionBackedChoice

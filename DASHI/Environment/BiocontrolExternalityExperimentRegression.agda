module DASHI.Environment.BiocontrolExternalityExperimentRegression where

import DASHI.Environment.BiocontrolExternalityExperimentExact as Biocontrol

------------------------------------------------------------------------
-- RED regression: target suppression alone must not pay the dissolved-oxygen
-- consumer, while a biomass-fate / oxygen discriminator must separate the
-- canonical collision.
------------------------------------------------------------------------

oxygenCollisionIsConsumerRelevant : Biocontrol.OxygenCollisionReceipt
oxygenCollisionIsConsumerRelevant = Biocontrol.canonicalOxygenCollision

oxygenProbeSeparatesSuppressionCollision : Biocontrol.OxygenDiscriminatorReceipt
oxygenProbeSeparatesSuppressionCollision = Biocontrol.canonicalOxygenDiscriminator

------------------------------------------------------------------------
-- RED regression: target suppression plus present oxygen state still does not
-- determine restoration outcome; community recovery is an additional axis.
------------------------------------------------------------------------

restorationCollisionIsConsumerRelevant : Biocontrol.RestorationCollisionReceipt
restorationCollisionIsConsumerRelevant = Biocontrol.canonicalRestorationCollision

communityProbeSeparatesRestorationCollision : Biocontrol.RestorationDiscriminatorReceipt
communityProbeSeparatesRestorationCollision = Biocontrol.canonicalRestorationDiscriminator

------------------------------------------------------------------------
-- RED regression: equal present target suppression does not close future
-- nutrient/seedbank rebound risk.
------------------------------------------------------------------------

reboundCollisionIsConsumerRelevant : Biocontrol.ReboundCollisionReceipt
reboundCollisionIsConsumerRelevant = Biocontrol.canonicalReboundCollision

nutrientCoordinateSeparatesReboundCollision : Biocontrol.ReboundDiscriminatorReceipt
nutrientCoordinateSeparatesReboundCollision = Biocontrol.canonicalReboundDiscriminator

------------------------------------------------------------------------
-- RED regression: equal target suppression and equal declared agent-count
-- surface do not determine whether the agent assemblage is independent or
-- interfering.
------------------------------------------------------------------------

agentInteractionCollisionIsConsumerRelevant : Biocontrol.AgentInteractionCollisionReceipt
agentInteractionCollisionIsConsumerRelevant = Biocontrol.canonicalAgentInteractionCollision

agentInteractionCoordinateSeparatesCollision : Biocontrol.AgentInteractionDiscriminatorReceipt
agentInteractionCoordinateSeparatesCollision = Biocontrol.canonicalAgentInteractionDiscriminator

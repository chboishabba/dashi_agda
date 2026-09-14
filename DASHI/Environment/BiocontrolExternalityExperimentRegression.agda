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

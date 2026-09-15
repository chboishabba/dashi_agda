module DASHI.Environment.BiocontrolActiveExperimentSearchRegression where

import DASHI.Environment.BiocontrolActiveExperimentSearchExact as Search

------------------------------------------------------------------------
-- RED regression: an oxygen observation reopens exactly the oxygen-dependent
-- downstream certificates, not an unrelated host-specificity certificate.
------------------------------------------------------------------------

oxygenObservationReopensOxygen : Search.OxygenReopeningReceipt
oxygenObservationReopensOxygen = Search.canonicalOxygenReopening

oxygenObservationReopensNetOutcome : Search.NetOutcomeReopeningReceipt
oxygenObservationReopensNetOutcome = Search.canonicalNetOutcomeReopening

hostSpecificityRemainsOutsideOxygenClosure : Search.HostSpecificityUnaffectedReceipt
hostSpecificityRemainsOutsideOxygenClosure = Search.canonicalHostSpecificityUnaffected

------------------------------------------------------------------------
-- RED regression: rebound and agent-interaction collisions must enter the same
-- generic collision -> bundle -> refined fibre -> selective reopening pipeline.
------------------------------------------------------------------------

reboundActiveSearch : Search.ReboundActiveSearchReceipt
reboundActiveSearch = Search.canonicalReboundActiveSearch

agentInteractionActiveSearch : Search.AgentInteractionActiveSearchReceipt
agentInteractionActiveSearch = Search.canonicalAgentInteractionActiveSearch

restorationActiveSearch : Search.RestorationActiveSearchReceipt
restorationActiveSearch = Search.canonicalRestorationActiveSearch

activeSearchWeld : Search.BiocontrolActiveExperimentSearch
activeSearchWeld = Search.canonicalBiocontrolActiveExperimentSearch

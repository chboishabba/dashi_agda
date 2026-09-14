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

activeSearchWeld : Search.BiocontrolActiveExperimentSearch
activeSearchWeld = Search.canonicalBiocontrolActiveExperimentSearch

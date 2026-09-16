module DASHI.Physics.Foundations.RFSensingProofSearchSnowballRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RFSensingProofSearchSnowballExact as RFSearch

------------------------------------------------------------------------
-- RED contract: this module intentionally imports a production owner that
-- does not yet exist at the point this regression is introduced.
------------------------------------------------------------------------

hackadayConsumerWifiLeadRequired : RFSearch.AcquisitionLead
hackadayConsumerWifiLeadRequired = RFSearch.hackadayConsumerWifiLead

hackadaySDRLeadRequired : RFSearch.AcquisitionLead
hackadaySDRLeadRequired = RFSearch.hackadaySDRPassiveRadarLead

proofSearchRouteRequired : RFSearch.RFSearchRoute
proofSearchRouteRequired = RFSearch.canonicalRFSearchRoute

sourceRolesSnowballRequired : RFSearch.RFAttributionBoundary
sourceRolesSnowballRequired = RFSearch.canonicalRFAttributionBoundary

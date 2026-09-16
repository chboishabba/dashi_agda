module DASHI.Physics.Foundations.GoniometerPhasedArrayAcquisitionSnowballRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.GoniometerPhasedArrayAcquisitionSnowballExact as Acquisition

------------------------------------------------------------------------
-- RED contract: the acquisition owner is introduced after this regression.
------------------------------------------------------------------------

historicalGoniometerLineageRequired : Acquisition.HistoricalGoniometerAcquisition
historicalGoniometerLineageRequired = Acquisition.canonicalHistoricalGoniometerAcquisition

phasedArrayAngleLineageRequired : Acquisition.PhasedArrayAngleAcquisition
phasedArrayAngleLineageRequired = Acquisition.canonicalPhasedArrayAngleAcquisition

acquisitionFrontierRequired : Acquisition.AcquisitionFrontier
acquisitionFrontierRequired = Acquisition.canonicalAcquisitionFrontier

sourcePromotionFirewallRequired : Acquisition.AcquisitionAuthorityFirewall
sourcePromotionFirewallRequired = Acquisition.canonicalAcquisitionAuthorityFirewall

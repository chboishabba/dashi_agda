module DASHI.Physics.Foundations.CSIArrayGoniometerSnowballRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CSIArrayGoniometerSnowballExact as Bridge

------------------------------------------------------------------------
-- RED contract: the production bridge imported above does not exist when
-- this regression lands.  The required surface keeps commodity CSI, phased
-- array direction finding, and the historical goniometer role in one typed
-- observer ladder without identifying their hardware implementations.
------------------------------------------------------------------------

coarseCSIRefutationRequired : ¬ Bridge.CoarseCSIFactorsToAoA
coarseCSIRefutationRequired = Bridge.coarseCSICannotRecoverAoA

phaseRepairRequired : Bridge.PhaseRefinementReceipt
phaseRepairRequired = Bridge.canonicalPhaseRefinementReceipt

phasedArrayEndpointRequired : Bridge.PhasedArrayEndpointReceipt
phasedArrayEndpointRequired = Bridge.canonicalPhasedArrayEndpointReceipt

goniometerEndpointRequired : Bridge.GoniometerEndpointReceipt
goniometerEndpointRequired = Bridge.canonicalGoniometerEndpointReceipt

snowballRouteRequired : Bridge.CSIArraySnowballRoute
snowballRouteRequired = Bridge.canonicalCSIArraySnowballRoute

observerIdentityFirewallRequired : Bridge.ObserverIdentityFirewall
observerIdentityFirewallRequired = Bridge.canonicalObserverIdentityFirewall

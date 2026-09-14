module DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationValidation where

------------------------------------------------------------------------
-- RED/GREEN regression for the publication-facing homochiral Taylor splice.
--
-- The production owner must:
--   * construct the exact paired Taylor carrier from radial multiplier values;
--   * reuse the existing paired second-order identity;
--   * expose the existing second-moment compiler without claiming its four
--     physical envelope inequalities are already paid;
--   * retain the abandoned incidence-only separation route as negative-control
--     provenance rather than silently deleting it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R

pairedTaylorCarrierClosed :
  R.r571HomochiralPairedTaylorCarrierClosed ≡ true
pairedTaylorCarrierClosed = R.r571HomochiralPairedTaylorCarrierClosedIsTrue

pairedSecondOrderIdentityReused :
  R.r571ExistingPairedSecondOrderIdentityReused ≡ true
pairedSecondOrderIdentityReused =
  R.r571ExistingPairedSecondOrderIdentityReusedIsTrue

pairedSecondMomentCompilerReused :
  R.r571ExistingPairedSecondMomentCompilerReused ≡ true
pairedSecondMomentCompilerReused =
  R.r571ExistingPairedSecondMomentCompilerReusedIsTrue

physicalEnvelopeInequalitiesRemainOpen :
  R.r571PhysicalSecondMomentEnvelopeBudgetClosed ≡ false
physicalEnvelopeInequalitiesRemainOpen =
  R.r571PhysicalSecondMomentEnvelopeBudgetClosedIsFalse

incidenceOnlySeparationRouteAbandoned :
  R.r571IncidenceOnlySeparationRouteRetained ≡ false
incidenceOnlySeparationRouteAbandoned =
  R.r571IncidenceOnlySeparationRouteRetainedIsFalse

r568NotPromotedHere :
  R.r571R568SpacetimeBudgetClosedHere ≡ false
r568NotPromotedHere = R.r571R568SpacetimeBudgetClosedHereIsFalse

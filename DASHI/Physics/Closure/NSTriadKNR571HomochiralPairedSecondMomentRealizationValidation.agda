module DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationValidation where

------------------------------------------------------------------------
-- RED/GREEN regression for the publication-facing homochiral Taylor splice.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R
import DASHI.Physics.Closure.NSTriadKNR571OppositeRound27PairedTaylorExact as PairWeld

pairedTaylorCarrierClosed :
  R.r571HomochiralPairedTaylorCarrierClosed ≡ true
pairedTaylorCarrierClosed = R.r571HomochiralPairedTaylorCarrierClosedIsTrue

oppositeRound27PairCarrierClosed :
  PairWeld.r571OppositeRound27PairCarrierClosed ≡ true
oppositeRound27PairCarrierClosed = PairWeld.r571OppositeRound27PairCarrierClosedIsTrue

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

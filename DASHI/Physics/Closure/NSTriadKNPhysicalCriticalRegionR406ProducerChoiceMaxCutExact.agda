module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406ProducerChoiceMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / VALID R406 PRODUCER CHOICE AFTER HOMOGENEITY RECUT
--
-- The universal A3/coherent-covariance same-object shortcut is not admissible:
-- it attempts to identify a quartic carrier with the quintic nonlinear R406
-- signed cross.  Existing source already provides two valid alternatives that
-- preserve amplitude degree honestly.
--
-- Route Q5 (direct): retain the literal quintic forcing/commutator cross and
-- prove its cutoff-uniform spacetime budget (R568/R503).
--
-- Route Q4+E (dynamic): use the exact R406 endpoint / Gram-flux normal forms
-- to replace the quintic producer by a quartic integrated Gram bound plus a
-- weighted-flux endpoint bound.  The compiler is already present; the two
-- analytic bounds are not.
--
-- Thus B7 is a genuine producer choice, not a representation weld.  Either
-- route suffices once its analytic receipt is supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as Direct
import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Quartic
import DASHI.Physics.Closure.NSTriadKNR406ExactEndpointNormalFormExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNA3ToR568HomogeneityBoundaryRound612Exact as Boundary

data B7ProducerRoute : Set where
  directSignedQuintic : B7ProducerRoute
  quarticGramPlusEndpoint : B7ProducerRoute

b7ProducerRouteClosed : B7ProducerRoute → Bool
b7ProducerRouteClosed directSignedQuintic =
  Direct.round568LiveCommutatorSpacetimeBudgetClosed
b7ProducerRouteClosed quarticGramPlusEndpoint =
  Quartic.directGramFluxAnalyticBoundsClosed

b7ExactEndpointNormalFormCompilerClosed : Bool
b7ExactEndpointNormalFormCompilerClosed =
  Endpoint.r406ExactEndpointNormalFormClosedGivenScalarFTC

b7QuarticGramEndpointCompilerAvailable : Bool
b7QuarticGramEndpointCompilerAvailable =
  Quartic.directR503QuarticGramPlusEndpointProducerAvailable

b7DirectSignedQuinticRouteClosed : Bool
b7DirectSignedQuinticRouteClosed =
  b7ProducerRouteClosed directSignedQuintic

b7QuarticGramEndpointRouteClosed : Bool
b7QuarticGramEndpointRouteClosed =
  b7ProducerRouteClosed quarticGramPlusEndpoint

b7UniversalA3RepresentationBridgeAdmissible : Bool
b7UniversalA3RepresentationBridgeAdmissible =
  not Boundary.a3ToR568RequiresScaleChangingAnalyticContent
  where
  not : Bool → Bool
  not true = false
  not false = true

b7ScaleChangingAnalyticContentRequired : Bool
b7ScaleChangingAnalyticContentRequired =
  Boundary.a3ToR568RequiresScaleChangingAnalyticContent

b7DirectRouteKeepsFineSignedCrossUntilPairing : Bool
b7DirectRouteKeepsFineSignedCrossUntilPairing =
  Boundary.canonicalR503RouteKeepsSignedCrossFineUntilPairing

b7RepresentationOnlyWorkRemaining : Bool
b7RepresentationOnlyWorkRemaining = false

clayPromotion : Bool
clayPromotion = false

b7ExactEndpointNormalFormCompilerClosedIsTrue :
  b7ExactEndpointNormalFormCompilerClosed ≡ true
b7ExactEndpointNormalFormCompilerClosedIsTrue = refl

b7QuarticGramEndpointCompilerAvailableIsTrue :
  b7QuarticGramEndpointCompilerAvailable ≡ true
b7QuarticGramEndpointCompilerAvailableIsTrue = refl

b7DirectSignedQuinticRouteClosedIsFalse :
  b7DirectSignedQuinticRouteClosed ≡ false
b7DirectSignedQuinticRouteClosedIsFalse = refl

b7QuarticGramEndpointRouteClosedIsFalse :
  b7QuarticGramEndpointRouteClosed ≡ false
b7QuarticGramEndpointRouteClosedIsFalse = refl

b7RepresentationOnlyWorkRemainingIsFalse :
  b7RepresentationOnlyWorkRemaining ≡ false
b7RepresentationOnlyWorkRemainingIsFalse = refl

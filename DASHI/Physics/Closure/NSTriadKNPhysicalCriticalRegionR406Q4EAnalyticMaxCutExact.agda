module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / PREFERRED Q4+E ANALYTIC MAX-CUT
--
-- Exact source now supplies:
--
--   * the direct-resolvent Gram/flux normal form,
--   * the literal global off-diagonal R290 derivative family,
--   * exact attachment to R406's canonical pair list,
--   * endpoint FTC given the repository's ordinary scalar FTC authority.
--
-- Therefore the preferred B7 route now has exactly TWO genuine analytic
-- inequalities left:
--
--   Q4  cutoff-uniform integrated off-diagonal Gram bound,
--   E   cutoff-uniform weighted-flux endpoint-increment bound.
--
-- Neither is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Q4E
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EFTCCompilerMaxCutExact as FTC

q4eExactNormalFormClosed : Bool
q4eExactNormalFormClosed = Q4E.directR503QuarticGramPlusEndpointProducerAvailable

q4ePreferredB7Route : Bool
q4ePreferredB7Route = true

q4eOffDiagonalFluxDerivativeCompilerClosed : Bool
q4eOffDiagonalFluxDerivativeCompilerClosed =
  FTC.q4eLiteralOffDiagonalDerivativeCompilerClosed

q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTC : Bool
q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTC =
  FTC.q4eEndpointFTCClosedGivenOrdinaryScalarFTC

q4eResearchLeavesReducedToTwoAnalyticBounds : Bool
q4eResearchLeavesReducedToTwoAnalyticBounds =
  FTC.q4eResearchLeavesReducedToTwoAnalyticBounds

q4eIntegratedGramBoundClosed : Bool
q4eIntegratedGramBoundClosed = false

q4eFluxEndpointBoundClosed : Bool
q4eFluxEndpointBoundClosed = false

q4eRepresentationOrTemporalPlumbingRemaining : Bool
q4eRepresentationOrTemporalPlumbingRemaining = false

q4eIntroducesQuinticEstimate : Bool
q4eIntroducesQuinticEstimate = false

clayPromotion : Bool
clayPromotion = false

q4eExactNormalFormClosedIsTrue : q4eExactNormalFormClosed ≡ true
q4eExactNormalFormClosedIsTrue = refl

q4ePreferredB7RouteIsTrue : q4ePreferredB7Route ≡ true
q4ePreferredB7RouteIsTrue = refl

q4eOffDiagonalFluxDerivativeCompilerClosedIsTrue :
  q4eOffDiagonalFluxDerivativeCompilerClosed ≡ true
q4eOffDiagonalFluxDerivativeCompilerClosedIsTrue = refl

q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTCIsTrue :
  q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTC ≡ true
q4eOffDiagonalFluxFTCClosedGivenOrdinaryScalarFTCIsTrue = refl

q4eResearchLeavesReducedToTwoAnalyticBoundsIsTrue :
  q4eResearchLeavesReducedToTwoAnalyticBounds ≡ true
q4eResearchLeavesReducedToTwoAnalyticBoundsIsTrue = refl

q4eIntegratedGramBoundClosedIsFalse :
  q4eIntegratedGramBoundClosed ≡ false
q4eIntegratedGramBoundClosedIsFalse = refl

q4eFluxEndpointBoundClosedIsFalse :
  q4eFluxEndpointBoundClosed ≡ false
q4eFluxEndpointBoundClosedIsFalse = refl

q4eRepresentationOrTemporalPlumbingRemainingIsFalse :
  q4eRepresentationOrTemporalPlumbingRemaining ≡ false
q4eRepresentationOrTemporalPlumbingRemainingIsFalse = refl

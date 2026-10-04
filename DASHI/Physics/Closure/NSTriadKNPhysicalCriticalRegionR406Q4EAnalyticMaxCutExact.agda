module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406Q4EAnalyticMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / PREFERRED Q4+E ANALYTIC MAX-CUT
--
-- The exact direct-resolvent Gram/flux normal form is already available:
--
--   4 * integral C_direct
--     = integral offDiagonalGram
--       + integral offDiagonalFluxTangent.
--
-- The existing compiler turns this into an R503 budget once three receipts are
-- supplied:
--
--   Q4a  cutoff-uniform integrated off-diagonal Gram bound,
--   E0   exact FTC for the same weighted off-diagonal flux curve,
--   E1   cutoff-uniform weighted-flux endpoint bound.
--
-- Only Q4a and E1 are genuine estimates.  E0 is standard derivative/FTC
-- plumbing, but no concrete literal off-diagonal R422 family currently closes
-- it in the repository, so it remains fail-closed here rather than being
-- silently treated as an estimate or as already proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNDirectResolventGramFluxNormalFormExact as Q4E
import DASHI.Physics.Closure.NSTriadKNR418FinitePairFamilyToR409Round422Exact as R422
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426

q4eExactNormalFormClosed : Bool
q4eExactNormalFormClosed = Q4E.directR503QuarticGramPlusEndpointProducerAvailable

q4ePreferredB7Route : Bool
q4ePreferredB7Route = true

q4eOffDiagonalFluxFTCClosed : Bool
q4eOffDiagonalFluxFTCClosed = false

q4eIntegratedGramBoundClosed : Bool
q4eIntegratedGramBoundClosed = false

q4eFluxEndpointBoundClosed : Bool
q4eFluxEndpointBoundClosed = false

q4eOnlyStandardTemporalSeamBeforeEndpointEstimate : Bool
q4eOnlyStandardTemporalSeamBeforeEndpointEstimate =
  R422.round422RemainingTemporalLeafIsActualCellCurveDifferentiation

q4eProjectedCrossProductRuleIsTemporalRoot : Bool
q4eProjectedCrossProductRuleIsTemporalRoot =
  R426.round426RemainingAnalyticLawIsProjectedCrossProductRule

q4eIntroducesNewRepresentationCarrier : Bool
q4eIntroducesNewRepresentationCarrier = false

q4eIntroducesQuinticEstimate : Bool
q4eIntroducesQuinticEstimate = false

clayPromotion : Bool
clayPromotion = false

q4eExactNormalFormClosedIsTrue : q4eExactNormalFormClosed ≡ true
q4eExactNormalFormClosedIsTrue = refl

q4ePreferredB7RouteIsTrue : q4ePreferredB7Route ≡ true
q4ePreferredB7RouteIsTrue = refl

q4eOffDiagonalFluxFTCClosedIsFalse :
  q4eOffDiagonalFluxFTCClosed ≡ false
q4eOffDiagonalFluxFTCClosedIsFalse = refl

q4eIntegratedGramBoundClosedIsFalse :
  q4eIntegratedGramBoundClosed ≡ false
q4eIntegratedGramBoundClosedIsFalse = refl

q4eFluxEndpointBoundClosedIsFalse :
  q4eFluxEndpointBoundClosed ≡ false
q4eFluxEndpointBoundClosedIsFalse = refl

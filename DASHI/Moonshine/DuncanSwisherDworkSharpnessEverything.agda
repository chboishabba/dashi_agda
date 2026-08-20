module DASHI.Moonshine.DuncanSwisherDworkSharpnessEverything where

------------------------------------------------------------------------
-- Public convergence root for the Dwork / Legendre first-pole sharpness lane.
--
--   exact Legendre exceptional polynomial factorization
--     -> algebraically forced ramification exponent 3/2
--     -> source-native local unit + depth-one parameter lift
--     -> ramified local J-coordinate depth
--     -> Dwork A1 valuation transfer
--     -> exact 3/2/1 coefficient depths
--     -> p11 Brandt-weight weld
--     -> exceptional p=5,7,11 partial-fraction total depth.
--
-- The existing bounded integer p-depth machinery is reused only below the
-- analytic boundary as an executable strict-minimum valuation shadow.  It is
-- deliberately not promoted to Dwork's p-adic carrier, and fuel stabilization
-- is proof-relevant rather than globally postulated.
--
-- The exceptional exponents 3 and 2 are no longer accepted as free p-adic
-- source data: they are derived from the exact Legendre j polynomial identities.
-- The remaining source authority is the genuine local p-adic lift/unit/parameter
-- construction plus Dwork's A1-to-local-J valuation transfer.
------------------------------------------------------------------------

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact
import DASHI.Algebra.SeparatedLeadingValuationExact
import DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact
import DASHI.Arithmetic.VpTrue
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact
import DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression

module DASHI.Moonshine.DuncanSwisherDworkSharpnessEverything where

------------------------------------------------------------------------
-- Public convergence root for the Dwork / Legendre first-pole sharpness lane.
--
--   multiplicative valuation algebra
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
-- The remaining authority is the actual Dwork p-adic local construction, not
-- a numeric first-pole depth table.
------------------------------------------------------------------------

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact
import DASHI.Algebra.SeparatedLeadingValuationExact
import DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact
import DASHI.Arithmetic.VpTrue
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact
import DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression

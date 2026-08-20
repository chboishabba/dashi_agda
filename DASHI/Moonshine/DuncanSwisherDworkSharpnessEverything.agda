module DASHI.Moonshine.DuncanSwisherDworkSharpnessEverything where

------------------------------------------------------------------------
-- Public convergence root for the Dwork / Legendre first-pole sharpness lane.
--
--   exact Legendre exceptional polynomial factorization
--     -> algebraically forced ramification exponent 3/2
--     -> simple-root/complement residue geometry
--     -> residue nonzero gives local-unit depth zero
--     -> depth-one lifted coordinate gives depth-one branch
--     -> ramified local J-coordinate depth
--     -> Dwork A1 valuation transfer
--     -> exact 3/2/1 coefficient depths
--     -> p11 Brandt-weight weld
--     -> exceptional p=5,7,11 partial-fraction total depth.
--
-- Finite exceptional residue inputs are now explicit for all p=5,7,11:
-- p=5 uses a concrete F25 quadratic chart, while p=7,11 use the rational
-- j=1728 Legendre branches.  None of these finite carriers is promoted to a
-- p-adic lift.
--
-- The existing bounded integer p-depth machinery is reused only below the
-- analytic boundary as an executable strict-minimum valuation shadow.  It is
-- deliberately not promoted to Dwork's p-adic carrier, and fuel stabilization
-- is proof-relevant rather than globally postulated.
--
-- The remaining source authority is now narrower than a free ramified-power
-- statement: construct the actual lifted local coordinate/factorizations and
-- Dwork's n=1 A1-to-local-J valuation transfer.
------------------------------------------------------------------------

import DASHI.Algebra.RamifiedLocalValuationSharpnessExact
import DASHI.Algebra.SeparatedLeadingValuationExact
import DASHI.Algebra.ResidueDetectedUnitValuationExact
import DASHI.Algebra.SimpleRootLocalParameterExact
import DASHI.Arithmetic.VpDepthStrictMinimumBridgeExact
import DASHI.Arithmetic.VpTrue
import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact
import DASHI.Moonshine.LegendreExceptionalBranchSimpleRootExact
import DASHI.Moonshine.LegendreJExceptionalLocalValuationCutsetExact
import DASHI.Moonshine.LegendreJExceptionalResidueLocalProducerExact
import DASHI.Moonshine.P5LegendreJZeroF25ResidueExact
import DASHI.Moonshine.P7P11LegendreJ1728ResidueCertificatesExact
import DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact
import DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression

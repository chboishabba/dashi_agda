module DASHI.Moonshine.DuncanSwisherDworkSharpnessEverything where

------------------------------------------------------------------------
-- Public convergence root for the Dwork / Legendre first-pole sharpness lane.
--
--   exact Legendre exceptional polynomial factorization
--     -> algebraically forced ramification exponent 3/2
--     -> explicit p=5,7,11 certified exceptional residue points
--     -> standard Hensel lift lambda0 of that finite centre
--     -> lambda := lambda0 + pi
--     -> lambda-lambda0 = pi*1
--     -> actual simple branch + rational J-alpha factors
--     -> v(J-alpha)=ramification exponent
--     -> published Deligne--Dwork A_n(alpha^) integer family
--     -> same-carrier p-adic coefficient family
--     -> Dwork Theorem 8.2 / Section 7.e n=1 sharpness
--     -> DERIVED v(A_1)=v(J-alpha)
--     -> exact 3/2/1 coefficient depths
--     -> exceptional partial-fraction total depth.
-- The three former p>3 source-facing objects are now closed at explicit
-- published authority boundaries.  In particular, `tracksLocalJDepth` is no
-- longer irreducible authority: it is reconstructed from Dwork's actual n=1
-- sharp-value theorem and the independently derived Hensel/Legendre J depth.
-- We still deliberately do not claim a formal reconstruction of all of
-- Dwork's 1969 p-adic cycle machinery or infinite convergence theory.
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
import DASHI.Moonshine.LegendreExceptionalPadicLiftSameObjectExact
import DASHI.Moonshine.LegendreExceptionalCertifiedResiduePointsExact
import DASHI.Moonshine.LegendreExceptionalPadicHenselConstructionExact
import DASHI.Moonshine.P5LegendreJZeroF25ResidueExact
import DASHI.Moonshine.P7P11LegendreJ1728ResidueCertificatesExact
import DASHI.Moonshine.DuncanSwisherDworkFirstPoleSameObjectExact
import DASHI.Moonshine.DuncanSwisherDworkPublishedCoefficientFamilyExact
import DASHI.Moonshine.DuncanSwisherDworkPublishedFirstPoleSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkPublishedAnalyticCompletionExact
import DASHI.Moonshine.DuncanSwisherDworkPublishedAnalyticCompletionRegression
import DASHI.Moonshine.DuncanSwisherDworkExceptionalAnalyticCutsetExact
import DASHI.Moonshine.DuncanSwisherDworkLiftedFirstPoleSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkRamifiedA1SharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkExceptionalPartialFractionSharpnessExact
import DASHI.Moonshine.DuncanSwisherDworkVpDepthShadowExact
import DASHI.Moonshine.DuncanSwisherDworkSharpnessHighestAlphaRegression

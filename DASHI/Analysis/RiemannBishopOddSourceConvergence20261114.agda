module DASHI.Analysis.RiemannBishopOddSourceConvergence20261114 where

------------------------------------------------------------------------
-- ORIGINAL RH BISHOP / FAST-CAUCHY / ODD-ZETA SOURCE-ACCEPTANCE ROOT.
--
-- Source donor: PR #1497, exact head
-- f213b5bfb893e49ae9b29b2915257884b3b0e14e.
-- See original author/DOI and code-priority records in
-- Docs/formalisms/ZetaOddIrrationalityBishopC3MaxCut.md and
-- Docs/SourceAttributionPolicy.md.
--
-- This imports the actual setoid comparison and odd-value witness
-- adapters, rather than claiming any arbitrary surrogate real.
-- It introduces no new RH assumptions, arbitrary Weil functional,
-- off-line-zero exclusion or signed residual positivity.
--
-- Pinned Agda 2.9 and transitive trust checks OPEN. Import root is
-- not a proof of RH, the G3 inequality or odd zeta irrationality.
------------------------------------------------------------------------

import DASHI.Analysis.BishopFastCauchyCanonicalRationalWeldExact
import DASHI.Analysis.BishopFastCauchyRationalNormalizationRoundTripExact
import DASHI.Analysis.BishopFastCauchyZetaWeldExact
import DASHI.Analysis.BishopSetoidWeldExact
import DASHI.Analysis.RiemannOddIrrationalityClayBoundaryExact
import DASHI.Analysis.ZetaOddValueWitnessTransportExact
import DASHI.Analysis.ZetaZ7AgdaIndexTransportExact

module DASHI.Statistics.ZipfFamilyEverything where

-- Canonical qualified statistics entry for the 27 requested Zipf-family
-- subjects, 27 Oct 2026. This aggregates ONLY source-written sibling
-- modules: it does not imply that any empirical laws hold universally,
-- that Agda has typechecked, or that an analytic zeta/Hilberg/RH result
-- is owned here. Prior mathematical and statistical researchers retain
-- original ownership and independently dated source roots.
--
-- Reuse the existing DASHI finite probability owner through the
-- adapter in ZipfIIDTwoDrawAndPNFExact; no second PNF is constructed.

import DASHI.Statistics.ZipfFamilyFiniteExact
import DASHI.Statistics.ZipfHeapsOrderNoGoExact
import DASHI.Statistics.ZipfIIDTwoDrawAndPNFExact
import DASHI.Statistics.ZipfPNFConstructiveNormalizationExact
import DASHI.Statistics.ZipfFractionAddRationalBridgeExact
import DASHI.Statistics.ZipfFractionFoldConditionalExact
import DASHI.Statistics.ZipfNoveltyCurveInjectiveExact
import DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact
import DASHI.Statistics.ZipfABC6OrderHeapsQuotientExact
import DASHI.Statistics.ZipfTernary27ActionHeapsExact

module DASHI.ComputerScience.TekumDASHIRoundingAssemblyExact where

------------------------------------------------------------------------
-- DASHI-owned extension of the existing verified Tékum assembly.
--
-- The historical assembly remains the authority for Hunhold/source claims and
-- keeps its Proposition-5/no-double-rounding flags unchanged.  This extension
-- imports the independent exact-nearest semantics and its theorem/falsifier
-- boundary without reinterpreting those historical booleans.
------------------------------------------------------------------------

import DASHI.ComputerScience.TekumBalancedTernaryVerifiedAssembly
import DASHI.ComputerScience.TekumExactNearestRoundingSemantics
import DASHI.ComputerScience.TekumNearestRoundingEnumerationExact
import DASHI.ComputerScience.TekumCanonicalNearestTieExact
import DASHI.ComputerScience.TekumRawNearestCorrectionExact
import DASHI.ComputerScience.TekumEfficientNearestRoundingExact
import DASHI.ComputerScience.TekumNearestNoDoubleRoundingExact
import DASHI.ComputerScience.TekumDASHIRoundingBoundaryExact

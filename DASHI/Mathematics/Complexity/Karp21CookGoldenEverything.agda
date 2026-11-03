{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CookGoldenEverything where

------------------------------------------------------------------------
-- GOLDEN K00 SAT semantic/certificate import root.
--
-- Only transitive-safe in-repository theorem owners are imported.
-- No postulates, metas, unsafe termination, or uncosted polynomial
-- membership claims are introduced.
--
-- Independent acceptance target:
--   agda -i . DASHI/Mathematics/Complexity/Karp21CookGoldenEverything.agda
--
-- This root contains strict SAT syntax, canonical decoder inverse,
-- executable finite Boolean SAT checker, all-accepted-word linear
-- certificate bound, and conditional PR.InNP packaging.
-- It does NOT import concrete tape models, their unverified machine
-- clocks, or a claimed Cook-Levin universal NP-completeness root.
-- Original mathematical credit: Cook 1971; Leonid Levin 1973.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.PolynomialReductionExact
import DASHI.Mathematics.Complexity.FiniteWordSizeExact
import DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact
import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact
import DASHI.Mathematics.Complexity.Karp21CookStrictWordCanonicalReencodeExact
import DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact
import DASHI.Mathematics.Complexity.Karp21StrictSATBoundedCertificateNPBoundaryExact

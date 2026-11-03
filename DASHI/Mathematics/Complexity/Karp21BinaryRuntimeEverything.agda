module DASHI.Mathematics.Complexity.Karp21BinaryRuntimeEverything where

------------------------------------------------------------------------
-- FOCUSED N21 RUNTIME BRIDGE ROOT -- NOT GOLDEN YET.
--
-- Original binary graph-word and sparse certificate semantics:
--   BitWord input -> gamma fields -> 2m endpoint bits -> Boolean result.
--
-- Includes a Fin-free runtime candidate plus the exact Fin
-- materialisation-size obstruction.  No new graph decision language,
-- no postulates and no claimed polynomialTimeVerifier proof.
--
-- Needed before promotion:
-- * Pointwise Bool equality with the source-owned N21 typed verifier.
-- * A bit-tape semantics and actual polynomial runtime receipt
--   independent of the decoded numerical vertex count n.
-- * Transitive --safe imports and Agda kernel acceptance.
--
-- Attribution: Karp (1972); DASHI original signed gamma E20/N21
-- codec and sparse consistency proof owners, Agda stdlib Fin owners.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.Karp21BinaryFinMaterializationCostExact
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact

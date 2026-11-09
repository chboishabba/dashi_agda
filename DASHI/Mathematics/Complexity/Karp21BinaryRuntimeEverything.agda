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

import DASHI.Mathematics.Complexity.Karp21FinFreeEndpointScanComparisonCountExact

import DASHI.Mathematics.Complexity.Karp21FinFreePairwiseQuadraticCountExact

-- Original-word input-length polynomial endpoint-comparison certificate.
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact

import DASHI.Mathematics.Complexity.Karp21N21SameWordCountedAcceptanceExact

import DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact

import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGraphComparisonEnvelopeExact

-- Native bit-weighted original-word comparison envelope (not a machine receipt).
import DASHI.Mathematics.Complexity.Karp21N21BitWeightedComparisonEnvelopeExact

import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryEqualitySameValueExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordNumericalWeldExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordValidityExact

-- All-word native signed-gamma structural inspection bound.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedInspectionClockExact

-- K05: original/native signed gamma all-word acceptance equivalence.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedAllWordValidityExact

-- K05: native ripple-carry sum and concrete linear inspection clock.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact

-- K05: proof-side Nat value semantics of executable bitwise ripple adder.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact

-- K05: executable two-lane binary signed-weight fold and total invariants.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact

-- K05: bit-native signed score vs original-shaped sign/magnitude threshold.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact

-- N21: decode original strictly positive gamma(W) as binary W, not W+1.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact

-- N21 binary-prefix trie identity sharing; equivalence and tape clock remain open.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeEndpointPrefixTrieExact

import DASHI.Mathematics.Complexity.Karp21BinaryNativeMultiplicityScaleExact
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorExact

-- K05: source-written all-word equivalence of grouped and original binary signed ledgers.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorSemanticExact

-- FRACDASH priority/guard dependency cache: generic same-step theorem.
-- N21 specialization and tape-clock receipt still open.
import DASHI.Mathematics.Complexity.Karp21FractranPriorityFrontierExact

-- Actual original N21 endpointConsistent/boolEqual + binary-ledger FRACDASH edge transition.
-- One-edge same-step and cached-score-update theorems; full rawSparseScore weld open.
import DASHI.Mathematics.Complexity.Karp21FractranN21EndpointScoreStepExact

-- Full raw-edge-list selected signed trace, same original rawSparseScore.
-- Source-written all-list equality; native binary token weld remains open.
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact

-- Actual original selected-edge signed trace equals typed N21 for every word.
-- This is ORIGINAL ℤ replay, not the native binary machine-clock result.
import DASHI.Mathematics.Complexity.Karp21FractranOriginalTypedTraceAcceptanceExact

-- Original raw signed ℤ trace projection from aligned native binary tokens.
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact

-- Original/native signed-gamma suffix identity on every word, including rejection.
-- Signed integer magnitude/value equality remains unproved.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedSuffixExact

-- Exact original gamma encoded-frame readouts in native token and original signed ℤ, suffix-preserving.
-- Original binary token arithmetic identity remains the P0 owner.
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact

-- Actual source zigzag (2M)/(2M−1) integer arithmetic, and BE gamma / native LE ledger value and signed successor decomposition.
-- Source-written, not yet original all-word signed-token ℤ theorem or Agda receipt.
import DASHI.Mathematics.Complexity.Karp21SignedGammaNumberTheoryExact
import DASHI.Mathematics.Complexity.Karp21SignedGammaBinaryValueArithmeticExact

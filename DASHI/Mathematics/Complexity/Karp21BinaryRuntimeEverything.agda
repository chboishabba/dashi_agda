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

-- Actual native signed token ℤ value matches original zigzag value on complete original gamma frames.
-- Still requires all-word successful-frame lifting and original raw-edge stream alignment.
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact

-- Actual native gamma successful-frame decomposition: exact zero prefix, consumed payload count and suffix.
-- Feeds all-word original/native signed integer representation agreement.
import DASHI.Mathematics.Complexity.Karp21SignedGammaAllWordFrameExtractionExact

-- Actual native signed-weight gamma token stream projected to original N21 readRawEdges and exact signed suffix.
-- Original gamma Nat endpoints still used; all-bit native endpoint clock/open.
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact

-- All-word original E20 signed item/strict partition numeric observation through actual native token parser.
-- Proof-side count and signed value only: bit-costed E20 runtime remains OPEN.
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeItemStreamExact

-- Native selected-token signed ℤ score matches original rawSparseScore under exact paired raw-edge numeric alignment.
-- Native two-lane ledger-to-signed-ℤ observation and whole graph still OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeSelectedSignedScoreExact

-- Actual binary signed ledger's two-register integer observation and original rawSparseScore correspondence.
-- SOURCE ONLY: complete graph grammar, physical clock and PR.InNP remain OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact
import DASHI.Mathematics.Complexity.Karp21NativeLedgerOriginalRawScoreExact

-- P0-E/F original compareLE structural correctness, reflexivity and source inspection bound.
-- General numeric atLeast theorem and physical bit-tape motion remain OPEN.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdStructuralExact

-- P0-E: constructive Nat gap witnesses for the ACTUAL compareLE on ALL bitwords, including noncanonical zero padding.
-- Agda kernel and complete original positive-threshold grammar remain outstanding.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdNumericalExact

-- Strictly positive N21 original threshold: actual native predecessor/nonzero test gives a positive Nat observation on every success.
-- SOURCE only; complete graph-word and original threshold value match OPEN.
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNonzeroExact

-- Exact positive N21 gamma source-frame numerical equality for actual binary predecessorLE (n, not n+1).
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNumericFrameExact

-- P0-D original complete raw-edge/certificate cursor FRACTRAN machine, exact first-enabled step and halt.
-- Final threshold and full typed graph decoder remain OPEN.
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawListMachineExact

-- Concrete N21 parsed raw-edge state: first-enabled FRACTRAN step includes actual binary terminal positive-threshold branch.
-- Original all-word graph header / bit clock / InNP remain separate.
import DASHI.Mathematics.Complexity.Karp21FractranParsedRawThresholdMachineExact

-- Original whole-word gamma(n), gamma(m), signed native weights, positive native threshold, strict original validation/suffix.
-- All-word observed graph equality and native binary endpoints remain OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeRawGraphWordExact

-- All-original-word Fin-free graph parser field equality: source gamma n/m, native signed weights and positive threshold, canonical validation/rejection.
-- Proof-side Nat endpoints and physical clock still OPEN; exact Agda kernel pending.
import DASHI.Mathematics.Complexity.Karp21NativeOriginalWholeGraphFieldsWeldExact

-- P0-F parsed original signed N21 machine: each enabled first-priority cursor step strictly lowers edge-count+1 potential.
-- NOT a physical bit-tape polynomial clock.
import DASHI.Mathematics.Complexity.Karp21FractranParsedRawStepPotentialExact

-- P1 original concrete tape same-run weld: canonical six-cell codec, run CNF path, identical flat tableau assignment and input-row pullback.
-- Global clause placement/accepting-run CNF/clock remains OPEN.
import DASHI.Mathematics.Complexity.Karp21ConcreteTapeCanonicalRunFlatWeldExact

-- P0-E signed terminal inequality for ACTUAL atLeast/addBits and two-register ledger, original Int <=b.
-- Source proof candidate: full word acceptance/bit clock remain separate.
import DASHI.Mathematics.Complexity.Karp21NativeThresholdOriginalSignedDecisionExact

-- P0-E actual binary two-lane signed threshold acceptance exactly original signed rawSparseScore for source-parsed raw edges.
-- Full all-word graph validator and physical bit-TM clock still OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeParsedRawAcceptanceExact

-- P0-E all-original-input-word native signed graph + binary ledger acceptance vs ORIGINAL Fin-free verifier.
-- Kernel receipt, native endpoint bit clock, original PR.InNP and typed N21 bridge remain OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeWordAcceptanceExact

-- P0-B/F actual binary endpoint/address reader, original raw-edge stream, strict bit-only validator.
-- Semantic observation source candidates; full original graph-validator equivalence, m/header and physical TM clock OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact

-- P0-B/F actual binary endpoint/address reader, original raw-edge stream, strict bit-only validator.
-- Semantic observation source candidates; full original graph-validator equivalence, m/header and physical TM clock OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact

-- P0-B/F actual binary endpoint/address reader, original raw-edge stream, strict bit-only validator.
-- Semantic observation source candidates; full original graph-validator equivalence, m/header and physical TM clock OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryStrictAfterOriginalExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryValidRawEdgesOriginalExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact

-- N21 original bit-native header/m/count, lex strict ordering, endpoint-history and whole runtime.
-- Proof candidates pending exact-head Agda; original typed bridge + physical bit-TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact

-- B5 actual binary endpoint history equals the original NatP Dec vertex chronology (SOURCE ONLY).
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryOriginalExact

-- Complete executable original N21 bit-register graph/certificate/signed-score/threshold path.
-- All-word original correctness kernel receipt and selected bit-TM clock remain OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact

-- B6 original signed edge stream via input-bounded binary count/fuel, source candidate only.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountFuelOriginalExact

-- B6 original signed edge stream via input-bounded binary count/fuel, source candidate only.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetFuelExact

-- Current real binary B6 graph/verifier/typed correspondence and F2 adder width; proof candidates only.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact

-- Current real binary B6 graph/verifier/typed correspondence and F2 adder width; proof candidates only.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCutLedgerOriginalExact

-- Current real binary B6 graph/verifier/typed correspondence and F2 adder width; proof candidates only.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierOriginalExact

-- Current real binary B6 graph/verifier/typed correspondence and F2 adder width; proof candidates only.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryTypedAcceptanceExact

-- Current real binary B6 graph/verifier/typed correspondence and F2 adder width; proof candidates only.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryAdderWidthBoundExact

-- Actual original-wire binary state machine, first-enabled priority, terminal halt (source only).
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityMachineExact

-- Actual binary first-enabled rule strict potential, finite-run halt and original N21 terminal acceptance.
-- SOURCE only: full original trace and physical bit-TM cost remain unpaid.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryStepPotentialExact

-- Actual binary first-enabled rule strict potential, finite-run halt and original N21 terminal acceptance.
-- SOURCE only: full original trace and physical bit-TM cost remain unpaid.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryFiniteRunExact

-- Actual binary first-enabled rule strict potential, finite-run halt and original N21 terminal acceptance.
-- SOURCE only: full original trace and physical bit-TM cost remain unpaid.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryPriorityRunAcceptanceExact

-- E1 original ordered signed selected-edge event trace on actual first-enabled binary machine.
-- Source-written proof candidate; Agda 2.9 and physical TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinarySelectedEventTraceExact

-- E1 original ordered signed selected-edge event trace on actual first-enabled binary machine.
-- Source-written proof candidate; Agda 2.9 and physical TM cost OPEN.
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryTraceRebuildExact

-- D2 essential negative control: original raw-list 'finished' ignores W, while binary whole machine threshold-rejects.
-- Therefore require a threshold-aware terminal observer/stuttering simulation, not phase equality.
import DASHI.Mathematics.Complexity.Karp21OriginalRawVsBinaryTerminalCounterexampleExact

-- D2 real original paired-raw-list machine state/step weld: binary nonterminal and terminal threshold quotient separately.
import DASHI.Mathematics.Complexity.Karp21NativeBinaryToOriginalRawMachineStepExact

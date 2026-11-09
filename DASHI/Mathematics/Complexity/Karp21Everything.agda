module DASHI.Mathematics.Complexity.Karp21Everything where

------------------------------------------------------------------------
-- Focused compile/check root for the Karp (1972) integration tranche.
-- DOI: 10.1007/978-1-4684-2001-2_9.
-- Source-written only until checked with the pinned Agda toolchain.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.Karp21HistoricalDagExact
import DASHI.Mathematics.Complexity.PolynomialReductionExact
import DASHI.Mathematics.Complexity.Karp21ReductionTransportExact
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact
import DASHI.Mathematics.Complexity.Karp21CliqueSetPackingExact
import DASHI.Mathematics.Complexity.Karp21WeightedCutObjectiveExact

import DASHI.Mathematics.Complexity.Karp21VertexSetCoverIncidenceExact
import DASHI.Mathematics.Complexity.Karp21ColouringCliqueCoverExact
import DASHI.Mathematics.Complexity.Karp21ExactHittingTransposeExact
import DASHI.Mathematics.Complexity.Karp21CertifiedDagTransportExact
import DASHI.Mathematics.Complexity.Karp21PartitionCutQuadraticExact
import DASHI.Mathematics.Complexity.Karp21SATToThreeSATGadgetExact
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact

import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact

import DASHI.Mathematics.Complexity.Karp21HeterogeneousEncodingExact

import DASHI.Mathematics.Complexity.Karp21FiniteCliqueCoverCardinalityExact

import DASHI.Mathematics.Complexity.Karp21FiniteCliqueVertexCoverCombinedExact
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact
import DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact

import DASHI.Mathematics.Complexity.Karp21FiniteColouringCliqueCoverExact

import DASHI.Mathematics.Complexity.Karp21SignedLaplacianCutExact

import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact

import DASHI.Mathematics.Complexity.Karp21PNFSignedTriangleSameObjectExact
import DASHI.Mathematics.Complexity.Karp21SSPTernaryMaskedCutExact
import DASHI.Mathematics.Complexity.Karp21SignedFrustrationBidiExact
import DASHI.Mathematics.Complexity.Karp21SSPDualCheegerSignlessOneExact
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphObjectiveExact
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact

import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact

import DASHI.Mathematics.Complexity.Karp21MaxCutCertificateBinaryCodecExact

import DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact

import DASHI.Mathematics.Complexity.Karp21FiniteCliquePackingDecisionExact

import DASHI.Mathematics.Complexity.Karp21FiniteNodeSetCoverDecisionExact

import DASHI.Mathematics.Complexity.Karp21MalformedWordTotalReductionExact

import DASHI.Mathematics.Complexity.Karp21UpperPairGraphEnumerationExact

import DASHI.Mathematics.Complexity.Karp21VOAZ2CutOrbitExact

import DASHI.Mathematics.Complexity.Karp21VOAGradeActionCertificateWeldExact

import DASHI.Mathematics.Complexity.Karp21VOAGradeDimensionCutSeparationExact

import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact

import DASHI.Mathematics.Complexity.Karp21CookLevinConcreteBitWordReuseExact

import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact

import DASHI.Mathematics.Complexity.Karp21MichaelLevinGoalExecutionWitnessExact

import DASHI.Mathematics.Complexity.Karp21MichaelLevinObserverCutQuotientBoundaryExact

import DASHI.Mathematics.Complexity.Karp21LevinPrefixFreeCookCodingExact

import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact


import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact
import DASHI.Mathematics.Complexity.Karp21LeonidLevinSearchDecisionExact

import DASHI.Mathematics.Complexity.Karp21PartitionSparseCutBidiExact

import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact

import DASHI.Mathematics.Complexity.Karp21CookStrictWordCanonicalReencodeExact

import DASHI.Mathematics.Complexity.Karp21StrictSATBoundedCertificateNPBoundaryExact

import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact

import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphWordBoundaryExact

import DASHI.Mathematics.Complexity.Karp21WeightedMaxCutFixedNoGraphExact

import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact

import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact

import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact

import DASHI.Mathematics.Complexity.Karp21EncodedFixedGraphWordsExact

import DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact

import DASHI.Mathematics.Complexity.Karp21CookConsistencyComparisonClockExact
import DASHI.Mathematics.Complexity.Karp21CookUnaryIndexWordBoundExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact

import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact

import DASHI.Mathematics.Complexity.Karp21StrictSATConcreteRunBidiExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryPayloadValueExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact

import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact

import DASHI.Mathematics.Complexity.Karp21GammaGoldenEverything

import DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact

import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact

import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphEndpointOrderExact

import DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact

import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictLexExact

import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictAfterExact

import DASHI.Mathematics.Complexity.Karp21FinDecoderIndexBidiExact

import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact

import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact

import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorPremisesExact

import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorCompleteExact

import DASHI.Mathematics.Complexity.Karp21OriginalGammaGraphWordFieldsReplayExact

import DASHI.Mathematics.Complexity.Karp21PositiveThresholdGammaExact

import DASHI.Mathematics.Complexity.Karp21BinaryFinMaterializationCostExact

import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact

import DASHI.Mathematics.Complexity.Karp21BinaryRuntimeEverything

import DASHI.Mathematics.Complexity.Karp21CanonicalParsedGraphAcceptanceExact

import DASHI.Mathematics.Complexity.Karp21OriginalGammaCompleteGraphParserExact
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGammaFrameExact

import DASHI.Mathematics.Complexity.Karp21FinFreeE20RawValidatorAgreementExact
import DASHI.Mathematics.Complexity.Karp21FinFreeAllRawValidatorAgreementExact
import DASHI.Mathematics.Complexity.Karp21FinFreeGammaGeneralSparseBudgetExact
import DASHI.Mathematics.Complexity.Karp21FinFreeRawReaderSparseBudgetExact
import DASHI.Mathematics.Complexity.Karp21FinFreeAllWordDecoderAgreementExact
import DASHI.Mathematics.Complexity.Karp21FinFreeAllGammaSuccessAgreementExact
import DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact
import DASHI.Mathematics.Complexity.Karp21FinFreeChronologicalConsistencyBidiExact
import DASHI.Mathematics.Complexity.Karp21FinFreeActualPairwiseConsistencySameExact
import DASHI.Mathematics.Complexity.Karp21FinFreeActualSparseScoreAcceptanceExact
import DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateCanonicalExact
import DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateWordVerifierSameExact

import DASHI.Mathematics.Complexity.Karp21CliqueComplementUpperTriangleWordExact

import DASHI.Mathematics.Complexity.Karp21CliqueComplementSameGraphWordExact

------------------------------------------------------------------------
-- Conway / C3 / primorial on the updated original Karp head.
-- Structural recursion, strict original gamma word codec, factor address,
-- and actual C3 cube -> trit-function algebraic transport.
------------------------------------------------------------------------
import DASHI.Mathematics.Complexity.Karp21ConwayTotalChainExact
import DASHI.Mathematics.Complexity.Karp21ConwayTetrationSameObjectExact
import DASHI.Mathematics.Complexity.Karp21ConwayGammaChainCodecExact
import DASHI.Mathematics.Complexity.Karp21ConwayPrimorialGammaAdapterExact
import DASHI.Foundations.ConwayC3SameObjectCodecExact

import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact

import DASHI.Mathematics.Complexity.Karp21N21SameWordCountedAcceptanceExact

import DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact

import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGraphComparisonEnvelopeExact

-- Native bit-weighted original-word comparison envelope (not a machine receipt).
import DASHI.Mathematics.Complexity.Karp21N21BitWeightedComparisonEnvelopeExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact
import DASHI.Mathematics.Complexity.Karp21GammaBinaryEqualitySameValueExact
import DASHI.Mathematics.Complexity.Karp21BinaryWordEqualityPrimitiveExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordNumericalWeldExact

import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordValidityExact

-- K05: original/native signed gamma all-word acceptance equivalence.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedAllWordValidityExact

-- K05: conservative two-pass signed gamma inspection schedule.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedInspectionClockExact

-- K05: native ripple-carry sum and concrete linear inspection clock.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact

-- K05: proof-side Nat value semantics of executable bitwise ripple adder.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact

-- K05: executable two-lane binary signed-weight fold and total invariants.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact

-- K05: bit-native signed score vs original-shaped sign/magnitude threshold.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact

-- SSP/FRACTRAN sign projection, lossless binary residual, and no-go.
-- Research crosswalk only; the actual N21 executable remains bit-native.
import DASHI.Mathematics.Complexity.Karp21SignedSSPOrientationNoLosslessExact

-- N21: decode original strictly positive gamma(W) as binary W, not W+1.
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact

-- N21 binary-prefix trie identity sharing; equivalence and tape clock remain open.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeEndpointPrefixTrieExact

import DASHI.Mathematics.Complexity.Karp21BinaryNativeMultiplicityScaleExact
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorExact

-- K05: source-written all-word equivalence of grouped and original binary signed ledgers.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorSemanticExact

-- SSP sign-inversion operation reuse on the original signed Karp factors.
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedTraceFactorC2Exact

-- Source-written first-enabled FRACTRAN cache/step invariance.
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

-- Reuse PR #1129 original executable verifier-code refinement for typed N21.
-- Code/size transport is exact; a polynomial clock must be supplied separately.
import DASHI.Mathematics.Complexity.Karp21FractranPvsNPVerifierCodeTransportExact

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

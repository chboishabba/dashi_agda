# Karp-21 / FRACDASH — actual mathematical cut, no wrapper inflation (9 Nov 2026)

**Source of truth:** PR #1474, `chatgpt/conway-karp-gamma-weld-20261106`; original Karp PR #1445; original P≠NP PR #1129. Refer to `Karp21FRACDASHMachineMaxCut20261109.md` for historical notes. This document records what must be **implemented and checked** before any gate is called closed.

## Why the apparent stalled progress?

Previously the programme repeatedly:
(1) introduced representation/observation wrappers around an unchanged runtime,
(2) proved only individual syntax/semantic equivalence or finite test agreement,
(3) imported source-written Agda declarations without obtaining exact-head Agda 2.9 kernel evidence,
(4) promoted the next layer of that same dependency as a newly discovered terminal lemma.

An Agda import is not a kernel receipt. A source-level Nat observation is not a polynomial bit-machine computation. High-level step count ≤m+1 is not a bound on the time used per step; a gamma field of L bits may denote a Nat of size Θ(2^L) when materialized as unary.

## Actual new implementation, NOT merely a wrapper

- `Karp21NativeUnsignedEndpointBitReaderExact.readGammaNatLE`: **executable** gamma(n) reader returns LE binary `n` from actual gamma(n+1) scanner plus binary predecessor (zero is allowed for n,m,u,v). Does not evaluate original Nat gamma. Proof candidates `nativeUnsignedEndpointSameOriginal`, `unsignedEndpointFrameSameOriginal`, `predecessorPreservesBitWidth`, `unsignedEndpointResultWidth`.
- `Karp21NativeBinaryEndpointRawEdgeStreamExact.readOneBinaryRawEdge`: **executable** same-wire u,v,w parser stores **two binary endpoint registers and actual signed binary token**. `oneBinaryEndpointRawEdgeSameOriginal`, `binaryEndpointRawEdgeStreamSameOriginal` source-write original raw-edge/cursor equivalence for all words and Nat count m (the count remains an unpaid runtime seam).
- `Karp21NativeBinaryEndpointValidatorExact.validNativeBinaryEdges`: **executable** bit-only u<v<n plus strict lex ordered original pair policy, consuming actual `Compare.compareLE`; `nativeStrictLessNumerical` source-writes exact numeric reflection against Nat Boolean strict order. Full original-list validator weld remains open.
- Existing `Karp21NativeWholeWordAcceptanceExact.karpFractranDecodePreservesAcceptance` is SOURCE-WRITTEN semantic equality against the **FIN-FREE ORIGINAL** word/cert verifier, not a binary-header/endpoint runtime and not a typed verifier + polynomial clock.
- Existing `Karp21BinaryNativeThresholdNumericalExact.compareLENumericalCorrect`, `Karp21NativePositiveThresholdNumericFrameExact.nativePositiveThresholdParserSameOriginal`, `Karp21NativeLedgerOriginalRawScoreExact.nativeSignedLedgerIntegerEqualsOriginalRawSparseScore` source-write actual arithmetic/parser/ledger semantics. They need kernel checks; they should NOT be listed as brand-new unpaid mathematical definitions.

**Verification status:** Exact-head Agda 2.9/parallel_checker **NOT RUN**. Source-written only. Independent finite Python differential of the new gamma endpoint value/suffix parser: 132,271 cases PASS; of the binary strict edge validator versus original numeric edge order: 19,440 cases PASS. The committed reproducible `scripts/check_karp21_binary_endpoint_cut.py` covers both and is in focused preflight. Finite testing is not a theorem.

## Maximum-cut leaves with dependency/closure criteria

| Priority | Exact next declaration (PROPOSED unless explicitly noted existing) | Source action / theorem contract | Why still open |
|---|---|---|---|
| B1 | `nativeBinaryStrictAfterSameOriginal` | Prove bit-only `strictAfterBinary` agrees with original `Graph.strictAfter` on *valueLE-observed* u,v,previous for all words, including padded zeros | `nativeStrictLessNumerical` exists SOURCE; bridge to original `NatP._<?_`/ `NatP._≟_` decision branches not yet inhabited |
| B2 | `nativeBinaryValidRawEdgesSameOriginal` | Structural induction that `validNativeBinaryEdges n previous edges ≡ Original.validRawEdges (valueLE n) (originalPrevious previous) (originalEdgeListObservation edges)` | Requires B1 plus `nativeStrictLessNumerical`; source true edge-list constructor and previous history |
| B3 | `nativeBinaryGraphHeadersSameOriginal` | Replace `Gamma.readGamma` of both original n and m by `readGammaNatLE`, preserving original all-word cursor and malformed rejection WITHOUT executing Nat reconstruction | Native one-token reader exists; entire header control flow not transported |
| B4 | `nativeBinaryCountBudgetSameOriginal` | On binary m, compare *3m* to remaining input bit length with source-correct bit operations BEFORE any m-loop, rejecting astronomically large counts | Existing original checks Nat `m*3 ≤ length remaining` and loops m times; new raw-edge stream still accepts Nat m |
| B5 | `nativeBinaryEndpointHistorySameOriginal` | Executable binary vertex equality (actual `Compare.compareLE` equality) and original endpoint-label chronology, with numeric reflection | Existing `endpointConsistent` uses Nat equality; binary strict validator alone does not pay history |
| B6 | `nativeGraphEndpointsConsumeInputBits` | Build a **whole** native graph reader using B1–B5, signed native weights/threshold and original strict validation; show `nativeWholeBitGraphWordSameOriginal` for all graph words, including truncated, invalid, zero-threshold and extra-suffix input | This is the actual remaining P0-B/P0-F source-to-runtime transport, not merely a one-token lemma |
| D1 | `karpFractranWholeWordInitialStateSameOriginal` | Construct initial parsed native binary state from B6 and original graph/certificate; malformed parse rejects; no unknown paired-edge oracle | Current `Cursor.State` holds Nat endpoint addresses |
| D2 | `karpFractranFirstEnabledSameVerifierStep` | On SAME B6 whole-word state, original independent step/halt/reject, ordered advance/finish/reject, threshold terminal and cached-priority equality | `karpFractranFirstEnabledSameParsedRawVerifierStep` exists SOURCE only for already-parsed raw list |
| E1 | `karpFractranTraceRebuildExact` | Prove finite run of D2 reconstructs original selected signed raw-score, endpoint-history, terminal threshold decision and all-word rejection | One-step correctness and score equality are not run/trace reconstruction |
| E2 | `nativeCanonicalTypedSparseVerifierSameWord` | Compose original Fin-free boolean verifier with original typed Fin/Cut sparse verifier on each word/certificate without changing language/certificate | Existing `karpFractranDecodePreservesAcceptance` covers only Fin-free original (SOURCE, kernel OPEN) |
| F1 | `originalNativeBitMachineConfiguration` | Select actual bit-TM tape/cell alphabet, head-motion, representations for n,m,u,v, token widths, ledger, history, frontier and trace | Current pure list/Nat functions are not a costed TM code |
| F2 | `originalBinaryIntermediateWidthsBound` | Bound every decoded address, edge/threshold weight, running P/N lane, count and residual by polynomial in combined original input/certificate bit length | Gamma LE endpoint proof gives per-token bit width, but aggregate allocations/carry/validation not paid |
| F3 | `originalBitTapeStepSimulatesN21Rule` | Relate a finite sequence of actual F1 bit-tape steps to each D2 machine step, with exact head movement and writes | High-level `cursorPotential` ≤ m+1 rule firings is insufficient |
| F4 | `karpFractranBitMachineClockPolynomial` | Produce explicit uniform polynomial `p(length graph + length certificate)`, verify all parser/validator/ledger/history/trace steps and malformed cases from F1–F3 | No F1 source code nor F2/F3 receipt; cannot infer from source inspection work |
| G1 | `originalN21VerifierProgramSameWord` | Concrete F1 code computes exact original `Graph.LiteralN21.verifyCanonicalSparseGraphWord` (or transported proven same-language verifier) | Fin-free/typed observational bridge E2 and bit runtime missing |
| G2 | `originalN21PolynomialVerifierClock` | Instantiate **actual** `PR.polynomialTimeVerifier cost verifies` for a selected, independently justified `PR.PolynomialCostModel` and real bit-TM F4 | Abstract `PR.PolynomialCostModel` fields cannot be populated from extensional equality |
| G3 | `originalN21PolynomialCertificateBound` | Instantiate `PR.polynomialCertificateBound cost canonicalSparseCertificateAdmissible`; reuse existing 2m≤input bound as the mathematical input | Existing bound is there; cost-model field inhabitant missing |
| G4 | `originalN21InNP` | Call existing `karpWeightedMaxCutInNPFromMachineReceipts cost G2 G3` on exact original language | Conditional assembler already exists; G2 and G3 missing |
| P1.1 | `originalE20CostedCompilerSameSource` | Source E20 reduction on original same words and B6/F4 cost, not a new number parser | Signed partition item stream SOURCE only; no costed source compiler |
| P1.2 | `canonicalWindowGlobalCoordinatePlacement` | Original canonical Cell/Bits finite local clauses index SAME flat tableau assignment | `canonicalSameRunCNFPacket` exists, but no global placement |
| P1.3 | `initialEndpointCNF`, `acceptingEndpointCNF`, `acceptingRunToSAT`, `satToAcceptingRun` | Prove one CNF is SAT iff original **accepting run**, including start/final guards and same-row transport | Transition/run CNF packet ≠ accepting-run iff |
| P1.4 | `originalCookLevinBitClockPolynomial` | Bound original clauses/variables widths and full encoded compiler cost on real bit-TM | No original machine F1/F4 |
| P2 | Original E01–E19, N01–N20, `CertifiedKarpNetwork` | Kernel-check each original reduction and original NP membership under SAME G cost model; assemble original 21-problem network | Individual source modules not collectively accepted; P1/G missing |
| P≠NP | `behaviouralSelfSpecializationOriginal`, `strictResourceInequalityOriginal`, `SATNotInP` | A mathematically valid universal deterministic polynomial-time SAT lower bound; code quotation/fixed point by itself is NOT such a proof | **Independent open research problem**, not a consequence of NP completeness or a syntactic diagonalization |

### Highest-alpha next run order

**B1 → B2 → B3/B4 → B5 → B6** is the most direct missing real-machine representation seam. Only then run D1/D2, E1/E2 and F1–F4 to G4. P1 and P2 depend on the same machine/cost receipts. Separately adjudicate old and new Agda transitive imports on exact PR head **before calling any theorem closed**. No CI dependence is required for that; a pinned local Agda 2.9/parallel_checker receipt suffices.

### Do not re-list as missing

`compareLENumericalCorrect`, `nativePositiveThresholdParserSameOriginal`, `nativeSignedLedgerIntegerEqualsOriginalTraceScore`, `nativeSignedLedgerIntegerEqualsOriginalRawSparseScore`, `nativeOriginalGraphWordFieldsSame`, `karpFractranFirstEnabledSameParsedRawVerifierStep`, `karpNativeThresholdDecisionSameOriginal`, `karpNativeParsedRawAcceptanceSameOriginal`, `karpFractranDecodePreservesAcceptance`, and the parsed-raw `karpFirstEnabledStepStrictPotential` have already been source-written. They may contain Agda errors and must be checked; **source-written is not kernel-closed**.

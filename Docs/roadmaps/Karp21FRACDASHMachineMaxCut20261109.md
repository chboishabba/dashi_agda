# Karp-21 / FRACDASH compiled-machine maximum cut — 2026-11-09

## Governance and sources

This is a workstream of the **original Karp-21 N21 graph-word and sparse-certificate verifier**, not a replacement decision language or a standalone NP proof.

* Primary Karp owner: PR #1445 and its original same-word, rawSparseScore, gamma, certificate, E20/Cook–Levin and Karp-21 owners.
* Integration: PR #1474, branch `chatgpt/conway-karp-gamma-weld-20261106`.
* Reuse: `chboishabba/FRACDASH` (`architecture.md`, `BRIDGE_CORRECTNESS.md`, `DA51_BELOW_SHARD_CONTRACT.md`, and `formalism/GenericMacroBridge.agda` / `BridgeInstances.agda`).
* Earlier DASHI symmetry and residual interfaces: `MonsterSSPFractranProjection`, `SSP15FractranCompression`, `VerifiedFractranCrankPipeline`, original signed SSP owners.
* Attribution: Conway FRACTRAN; Cook/Levin NP and compiler; Karp's 1972 reductions; Elias gamma coding; the preceding FRACDASH and original DASHI authors/owners. Do not describe reuse as a new invention.

**Golden rule:** Agda source is the target of adjudication. Source-written terms are **not** kernel-accepted until exact-head Agda 2.9 / parallel_checker receipts. Do not infer P != NP from a Karp-21 reduction network; the independent SAT lower bound is missing.

## Architecture and current deliverable

Original N21 graph/certificate words
→ native binary gamma, endpoints and selected signed edge tokens
→ binary-native two-lane ledger and operation-class factoring
→ **FRACDASH-like ordered guarded signed-delta IR**
→ optional cached first-enabled priority frontier
→ binary output / original Boolean verifier
→ original `PR.InNP`, E20, Cook–Levin and Karp-21 reductions.

### New source-written Agda

`DASHI/Mathematics/Complexity/Karp21FractranPriorityFrontierExact.agda` is `--safe` and defines a parameterized compiled machine over original-state and rule types:

* `populate`: initial ordered list of rule guards.
* `refreshEntry` / `refreshCache`: recompute an affected rule's guard and reuse the unaffected cached bit.
* `refreshEntryCorrect`: valid guard reuse follows from the **explicit independent-rule stability premise**.
* `refreshPopulationCorrect` / `refreshStoredCorrect`: refreshed guards agree exactly with a full evaluation.
* `firstPopulatedCorrect` / `firstRefreshedCorrect`: unchanged FRACTRAN first-enabled priority, including halting.
* `cachedStepCorrect`: same selected operation and successor/halt as a fresh direct execution.

No theorem assumes all rules commute, that priority can be reordered, or that a syntactic disjointness test proves independence without its stability lemma. Imported by the existing `Karp21BinaryRuntimeEverything` and `Karp21Everything`; Golden referee includes it.

**Acceptance:** SOURCE WRITTEN; exact-head Agda/parallel_checker receipt OPEN. This is a GENERIC cache theorem, **not** an instance for N21 and not a bit-machine clock. No runtime benchmark is claimed for this source.

### Prior relevant completed/source-written constituents (do not duplicate)

* `Karp21BinaryNativeSignedLedgerExact`: actual binary two-lane accumulation, source-written numeric observations.
* `Karp21BinaryNativeSignedTraceFactorExact`, `...SemanticExact`, `...C2Exact`: actual signed-token classes, multiplicity scaling, factor replay, semantic equivalence to the native ledger and sign flip.
* `Karp21BinaryNativeEndpointPrefixTrieExact`: actual bit-address trie with conflict detection; original all-word equivalence OPEN.
* `Karp21GammaBinaryNativePositiveThresholdExact`: original strictly-positive gamma threshold's successor correction.
* Original N21 all-word typed/Fin-free same-word and primitive comparison envelopes exist at source level.

FRACDASH's DA51 corpus reports 15,658 raw bytes → 9,275 aggregate → 5,387 below-shard with exact reconstruction **on that corpus**. This demonstrates operation/trace reuse, not a guaranteed generic N21 compression or complexity improvement. The separate 256 × 1,025-bit signed-weight example reduced arithmetic stages but did not improve total accounted key+addition work.

## Phases, deliverables, exact remaining lemmas

| Phase | Gate | Exact owner/target | Status |
|---|---|---|---|
| P0.0 | Compiled priority | `refreshStoredCorrect`, `firstRefreshedCorrect`, `cachedStepCorrect` | SOURCE WRITTEN generic; Agda receipt OPEN |
| P0.1 | Original signed score | `karpSignedIRSameOriginalSparseScore` — same original selected edges, original gamma values, two binary lanes | OPEN original-object weld |
| P0.2 | N21 rule implementation | Construct N21-specific `State`, `Rule`, `enabled`, `apply`, `affected`, independence witnesses | OPEN |
| P0.3 | First-enabled simulation | `karpFractranFirstEnabledSameVerifierStep` — instantiate the generic machine and match original N21 next step including rejection/halting | OPEN |
| P0.4 | Readout/acceptance | `karpFractranDecodePreservesAcceptance` on **all** original graph and certificate words, malformed included | OPEN |
| P0.5 | Reproducible trace/residual | `karpFractranTraceRebuildExact` with lossless decoder or sufficient decision-preserving quotient, and actual trace replay | OPEN |
| P0.6 | Cost model | `karpFractranBitMachineClockPolynomial` with program size, guard scans/frontier updates, bit widths, writes, allocations, pointer/tape motion, trace/residual cost | OPEN |
| P0.7 | Original graph weld | `trieAdmitIffOriginalHistoryConsistency`; `nativeGraphEndpointsConsumeInputBits`; `nativeSparseScoreSameOriginalRawSparseScore`; `nativeN21SameWordAndClock` | OPEN |
| P0.8 | Membership | Construct the original N21 `PR.InNP` via its actual polynomialTimeVerifier / witness bound | OPEN |
| P1.1 | E20 | Uniform original complete-graph word compiler and all-word clock (including malformed cases) | OPEN |
| P1.2 | Cook–Levin | Original Cell/Bits accepting-run compiler, canonical specialization and polynomial clock | OPEN |
| P2 | Historical Karp network | E01–E19 reductions, N01–N20 membership and `CertifiedKarpNetwork` | OPEN |
| P3 | Referee | Agda 2.9 exact-head Golden plus original `parallel_checker` receipts, no CI dependence | OPEN |
| Independent | P != NP | SATNotInP lower bound; **not implied by any above gate** | OPEN |

## Mathematical requirements for N21 instantiation

For state `s`, ordered rules `r_i`, and guard `g_i`, the compiled target must choose
`min { i | g_i(s)=true }` and update `s` by the selected rule's signed delta.
No rule enabled means halt, with the original rejection/acceptance distinction maintained by the decoder.

For a transition `s → s′`, a cached guard may be reused only with

`affected(r,s,s′)=false → g_r(s)=g_r(s′)`.

This is **stronger than** merely asserting that a rule's syntactic lane set is disjoint from a changed-lane set unless the source-specific dependency lemma validates the relation. Prioritized selection must observe the smallest enabled index after refresh.

Signed magnitude is kept in binary registers. The formal exponent-vector semantics does not license constructing huge prime-power integers. Finite SSP15/Monster projections require explicit residual data or an observational congruence; a prime dividing a group order is not an automatic quotient, nor an optimization receipt.

## Explicit bit cost and comparison experiment

For input bit length `L`, witness length `W`, `R` rules, and trace steps `T`, charge:
program construction and stored rule bits; every parsed input bit; guard threshold comparisons and dependency refresh; address-trie traversal; signed binary add/scale; output and residual bits; allocations and memory access; on-tape head movement for the chosen Turing machine.

A short FRACTRAN program or collapsed DA51 shard does **not** establish polynomial `T`, bounded intermediate valuation bit widths, or a polynomial physical machine clock. Establish an explicit polynomial in `L+W` under the original cost interface. Compare full scan, cached priority-frontier, and original binary verifier under the same input and accounting rules, including adverse unique-weight / all-rules-affected controls.

## Next highest-alpha precise coding cut

1. Instantiate `Machine` with a **real N21 machine state** retaining input cursor, gamma suffix, endpoint trie/history, binary signed ledger, current threshold, witness cursor and explicit halt/accept status.
2. Define rules corresponding to the existing binary-native parser/validator operations; do not replace the source grammar.
3. Prove each `affected` false case by actual lane dependence or conservatively mark it true. Only then apply `cachedStepCorrect`.
4. Prove original-step simulation and trace readout, including malformed and halting branches.
5. Build a concrete bit-tape implementation and its all-word polynomial clock; instantiate original `PR.InNP`.

No synthetic N21 result should be promoted from the generic theorem.

### Bounded independent regression — 2026-11-09

`script/check_karp21_fractran_priority_frontier.py` (actual tracked path: `scripts/check_karp21_fractran_priority_frontier.py`) is included in `referee_karp21_maxcut.sh`. Executed independently here on 38,860 finite guard/frontier cases for 1–3 Boolean lanes and 0–3 ordered rules, with exact agreement between incremental cache refresh, full recomputation, and first-enabled priority; it also rejects an affected-rule stale-cache negative control. **These are finite Python checks, not Agda kernel receipts, not original N21 tests, and not evidence of a bit-machine polynomial clock.**


## 2026-11-09 continuation — original N21 endpoint/score guarded machine vertical slice

New original-owner integration `DASHI/Mathematics/Complexity/Karp21FractranN21EndpointScoreStepExact.agda` **actually imports** `Karp21FinFreeRawSparseWordVerifierExact.endpointConsistent`, `Karp21BoolGoldenExact.boolEqual`, the real `Karp21GammaBinaryNativeSignedExact.SignedMagnitudeBits`, the executable `Karp21BinaryNativeSignedLedgerExact.insertSigned`, and the FRACDASH-style `Karp21FractranPriorityFrontierExact.Machine`.

The source-written `N21Edge` instantiation fixes one original edge's u/v, certificate labels a/b, original chronological endpoint history and decoded binary signed weight. It exposes a **genuine priority-ordered two-rule machine** (`advance`, then `reject`) with first-rule guard equal to the original endpointConsistent checks and continuation status. Its rule action updates the binary positive/negative ledger if and only if original `boolEqual a b` is false. The fallback rejects. `karpFractranFirstEnabledSameN21EdgeStep` states exact same-step on this **one-edge original-guard score phase**. `unaffectedStable` is proved by case analysis on the concrete status-change dependency, and `scoreOnlyUnaffected`/ `scoreOnlyGuardStable` certify score-only binary updates cannot alter fixed endpoint guards. `karpN21CachedScoreUpdateSameStep` transports the generic first-enabled cached-step theorem to this concrete frame.

This is strictly narrower than `karpFractranFirstEnabledSameVerifierStep` on ALL original N21 words. The original `rawSparseScore` recursively validates the entire history and sums `Graph.RawEdge.weight : ℤ`, while this local machine consumes one native signed bit token. **Unpaid:** original gamma signed token value/suffix equality; one-edge raw signed-ℤ to native lane correspondence; induction over whole edge list and 2m certificate; parser malformed/suffix behavior; exact acceptance and trace replay; fully costed bit-machine verifier; `PR.InNP`. The local state does not assert a global graph cursor or output acceptance.

The module is imported by both original Karp roots and checked by `referee_karp21_maxcut.sh e20/all`; a bounded differential `scripts/check_karp21_fractran_n21_edge.py` is run in preflight. A local independent source-shaped Python reproduction passed **13,440** cases (two vertex addresses, both labels and live statuses, five signed weights, endpoint histories of length up to two, two small ledger lanes); conflicting-label negative control passed. This evidence **does not** typecheck Agda or prove the original word-level theorem.

**Phase ledger:** P0.2 = source-written concrete endpoint/score phase, **not full graph rules**. P0.3 = local first-enabled same-step SOURCE, full `karpFractranFirstEnabledSameVerifierStep` OPEN; P0.6 bit clock OPEN; all downstream P0–P3 remain OPEN. Exact-head Agda 2.9 and parallel_checker receipt not obtained.


## 2026-11-09 — Full original raw-score selected-trace reconstruction and all-word acceptance (SOURCE ONLY)

**New owner:** `DASHI/Mathematics/Complexity/Karp21FractranOriginalRawTraceReplayExact.agda`.

The runtime `rawSelectedTrace` traverses the ORIGINAL `Graph.RawEdge` list and the original **exactly two certificate bits per edge**, applies the original `Runtime.endpointConsistent` (including chronological history extensions) and `Boolean.boolEqual`, and emits just those original signed `ℤ` weights whose labels differ. It rejects inconsistent or short/long certificate lists with `nothing`. `replayOriginalSignedTrace` folds the original signed weights. Proposed source-written `rawSelectedTraceRebuildsOriginalScore` proves the full all-raw-list equality `decodeTraceScore (rawSelectedTrace edges bits history) ≡ Runtime.rawSparseScore edges bits history` via structural induction, including malformed bit lengths, all signed weights, and arbitrary histories.

The same source additionally defines `verifyOriginalGraphWordByTrace` using **the actual original** `Runtime.readRawGraphWord` rather than a replacement graph parser; `karpOriginalRawTraceAllWordAcceptance` is a source-written theorem asserting Bool equality against `Runtime.verifyFinFreeSparseGraphWord` for *every original graph-word and certificate bitword*. This is a trace/replay equality at the ORIGINAL `ℤ` representation, not native signed-gamma value equivalence, a binary FRACTRAN runtime, or a bit-machine complexity result.

**Independent executable evidence:** `scripts/check_karp21_fractran_original_raw_trace.py` reproduced the literal source-level branch order and checked **449,895** bounded raw edge/certificate cases (0–3 edges, small signed weights including negative, conflicting endpoint histories and malformed certificate lengths): 8,257 accepted, 441,638 rejected, all replayed decisions/scores agreed. This is a Python transcription of the original raw-language semantics, not direct execution of Agda, and does not test the complete all-word parser. Added to existing Golden roots and referee.

**Exact authority:** source-written proof candidate, **no Agda 2.9 kernel receipt**. The full target `karpSignedIRSameOriginalSparseScore` is STILL OPEN because the native binary sign/magnitude token values and gamma suffix must be welded to the original `ℤ` weights. The stronger `karpFractranFirstEnabledSameVerifierStep` is ALSO OPEN beyond the preceding one-edge original-guard instance. All-word original-ℤ trace acceptance is source-written but native-binary all-word acceptance is not. Full original N21 bit-machine clock, `PR.InNP`, E20, Cook–Levin and remaining Karp-21 reductions/memberships remain open.

**Next tight cut:** prove the actual original `readSignedGamma` / `readRawEdges` to native binary token value-and-suffix equivalence; use a mathematical signed-lane observation bridge to map replayed native selected tokens to this exact original signed selected trace; then instantiate a true bit-tape step bound and the original `PR.InNP`.


## 2026-11-09 continuation — original typed N21 all-word trace composition and paired binary projection

New source-written `Karp21FractranOriginalTypedTraceAcceptanceExact.agda` composes the existing source-owned `Karp21FinFreeAllWordDecoderAgreementExact.n21FinFreeVerifierSameWord` and `Karp21FractranOriginalRawTraceReplayExact.karpOriginalRawTraceAllWordAcceptance`. Its declaration `karpOriginalTraceSameTypedN21AllWords` states that the original signed-ℤ selected-trace evaluator has exactly the same Bool as `Graph.LiteralN21.verifyCanonicalSparseGraphWord` for all original graph words and certificate words, malformed included. **Composition of source-written theorems only, Agda kernel receipt not received.**

New `Karp21FractranPairedBinaryTraceExact.agda` retains each original `Graph.RawEdge` together with its corresponding actual `SignedMagnitudeBits`, preserving the original endpoint `Runtime.endpointConsistent` and `Boolean.boolEqual` selection and certificate-history update. `pairedTraceProjectsToOriginal` source-writes original signed-ℤ trace recovery for every aligned paired raw-edge list, arbitrary original history and certificate, with rejection exact. `pairedTraceOriginalScoreExact` composes this projection with the original `rawSparseScore` reconstruction. Native tokens can be projected for ledger replay without losing pairing identity. Neither theorem falsely presumes token magnitude/value equals the original signed-ℤ weight: **that equality is still a separate, open signed-gamma graph-reader weld.**

All sources are imported into both original Karp roots, and the exact-head referee checks each of them in e20/all. Local Python scripts already mounted in the runtime were directly executed this continuation: raw signed-score trace 449,895/449,895, original edge-guard phase 13,440/13,440, and priority frontier 38,860/38,860; passing tests are NOT Agda receipts.

**Remaining exact maximum cut**: (i) original graph signed-gamma `readRawEdges` → native binary signed token/suffix equality for all input words; (ii) original signed weight ↔ native signed value and threshold `P ≥ N+W` equality; (iii) use the paired full-edge trace to prove the actual native binary ledger and full FRACDASH step agree with `rawSparseScore` and the original typed N21 Bool for all words; (iv) bit-TM clock with parsing, update, selection, storage, motion and residual costs; (v) original `PR.InNP`; (vi) E20 and Cook–Levin; (vii) E01–E19/N01–N20 and `CertifiedKarpNetwork`; (viii) exact-head Agda 2.9/parallel_checker. These remain OPEN. The new source is *not* a verified NP-completeness proof.


## 2026-11-09 — P-vs-NP PR #1129 cross-pollination: executable verifier code transport

**Audited original `chboishabba/dashi_agda` PR #1129** (`agent/pnp-maxcut-20261012`, observed head `730ec95ce0442b8ab48a17a3cc9a3d1307ba8c76`) and the branch's existing `PNotEqualsNPExecutablePolynomialCostRefinementExact`, `PNotEqualsNPClayCoreExact`, `PolynomialReductionExact`, and original `Karp21SparseGraphWordNPBoundaryExact`. The P-vs-NP branch already distinguishes extensional `polynomialTimeVerifier` from executable finite code, actual halting versus estimated upper bound, and independent `SATNotInP` lower-bound obligations. **Do not mistake its behavioural self-specialization interfaces or Cook quotation boundaries for a proved SAT lower bound.** The existing Karp NP boundary already explicitly requires a physical verifier clock and certificate-bound witness to construct `PR.InNP`.

**New actual reuse, not a duplicate cost model:** `DASHI/Mathematics/Complexity/Karp21FractranPvsNPVerifierCodeTransportExact.agda` imports the SOURCE P-vs-NP `ExecutableVerifierCode` carrier, original typed N21, and this branch's all-word original signed-ℤ trace theorem. `karpTraceCodeRealizesOriginalTypedN21` transports a real concrete code, its interpreter, and its `codeSize` field from original trace verification to the actual typed N21 verifier. `karpTypedCodeRealizesOriginalTrace` transports the other way. Both update only `runExact` by transitivity/symmetry of the source-owned all-word Boolean equality; they do **not** synthesize a tape program or clock. `karpTraceRefinedToOriginalTyped` transports a P-vs-NP `ExecutablePolynomialTimeVerifier` *only when a separate original typed-verifier polynomial-time witness has been supplied*. This refuses to postulate that extensional code or numerical comparison count equals a bit-Turing-machine runtime.

The new module is imported by the original `Karp21Everything` root (not marked `--safe`, matching the historical P-vs-NP import closure) and checked by `referee_karp21_maxcut.sh e20/all`. The previous `Karp21FractranPairedBinaryTraceExact` had a missing `sym` import in its all-list proof; that import was repaired. Exact-head Agda 2.9 and `parallel_checker` unavailable here.

**Actually executed** bundled Python scripts in this working container this continuation: `check_karp21_fractran_priority_frontier.py` 38,860 PASS, `check_karp21_fractran_n21_edge.py` 13,440 PASS, `check_karp21_fractran_original_raw_trace.py` 449,895 PASS. These finite source-shaped tests are not Agda kernels or end-to-end N21 binary parser tests.

**Exact remaining maximum cut, unchanged by code-transport:** source signed-gamma `readRawEdges` and native bit-token value/suffix alignment; binary two-lane numeric representation equal to original signed-ℤ `rawSparseScore`; actual complete N21 FRACTRAN first-enabled original machine; native all-word acceptance and residual trace reconstruction; concrete bit-machine execution/bit width/heap/tape/head/priority-frontier polynomial cost; `PR.polynomialTimeVerifier` and original `PR.InNP`; E20, Cook–Levin original Cell/Bits and remaining E01–E19/N01–N20 network; independent behavioural self-specializer and resource fixed point to derive `SATNotInP` in separate P-vs-NP lane. Source written ≠ kernel accepted ≠ Clay result.

**Provenance:** Stephen Cook, Leonid Levin, Richard Karp, Elias gamma/Conway FRACTRAN; reuse of repository's original PR #1129 and PR #1445 authorship and FRACDASH compiled-machine work. No ESD paths touched.

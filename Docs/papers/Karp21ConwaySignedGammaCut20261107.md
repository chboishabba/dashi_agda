# Karp-21 / Conway: signed-gamma exact-head cut (2026-11-07)

Primary owner: PR #1474, `chatgpt/conway-karp-gamma-weld-20261106`, based on the original Karp-21 reduction transport.

## Source-written this continuation
- `Karp21GammaBinaryNativeSignedInspectionClockExact`: a conservative bound on two explicit full-input inspection schedules, `<=2(1+L)`. This is **not** an exact cost of `readSignedBinary`, because its splitter actually scans the returned successor payload, not the original entire word. It also excludes copying, list allocation and tape-head travel.
- `Karp21GammaBinaryNativeSignedAllWordValidityExact`: proves the original signed-gamma decoder and executable native signed-gamma decoder have the same accept/reject behavior on every literal input word, including malformed, incomplete and suffix-bearing words. It reuses the original unsigned gamma all-word weld. Kernel acceptance **not received**.
- Both owners imported in `Karp21Everything` and `Karp21BinaryRuntimeEverything`.
- `scripts/check_karp21_signed_gamma_allwords.py`: independently enumerates all 16,383 words of length <=13, comparing original and binary-native integer, suffix and rejection. Passing this test is not an Agda receipt.

## Highest-alpha remaining cut (do not duplicate existing owners)
1. **K05-SIGNED-VALUE**: formally relate sign/magnitude payload value to original `unzigzag` for arbitrary decoded gamma words. Bounded Python agreement is not an Agda value theorem.
2. **K05-SIGNED-COST**: exact recursive inspection count and bit-operation budget for the actual `readSignedBinary` payload, plus signed multiword addition and threshold comparator.
3. **K05-GRAPH-COST**: instantiate the original complete gamma graph-word parser and fin-free N21 verifier in a bit-native machine, with all-word polynomial tape cost, not just weighted comparison count.
4. **K06-N21**: combine existing all-word semantic equivalence, certificate-length bound and the actual machine clock into a native `PR.InNP` instance.
5. **K03/E20**: prove original signed PARTITION-to-MAX-CUT transducer preserves acceptance and runs in polynomial binary-machine time on every input.
6. **K06-COOK-LEVIN**: finish source-native uniform guarded run/CNF construction and clock; re-use selected Cell/Bits owners.
7. **K01/K02/K04/K07**: exact-head Agda acceptance of Conway total evaluator, original wire codecs and C3 carrier/character transports, and `parallel_checker` receipts.
8. **KARP-21**: instantiate remaining edges and all 21 NP-memberships; any P != NP implication additionally needs a separate genuine SAT lower-bound theorem.

## Verification boundary
New Agda declarations are source-written candidates, **not kernel-certified**. No Agda or `parallel_checker` executable was found in the execution environment, and no CI receipt is inferred. No complete `PR.InNP` or NP-completeness certificate is asserted.


## 2026-11-09: newest-PR re-audit and K05 binary adder

Re-audited the original Karp-21 PR #1445 and the integrated Conway PR #1474. Original sparse-N21 semantic iff and all-word verifier equality are existing owners; neither should be rewritten. The canonical vertex count is Elias-gamma encoded, so the 2m-bit sparse certificate remains essential to avoiding exponential witness allocation.

New source-written Agda on the same Conway-Karp branch:
- `Karp21BinaryNativeRippleAdderExact`: executable Boolean ripple-carry addition with eight exhaustive locally correct full-adder cases, structural step-count function, and `additionInspectionLinear` bound `work(xs,ys) <= 1 + length(xs) + length(ys)`.
- `Karp21BinaryNativeRippleAdderValueExact`: `valueLE` mathematical observation, ring-normalized `carryAlgebra`, recursively source-written `addCarryValue` over arbitrary source word lengths and incoming carry, and `addBitsValue` for the actual new bit-native adder. This is a proof *candidate* until Agda accepts it. `valueLE` is not executed by the adder.
- Both files integrated in original `Karp21Everything` and `Karp21BinaryRuntimeEverything`.
- `scripts/check_karp21_binary_native_ripple.py`: independently executed exhaustive reference of all 65,025 pairs of widths 0 through 7; numerical value and counted linear inspection bound passed. Finite Python checks do not prove the Agda statements.

Revised decisive order:
1. **Exact-head compiler:** Agda 2.9/parallel_checker on all new and older owners; fix type or termination failures against the real source. No receipt currently available.
2. **Binary sign arithmetic:** normalize sign/magnitude, give executable subtraction and signed accumulation with a whole-word correctness proof, and transport to the original signed-score definition.
3. **Actual N21 machine:** cost complete gamma graph parser, raw validation, equality, arbitrary-length arithmetic, sparse witness, and rejection on every malformed input. Use a machine model where copy, allocation and head movement are charged; the current structural inspection bounds alone are insufficient.
4. **N21 membership:** instantiate the actual `PR.InNP` from machine semantics, polynomial clock, verifier agreement and 2m certificate size.
5. **E20:** the source-owned signed PARTITION-to-MAX-CUT original graph compiler, all-word semantics and uniform polynomial bit-machine transducer.
6. **K00 Cook–Levin:** exact source Cell/Bits accepting-run/CNF compiler and polynomial clock, then E01–E19 and N01–N20.
7. **P!=NP:** separate SAT lower bound; not implied by the completed representation or NP-completeness chain.

Do not conflate source-written Agda with checked code or a local primitive step count with an actual multi-tape machine cost.


## 2026-11-09 second implementation cut: original-form signed arithmetic

**New executable owners on PR #1474**:
- `Karp21BinaryNativeSignedLedgerExact`: for each native `SignedMagnitudeBits`, append its magnitude to the selected little-endian positive or negative accumulation lane, using the existing ripple adder. No unary integer reconstruction in the executable loop. `insertPositiveValue`, `insertNegativeValue` and the preserved-opposite-lane lemmas use the original adder's source-written value theorem. The whole-input proofs `accumulatePositiveValue` / `accumulateNegativeValue` and empty-ledger specialisations state exact nonnegative totals. Source-level correction to base-case identity orientation included. **No kernel receipt**.
- `Karp21BinaryNativeThresholdExact`: signed threshold comparator on the accumulated two-lane word and the selected native signed gamma magnitude. It reduces `P-N>=+t` to `P>=N+t` and `P-N>=-t` to `P+t>=N`, using the actual bit-native adder and a high-bit-first recursive comparison on little-endian words. There is no unary Nat conversion in the executable path. All-word numeric-order correctness of `compareLE` is **still to be proved in Agda**.
- Both owners imported through the existing original `Karp21BinaryRuntimeEverything` and `Karp21Everything`; no duplicate N21 verifier or graph language.
- Independent exact Python runs: **137,257** signed-token lists (length 0..6 from 7 signed values), and **377,856** signed-score/threshold triples. All matched mathematical integer semantics. Committed reference scripts: `scripts/check_karp21_native_signed_ledger.py` and `scripts/check_karp21_binary_native_threshold.py`. These do not constitute kernel proofs.

**Critical original-object welds still unpaid**:
1. `readSignedBinary` must provably represent the same signed **value and suffix**, not merely accept/reject behavior, as original `readSignedGamma` on *every* input.
2. `compareLE` must be proved equal to the Nat binary-value ordering for **every** bitword, including redundant zeros and differing widths; then threshold comparison must match original signed-score test.
3. Cost the actual `reverse`, ripple addition, persistent-list copies and allocations, all-token repeated accumulation, graph gamma parser, sparse consistency/validation, and certificate scan on a specified **tape** machine. The local inspection costs alone are not a certified whole-machine polynomial clock.
4. Attach the new signed ledger to the literal original graph-edge weighted cut score with original E20 output words and N21 certificate words; verify all signed negative weights, malformed words and threshold conventions.
5. Construct original `PR.InNP`, then the uniform original signed E20 reduction and Cook–Levin Cell/Bits runtime; cover E01–E19, N01–N20 and source-head kernel checks.
6. Keep original SAT lower bound for P!=NP separate; Karp reductions cannot supply it.

**Trust status:** source-written Agda imported, independent Python tests executed, **Agda 2.9 and parallel_checker not available in this execution environment**. These modules are not promoted to checked theorems.


## 2026-11-09 signed SSP/FRACTRAN audit — reuse without exponential runtime

Primary owners inspected:
- `DASHI.Biology.SignedSSPFRACTRANWeaveExact`: fifteen SSP prime lanes, `SignedMultiplicity`, `FibreOrientation`, `negateMultiplicity`, and separate program, execution and normal-form lengths.
- `DASHI.Biology.FRACTRANSSPTransitionExact`: fixed-priority finite step examples, not an arbitrary binary integer arithmetic implementation.
- `DASHI.Combinatorics.SSP15FractranCompression`: an outcome quotient or label-plus-residual codec needs a real roundtrip, transition congruence and MDL receipt; a bare fifteen-label compression is not asserted lossless.

New `Karp21SignedSSPOrientationNoLosslessExact.agda` directly reuses the *original* SSP polarity/orientation type and original Karp signed-binary token. It source-writes `binaryOrientationIsSSPOrientation`, `flipMatchesSSPNegation`, `flipBinaryInvolutive`, and a constructive `noLosslessOrientationDecoder` collision: distinct signed binary payloads share `forwardOrientation`. It also constructs the correct lossless `SSPPolarityWithResidual` pair and `sspPolarityResidualRoundtrip` while retaining the entire binary magnitude as residual. This is a semantic/provenance bridge only; it is **not** a replacement for the binary N21 score machine and provides **no compression or step-cost advantage** by itself.

`scripts/check_karp21_ssp_residual.py` passed 4,094 finite signed-token roundtrips over widths 0..10 plus a concrete sign-only collision and mediated-token rejection, using local Python. It is independent of Agda. The new bridge is attached to the original `Karp21Everything` import graph, not the bit-native runtime root.

**Reason for not switching the original N21 runtime to FRACTRAN:** the selected SSP `Nat` multiplicities and prime-power semantics have no admitted all-binary-word simulation or polynomial bit-machine clock. Arbitrary binary weights cannot be reconstructed from one of three orientations (or fifteen prime labels) without a residual. Prime exponent/value expansion could cost far more than the literal bit length. Do not infer constant-time arithmetic from short FRACTRAN source programs.

**Current exact kernel boundary:** the attached local Agda-2.9 receipts at historical Karp PR #1445 heads establish selected historical modules, not all present integration modules. On 2026-11-09 the GitHub connector reported #1445 at `b3915126edd096cd09ce7cc1b1b195e75d9e9e87` and #1474 at `100949a4548aa8b73533c1b24239959c889f252f`, with no workflow runs/statuses returned for either head. New bridge commits remain **SOURCE-WRITTEN**, not kernel-accepted.

**Highest alpha after this audit:** stop adding lossy representation layers. Finish Agda 2.9 exact-head referee diagnostics; prove `readSignedBinary` all-word value/suffix semantics; prove two-lane score to the *original* signed weighted-edge decision; charge actual parser, bitstring copying/allocation, endpoint equality, signed threshold and malformed-input rejection under a concrete binary tape machine; construct original `PR.InNP`; then E20 and Cook-Levin costed original transducers, then E01–E19 and N01–N20. No P != NP lower bound follows from the Karp network.


### Prior-art correction: original StageTwelve non-descent proof

A deeper search located `DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact` on master. Its existing source-owned `signedMagnitudeNonDescentWitness`, `ternaryRelationCellCannotAnswerSignedMagnitude`, `ternaryRelationCellCannotFactorSignedMagnitude` and `signedMultiplicityResidualRoundTrip` already prove the relevant SSP signed-magnitude information-loss and residual recovery phenomenon **for its original relation-cell/SSP Nat carrier**. The new Karp bridge does not discover that fact; its new domain-specific result is `noLosslessOrientationDecoder` for the original binary N21 `SignedMagnitudeBits`, with bitword residual retained exactly. Attribution remains with the original StageTwelve and SSP module authors. Avoid importing the much larger StageTwelve graph into the Karp runtime merely to restate the theorem.

The word "Grothendieck" in StageTwelve refers to the source's finite topology/sheaf construction; it is not by itself a certified group-completion quotient or a polynomial FRACTRAN-to-binary-machine compiler.


## 2026-11-09 N21 original strictly positive gamma threshold correction

Direct source audit of `Karp21FinFreeRawSparseWordVerifierExact.readRawGraphWord` establishes the selected N21 threshold is always `suc threshold` and rejects zero. Actual check is `Int._≤ᵇ_ (+ positiveThreshold) score`. Therefore the intended binary comparison is only `positive >= negative + W`, W >= 1. No general signed threshold is required to execute this particular original verifier.

**Codec bug/gap prevented:** the already constructed `Native.readGammaBinary` returns big-endian bits for `W+1`; feeding those bits directly to a magnitude-only positive threshold comparator would compare against the wrong number. Moreover, `readSignedBinary` interprets a zigzag sign, not the original unsigned positive threshold; it is not a substitute.

New source-written `Karp21GammaBinaryNativePositiveThresholdExact.agda` defines `predecessorLE` for successor bits, `readPositiveGammaLE` with strict zero rejection and suffix retention, the `meetsOriginalPositiveThreshold` specialization and a mathematical `predecessorLEValue` proof candidate. The executable path manipulates only bit lists. It imports in both original Karp roots and is a Golden referee target. `scripts/check_karp21_positive_gamma.py` independently enumerated all 32,767 bitwords of length <=14, comparing original positive gamma numerical semantics and native predecessor result with exact suffix. All passed in local Python.

This is **NOT** an unconditional all-word Agda kernel receipt or the graph-level same-object parser weld. Remaining P0: Agda acceptance; compose the actual gamma field scanner across all original graph headers, edges and threshold; prove original signed-weight numerical value and binary accumulator correctness, plus full bit-tape cost (including copying/allocation and memory head movement); then original `PR.InNP`. E20/Cook–Levin and other Karp edges remain open.


### Exact original Python owner for native threshold (attribution correction)

The binary-positive-threshold algorithm is **already implemented** in `scripts/karp21_native_bitword_sparse_verifier.py`: `successor_to_nat_bits` performs the non-unary successor-to-natural predecessor, `parse_graph` rejects zero W, and `verify_native_sparse_graph` already checks `positive_sum >= negative_sum + graph.threshold`. The new Agda `Karp21GammaBinaryNativePositiveThresholdExact` is a proof-oriented *formal transport of that original implementation* into the selected Agda runtime graph, not a novel replacement. The immediate new obligation is a kernel-accepted all-word equality to this original binary operator plus source-owned numeric gamma and an actual tape-cost proof. The independent local Python test checks a transcription, not a re-execution of the repository source through the GitHub connector.


## 2026-11-09 shared-operation symmetry / SSP / Monster max-cut

The user's SSP/Monster suggestion concerns **operation reuse and symmetry factorisation**, not simply replacing a signed numeral by a fixed prime tag. The existing `DASHI.Foundations.PrimeLaneUnitActionQuotient` has source-owned p7/C6, p11/C10 and p13/C12 unit-action candidates; `DASHI.Combinatorics.FractranComputationEquivalence` requires step/halt/run preservation for a real FRACTRAN representation, and `DASHI.Combinatorics.SSP15FractranCompression` separates quotient outcomes, lossless residuals and transition congruence. Source ownership remains with those modules, and Monster/VOA operations cannot be promoted to an N21 subroutine without an explicit effective encoding and simulation theorem.

Mathematical caveat: a prime p dividing |G| supplies a subgroup of order p by Cauchy's theorem, **not** necessarily a quotient. The Monster is simple, so it has no nontrivial proper quotient. Its SSP prime lanes and group representations can still supply subgroup actions or reusable invariant operations. The p7/C6 surface uses multiplicative units modulo 7 (order 6), which must not be conflated with the additive C7 group.

### Concrete operation-reuse implementation

New `DASHI.Mathematics.Complexity.Karp21BinaryNativeEndpointPrefixTrieExact` is an executable Agda binary-prefix trie: each original gamma successor bitword follows a shared prefix path; repeated endpoint labels are stored on the terminal node, and conflicting labels are rejected. Source-written only: all-word equivalence to the original `endpointConsistent` and bit-Turing-machine costs still open.

New `scripts/karp21_native_prefix_trie_consistency.py` contains an instrumented Python trie and `verify_original_native_word_via_trie`, reusing the **actual original** `karp21_native_bitword_sparse_verifier.parse_graph`, `add_unsigned`, `compare_unsigned` and the same 2m sparse witness and strictly positive W. No new graph-language encoding. Local independent trie-vs-pairwise enumeration: **37,449** histories over four distinct binary addresses and two labels, plus one 1025-bit address and deliberate conflict, all PASS.

`scripts/check_karp21_native_prefix_trie_consistency.py` adds a repository-integration regression: original-versus-trie-backed native verifier over signed graphs, malformed words, 2^1024 vertices, and certificate variants. It additionally checks `sum(endpoint successor bit lengths) <= length(original graph word)` in the tested parsed graphs. This **repository integration regression was committed but not executed in the current offline environment** (no local repository checkout). The focused referee now invokes it and includes the new Agda trie owner.

Resource insight for this concrete implementation: on one successful word, one traversal of each endpoint successor bit gives at most L trie path edges (and at most L+1 allocated nodes). This bound is a **candidate for formal proof** by pairing each trie edge traversal with its distinct source gamma endpoint token bit. It is not yet an accepted Agda lemma. A heap/pointer machine still must price lookup, node allocation, and tape movement: in a pointer-RAM model a trie can have O(L) structural operations; a naive one-tape encoding of the same trie need not have O(L) head movements. Either yields a polynomial clock after an explicit simulation proof.

Compare to existing original O(m^2) endpoint equality-count owners, rather than deleting them. They remain valid for the old algorithm. The optimized trie is a *different implementation of the same decision problem* and needs a checked universal same-word equivalence before promotion to `PR.InNP`.

### Mandatory next exact Agda lemmas
1. `trieAdmitIffOriginalHistoryConsistency`: for all original binary endpoint occurrences (including conflicts), prove trie decision equals the original history comparator decision.
2. `nativeGraphEndpointsConsumeInputBits`: for successful original gamma parsing, sum of lengths of u/v successor bitwords <= |word|; signed weights/count/threshold occupy other positive-length original tokens.
3. `trieMachineStepsPolynomial`: bind an actual selected memory/tape representation, allocate/update cost and bounded head movement to the trie implementation; do not confuse Python dict lookup with a zero-cost oracle.
4. `nativeSparseScoreSameOriginalRawSparseScore`: pair original signed gamma values, two-lane ledger and positive W with source-owned signed score, including the malformed-word branches.
5. `nativeN21SameWordAndClock`: universal decision equality, certificate bound, and full actual machine runtime => original `PR.InNP`.
6. Only then the original E20 bit compiler, Cook-Levin uniform compiler, remaining Karp edges and memberships.

All new Agda declarations are source written. No compiler receipt is inferred. Agda remains Golden.


## 2026-11-09 signed SSP / Monster *Karp trace* factorisation (not a Monster quotient)

The user's proposal concerns original Karp traces and large gamma integers, not arbitrary Monster elements. Audited source owners:
- `DASHI.Combinatorics.MonsterSSPFractranProjection`: selected 15-lane exponent state, Monster-to-SSP candidate projection, preservation contracts; **no inhabitant of the required computational compiler/simulation**.
- `DASHI.Interop.VerifiedFractranCrankPipeline`: actual `MicroOp` IR and compiler simulation, explicit `CostVector` versus `MDLVector`, receipt-governed verified crank.
- `DASHI.Combinatorics.SSP15FractranCompression`: outcome equivalence, optional lossless residual, step congruence, MDL receipts.
- Original `scripts/karp21_native_bitword_sparse_verifier.py`: binary signed magnitudes, original gamma graph parser, 2m certificate and positive threshold.

### Concrete source implementations committed on PR #1474

1. `scripts/karp21_native_signed_trace_factor.py`: factor selected original cut-edge contributions by EXACT original binary sign+magnitude keys; count repetitions using BINARY counters; replay each factor using binary shift/add; maintain separate positive and negative lanes; preserve original word, certificate and positive threshold by delegating graph parsing and endpoint consistency to existing original native owner.
2. `DASHI/Mathematics/Complexity/Karp21BinaryNativeMultiplicityScaleExact.agda`: `scaleBits`, structurally recursive on original binary multiplicity bits, and universal source-written `scaleBitsValue` proof that the returned bitword denotes binary weight times binary count. This is an actual runnable bit operator, not a Nat exponent-vector evaluator.
3. `DASHI/Mathematics/Complexity/Karp21BinaryNativeSignedTraceFactorExact.agda`: actual signed token equality, duplicate-weight class insertion via a binary occurrence counter, and positive/negative binary replay via the native scaling. All imported by original Karp21Everything and Karp21BinaryRuntimeEverything. Source-written Agda, exact-head kernel receipt OPEN.
4. `scripts/check_karp21_native_signed_trace_factor.py`: original-word differential graph/certificate regression and repeated huge-weight operation count, committed to fail-closed referee. **Original-source integration script not executed here** because repository Python imports are not installed in the execution environment.

### Local mathematical comparison (separate reproduction)

An independent Python reproduction tested 19,531 signed integer traces (each length 0..6 over {-5,-1,0,1,5}); grouped and original two-lane totals were equal. For 256 identical positive weights of 1,025-bit width, repeated addition took 263,946 counted binary addition stages, versus 3,868 stages for binary-count grouping. **But** grouping also charged 262,656 binary key bits. Together these accounted operations were 266,524 versus 263,946, so there is **no certified speedup** for that example when key processing is included. Dictionary hashing/lookup/collision checks, allocations and tape head motion were not yet fully costed. Parsing the original wire already requires reading these repeated tokens; do not claim sublinear input consumption.

### How SSP/VOA/Monster could help rather than decorate the implementation

The reusable object is an **operation orbit / trace signature**, not a bare subgroup of Monster and not an arbitrary prime-power integer. A legitimate further quotient must give:
- exact equivariance or decision-preserving congruence for the concrete operation on the original N21 signed score; not merely a symmetry name;
- a source-word-to-label+residual codec and replay in all cases (or a proved decision-only quotient);
- an amortized key-building/lookup schedule including bit comparison, shared-prefix trie, allocation and memory motion;
- an actual improvement in `MDLVector` or `CostVector` under selected input families or a worst-case envelope, with transcript/binary-replay evidence.

The next substantive theorem cut: `factorSignedTraceReplaySameOriginal` and `originalGammaWordTraceFactorizationSameScore` for ALL words, then a costed word-scan compiler into this representation. The earlier `trieAdmitIffOriginalHistoryConsistency`, `nativeGraphEndpointsConsumeInputBits`, full original N21 `PR.InNP`, E20, Cook-Levin and remaining 19 reductions/20 NP-memberships are still OPEN. No source-written Agda is promoted without an exact-head Agda 2.9 receipt.


## 2026-11-09 continuation: complete factor-list semantics and SSP C2 operation reuse (source-written)

Additional Agda (directly on PR #1474, not sidecar hypothetical interfaces):
- `Karp21BinaryNativeSignedTraceFactorExact.sameSignedTokenSound`: bitwise original signed-token equality has a genuine constructor-equality proof; a hash collision or SSP sign tag is not used as an equality oracle.
- `binaryCounterIncrementValue`: the class multiplicity is incremented by actual ripple addition; proof-side value increases by exactly one.
- `replayFactorsPositiveValue`, `replayFactorsNegativeValue`: the executable group-replay fold yields precisely the sum of each factor's (binary weight × binary count) in the two selected lanes.
- `Karp21BinaryNativeSignedTraceFactorSemanticExact`: source-written universal `insertPositivePreservesTotal`, `insertNegativePreservesTotal`, complete `factorPositiveTotalCorrect` / `factorNegativeTotalCorrect`, and `factorReplayPositiveEqualsOriginalLedger` / `factorReplayNegativeEqualsOriginalLedger`. This identifies the **actual original bit-native signed ledger**, not yet the original unary-\(\mathbb Z\) `Runtime.rawSparseScore`. Proof status: SOURCE, NOT KERNEL.
- `Karp21BinaryNativeSignedTraceFactorC2Exact`: reuses `Karp21SignedSSPOrientationNoLosslessExact.flipBinarySign` (SSP sign orientation), proves involution on classes, sign-invariant identical-weight keys and concrete `factorReplayCommutesWithSignFlip`, i.e. replaying a sign-flipped class list swaps positive/negative accumulator lanes. The unfactored insert operation satisfies the same action. It uses the non-safe historical SSP import route, so is **not** advertised as `--safe`.
- The original Golden roots import the complete source-written semantics; C2 is exposed only through the non-safe original `Karp21Everything` root. The fail-closed referee now includes both.
- The finite Python audit also checks the sign-flip law. A local independent reproducer passed 19,531 signed traces and the same number of sign-flip comparisons.

### Verification and mathematical honesty

This is a real semantics-reuse advance, not a full N21 completion. Exact-head Agda 2.9 acceptance is still missing; the source proof terms might require changes after compiler diagnostics. The full original same-graph-word `rawSparseScore` weld still needs the arbitrary-word signed gamma numerical/suffix theorem, selected edge cut observation, endpoint guard and positive threshold. The model-dependent cost of building the weight dictionary and replay is not yet a bit-Turing-machine polynomial proof. Some traces will be *slower* to factor, and a shorter factor description does not automatically yield a faster execution. Do not promote P0 `PR.InNP`, E20, Cook–Levin, or E01–E19 / N01–N20.

Recheck local compiler with the repository's authoritative `scripts/run_agda29_parallel_check.sh` on the exact PR head; the current isolated environment has Python but not Agda/Nix or a network-reachable Git clone. The new GitHub source and bounded Python tests are not kernel receipts.


## 2026-11-09 — FRACDASH compiled priority-frontier max-cut (PR #1474)

Canonical detailed phase/deliverable/exact-lemma ledger: [Karp21FRACDASHMachineMaxCut20261109.md](../roadmaps/Karp21FRACDASHMachineMaxCut20261109.md).

Read `chboishabba/FRACDASH` as a three-layer source → signed executable IR → compiled exponent-vector FRACTRAN machine; not merely as a prime-power integer or two-lane sign metaphor. Its compiled first-enabled guard/delta semantics and exact-reconstruction DA51 codec are reusable, but its earlier 41-shard compression measurements are not a complexity bound for original N21.

New `--safe` source: `Karp21FractranPriorityFrontierExact.agda`, with `refreshEntryCorrect`, `refreshPopulationCorrect`, `refreshStoredCorrect`, `firstPopulatedCorrect`, `firstRefreshedCorrect` and `cachedStepCorrect`. This proves correctness of a selectively refreshed ordered guard cache conditional on a genuine unaffected-guard stability witness, and same selected successor/halt as full evaluation. Imported by both original Karp roots and added to focused Golden referee.

**Status:** source-written GENERIC frontier only; no N21 `Machine` instantiation, no original verifier-step equivalence, no original all-word decoder acceptance, no trace/residual compiler, no bit-tape polynomial runtime, no `PR.InNP`, and no Agda 2.9/parallel_checker receipt. Remaining exact original-owner goals are `karpSignedIRSameOriginalSparseScore`, `karpFractranFirstEnabledSameVerifierStep`, `karpFractranDecodePreservesAcceptance`, `karpFractranTraceRebuildExact`, `karpFractranBitMachineClockPolynomial`, `trieAdmitIffOriginalHistoryConsistency`, `nativeGraphEndpointsConsumeInputBits`, `nativeSparseScoreSameOriginalRawSparseScore`, `nativeN21SameWordAndClock`, original `PR.InNP`, E20, Cook–Levin and remaining Karp-21. The P != NP SAT lower bound is separate.

No new runtime regression or kernel acceptance is claimed for this generic-source cut.

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


## 2026-11-09 — Signed-gamma original/native all-word suffix and numerical-control cut

Canonical up-to-date status table and exact lemma chain: [Karp21FRACDASHMachineMaxCut20261109.md](../roadmaps/Karp21FRACDASHMachineMaxCut20261109.md).

New `--safe` Agda source owner `Karp21GammaBinaryNativeSignedSuffixExact` directly reuses original gamma/zigzag, native gamma/signed parsers and the existing unsigned numerical weld. The code source-writes `nativeScanNumericSuffixSame`, `nativeGammaOriginalSuffixAllWords`, `nativeSignedSuffixEqualsNativeGamma`, `karpNativeSignedGammaSuffixSameOriginal` and `karpSignedNativeControlNumericViewSameOriginal`. Every input bitword is included, including malformed, truncated and suffix-bearing words. This **closes only the suffix branch at SOURCE level** and gives original-ℤ numerical observation of the native grammar's control path. It **does not prove actual executable signed-token `valueLE (reverse magnitude)` equals old `unzigzag`**. That token-value theorem and the original graph `readRawEdges` frame are the next precise gates.

Both original Karp roots and focused Golden referee import the owner. `scripts/check_karp21_signed_gamma_suffix_values.py` is in preflight; a local independent direct execution matched original/native value, sign, suffix and failure in **65,735 finite cases**, including 200 large inputs; this is regression evidence, not Agda semantics or polynomial runtime. Exact-head Agda 2.9 and parallel_checker are unavailable. All the original full native binary ledger/score, complete FRACTRAN N21 machine, polynomial bit-machine clock, N21 `PR.InNP`, E20/Cook–Levin, remaining network and P-vs-NP `SATNotInP` remain OPEN. Do not promote a finite test or the proof-only numeric observation into a code-to-proof execution receipt.


## 2026-11-09 exact original gamma payload / native ledger rejection cut

**Source-written and not kernel accepted:** `Karp21GammaBinarySignedPayloadValueCutExact.agda` computes the actual native `Signed.readSignedBinary` and original `Old.readSignedGamma` on the same complete source gamma frame with the exact unchanged suffix. It covers arbitrary nonempty successor payloads ending in either sign bit, plus a separate gamma-zero fixture. This is NOT the signed numerical value equality: the next required lemma equates `Value.valueLE(reverse (true ∷ prefix))` with the original `Old.unzigzag` magnitude formula, handling zero and both signs. All-word malformed/truncated suffix preservation is covered by the preceding signed-gamma suffix owner.

**Real native execution and rejection theorem:** `Karp21FractranPairedBinaryTraceExact.agda` now contains `nativePairedLedger`, which runs the actual `Ledger.accumulateSigned` over the selected native tokens after original endpoint/history and 2-bit certificate checks. `nativePairedLedgerSameOriginalRejection` source-writes same success/rejection as the actual original `Runtime.rawSparseScore` on **all supplied aligned raw-edge/token lists and all certificates**, without assuming unproved token numeric equality. It does NOT validate that supplied paired binary tokens were decoded from the original graph word; that original graph-reader weld remains unpaid.

Both source owners are reached through existing Karp Golden imports; signed payload owner additionally referenced in focused referee. Existing finite regression scripts directly rerun in the working container: 38,860 priority, 13,440 N21 edge and 449,895 original raw trace cases PASS. These tests are not Agda typechecks or full original/native binary score tests. Agda 2.9/parallel_checker unavailable. Current phase/status table and precise arithmetic obligation live in `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. Original `PR.InNP`, E20, Cook–Levin, Karp network and independent P-vs-NP SAT lower bound remain OPEN.


## 2026-11-09 — Actual N21 signed-token numerical theorem and decisive remaining cut

Three new actual Agda arithmetic owners are committed on original Karp PR #1474:

1. `Karp21SignedGammaNumberTheoryExact`: source zigzag (2M/2M-1) positive/negative correction, including nonzero negative magnitude.
2. `Karp21SignedGammaBinaryValueArithmeticExact`: source original gamma BE `payloadValue` = actual native ledger `Value.valueLE(reverse bits)`; sign-bit append doubles magnitude; proves a leading-one magnitude is `suc k`.
3. `Karp21SignedGammaNativeOriginalValueExact`: `interpretNativeToken` uses the **actual** signed token's bit value, and `karpNativeSignedTokenValueMatchesOriginalEncodedFrame` source-writes exact equality of the original signed-ℤ `readSignedGamma` and the native signed binary decoder's numeric observation on EVERY COMPLETE original gamma frame, arbitrary positive/negative sign bit, prefix, suffix; separate gamma-zero theorem. Not just agreement on acceptance/suffixes.

**Status:** all new declarations **SOURCE-WRITTEN only**, Agda 2.9/`parallel_checker` exact-head unavailable; no kernel-green claim. A same-source numerical regression passed **66,334** independent finite cases for 0–14 prefix bits and 128–2048-bit additional magnitude tests, including negative and positive. This is not an Agda receipt.

**Do not overpromote:** the full all-input-word numerical weld is still OPEN until successful frame decomposition and original `Graph.readRawEdges` to native word/cursor/weight alignment are proved. The actual native two-lane signed-score equality to `rawSparseScore`, full original N21 compiled FRACTRAN simulation/acceptance/trace, physical polynomial bit-machine clock, original `PR.InNP`, E20/Cook–Levin, remaining Karp-21 edges and memberships, and separate P-vs-NP behavioural fixed point/resource lower bound `SATNotInP` remain OPEN.

The [canonical current phase and deliverables roadmap](../roadmaps/Karp21FRACDASHMachineMaxCut20261109.md) has an IN-PLACE authoritative P0-A…P0-G, P1, P2, separate P-vs-NP and Golden lemma table. Earlier chronological OPEN entries in these documents may be historical and do not supersede the new canonical table. Original attribution preserved; no ESD files edited.


## 2026-11-09 — All original bitwords: genuine native signed token ℤ value and suffix (SOURCE; kernel receipt OPEN)

The current original Karp PR #1474 now source-writes `karpNativeSignedTokenValueMatchesOriginal` in `Karp21SignedGammaNativeOriginalValueExact.agda`, proving the intended equality of the actual `Signed.readSignedBinary` token's `Value.valueLE(reverse bits)` integer interpretation and the original `Old.readSignedGamma` result **on all original gamma bitwords including malformed/rejected and arbitrary suffix**, by combining the previous complete-frame genuine number theory and new `Karp21SignedGammaAllWordFrameExtractionExact.agda` (the actual `Native.scanZeros` + `Native.readPayload` successful canonical-frame decomposition), and the original/native all-word signed suffix rejection theorem. No postulate or alternate gamma grammar is assumed.

**Correct adjudication:** SOURCE-WRITTEN proof candidates, not yet Agda 2.9 kernel-checked; the Golden referee now includes both owners. The signed number theory itself is no longer just a TODO or acceptedness wrapper. Bounded differential: 66,334 direct finite signed-zigzag/native BE/LE cases PASS, including long binary magnitudes, not a proof.

**Next exact max-cut:** original `Graph.readRawEdges` vs native graph word cursor/endpoint/signed-weight frame (P0-B); original signed `rawSparseScore` vs native binary two-lane selected weight total (P0-C); complete FRACTRAN original N21 first-enabled machine and original threshold/all-word acceptance (P0-D/E); true physical polynomial bit-TM clock (P0-F); original `PR.InNP` (P0-G); E20 and Cook–Levin, remaining Karp network, separate P-vs-NP coded behavioural self-specialization and SAT lower bound. All remain open. Authoritative owner [P0-A..P0-G/P1/P2 exact phase and deliverables table](../roadmaps/Karp21FRACDASHMachineMaxCut20261109.md); historical OPEN mentions in older notes are superseded only as SOURCE status.


## 2026-11-09 source refresh — exact phases and new P0-C/E20 owners

Canonical up-to-date gate ledger: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md` (CURRENT CANONICAL PHASE / DELIVERABLE / EXACT-LEMMA CUT). Existing branch source `Karp21SignedGammaNativeOriginalValueExact.karpNativeSignedTokenValueMatchesOriginal` already asserts **all-word actual SignedMagnitudeBits ↔ original signed-ℤ result**, and `Karp21SignedGammaNativeRawEdgeStreamExact.nativePairedRawEdgesSameOriginal` already asserts original raw signed-edge stream identity, subject to exact-head Agda 2.9 kernel check. New `Karp21SignedGammaNativeItemStreamExact` source-writes `nativeObservedItemsSameOriginal` and `nativeObservedPartitionSameOriginal` on the ACTUAL signed-token parser plus proof-side values, original count and strict suffix rejection. New `Karp21NativeSelectedSignedScoreExact` source-writes `selectedTraceRetainsNativeNumericalAlignment`, `alignedSelectedSignedSum`, `nativeAlignedScoreSameOriginalRawSparseScore`, `nativeRawEdgeStreamIsAligned` and `nativeRawStreamSignedScoreSameOriginal`, carrying original signed-ℤ numerical score from ACTUAL native gamma raw-edge stream through original endpoint guard, two-bit certificate and selected cut traces.

**Not yet paid:** actual two-lane signed binary ledger numerical interpretation equals native ℤ trace sum; native bit-oriented endpoint/count and complete graph header/threshold; complete N21 FRACTRAN same-step, output/readout and trace; bit-tape physical polynomial clock; original `PR.InNP`; E20 fully bit-native costed compiler, Cook–Levin, all 21 historical NP reductions/memberships; separate behavioural fixed-point resource lower bound `SATNotInP`. Signed source semantics must not be mistaken for executable cost. All changes imported into Golden roots, focused referee updated; exact-head Agda 2.9/parallel_checker **not run/receipt OPEN**. No P≠NP proof claimed.


## 2026-11-09 latest P0-C: ACTUAL native two-register signed score ↔ original rawSparseScore

Canonical source-of-truth: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md` CURRENT CANONICAL PHASE table (supersedes older chronological OPEN rows).

New `Karp21NativeLedgerIntegerScoreExact.agda` imports real `Karp21BinaryNativeSignedLedgerExact.accumulateSigned` and existing `accumulateEmptyPositive`/`accumulateEmptyNegative`; `integerPositiveStep`, `integerNegativeStep`, `negativeTokenInteger`, `tokenClassesEqualOriginalSignedTrace` and `nativeSignedLedgerIntegerEqualsOriginalTraceScore` source-write the binary two-register numerical observation `(+ P) + (- (+ N))` as the exact signed ℤ token fold. Neither the executable parser nor accumulator performs proof-side unary-Nat subtraction.

New `Karp21NativeLedgerOriginalRawScoreExact.agda` composes `nativeLedgerScoreMatchesNativeSelectedTrace` and `nativeSignedLedgerIntegerEqualsOriginalRawSparseScore` with actual original endpoint/history/certificate selection and parser-produced native signed edge pairs. This is source-written equality with original `Runtime.rawSparseScore` **on successfully parsed source signed raw-edge streams**, including certificate failures; it is **not** the complete original graph-word / threshold decision.

**Remains OPEN**: Agda 2.9 exact-head and parallel_checker receipts; native bit-coded endpoint and full strict graph header/positive-threshold parsing; original binary threshold-comparator numeric theorem; complete first-enabled N21 FRACTRAN step and acceptance/trace; physical polynomial bit-machine clock and actual `PR.InNP`; costed E20/Cook–Levin; original Karp-21 network; independent P-vs-NP code-consuming behavioural fixed point, resource lower bound and `SATNotInP`.

Both new owners imported into the original Golden Karp roots and added to the focused Agda referee. A new reproducible bit-ripple two-register differential is tracked at `scripts/check_karp21_native_two_lane_raw_score.py` and called during preflight. An independently executed finite numerical differential passed 454,895 cases including 256-bit weights; the committed bit-ripple version has NOT been executed under this harness yet. No new Agda kernel receipt or Clay result.


## 2026-11-09 P0-E/F same-source binary comparator cut

New source-written `Karp21BinaryNativeThresholdStructuralExact.agda` uses the genuine `Karp21BinaryNativeThresholdExact.compareLE`, proving `compareLEReflexive`, `atLeastReflexive`, `compareLESameLowBit`, `atLeastSameLowBit`, high-priority select laws and `compareInspectionLinear` (actual source recursive comparisons ≤ combined operand width +1). Its `--safe` source is imported by original `Karp21Everything` and `Karp21BinaryRuntimeEverything` and checked by focused referee. Local independent numerical three-way ordering and atLeast differential: **71,025/71,025 PASS**, including exhaustive all bitwords of length 0..7 and 6,000 random operands up to 513 bits. Committed `scripts/check_karp21_native_comparator_exact.py`, wired into `referee_karp21_maxcut.sh`.

**Exact P0-E OPEN**: `compareLENumericalCorrect` for arbitrary bitwords (regression ≠ Agda theorem); `nativePositiveThresholdParserSameOriginal`, `nativeOriginalGraphWordFieldsSame`, `karpNativeThresholdDecisionSameOriginal`, `karpFractranDecodePreservesAcceptance`, `karpFractranTraceRebuildExact`. P0-F physical bit-Turing-machine movement/allocations/bit-width clock is NOT paid by primitive inspect counts. P0-D original N21 first-enabled machine, original `PR.InNP`, original E20/Cook–Levin, Karp-21 network and independent P-vs-NP `SATNotInP` remain OPEN. Exact-head Agda 2.9 / parallel_checker not run. Canonical CURRENT table and exact phase/lemma inventory: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`.


## 9 November 2026 continuation — P0-D/E original comparator, source positive gamma, parsed-raw FRACTRAN terminal decision

**NEW SOURCE candidate** `Karp21BinaryNativeThresholdNumericalExact.agda`: `compareLENumericalCorrect` for all original bit lists (constructive strict Nat gap trichotomy, source `Compare.compareLE`, including unequal widths and zero padding); `atLeastTrueGivesNumericalOrder`, `atLeastFalseGivesNumericalOrder` follow actual `atLeast`. **NEW** `Karp21NativePositiveThresholdNonzeroExact.agda`: native bit test `anyOneFalseMeansZero`, `anyOneTrueMeansPositive`, `readPositiveGammaLEAlwaysPositive`. **NEW** `Karp21NativePositiveThresholdNumericFrameExact.agda`: `nativePredecessorValueSameOriginalGamma` pays gamma(n+1) successor correction for actual LE binary predecessor; `nativePositiveThresholdParserSameOriginal` source-writes all-word strict original gamma-positive threshold parser/number/suffix/rejection equality (no complete graph header).

**NEW P0-D** `Karp21FractranOriginalRawListMachineExact.agda` follows complete original parsed raw signed-edge list and exactly-two-label-bits-per-edge cursor, original endpoint-history, actual binary two-lane ledger and halt/reject; `karpFractranFirstEnabledSameRawCursorStep` checks independently defined raw list transition. **NEW** `Karp21FractranParsedRawThresholdMachineExact.agda`: positive native threshold decision on terminal cursor, `karpFractranFirstEnabledSameParsedRawVerifierStep` and cache version exact **for parsed raw inputs**. No artificial promise that this is the full `Runtime.readRawGraphWord` or typed original verifier step.

63,001-case independent full parsed raw-score + positive threshold machine regression PASS (including 7,000 random cases with 128-bit signed weights), committed `scripts/check_karp21_fractran_parsed_raw_threshold.py`, wired to focused preflight; existing 71,025 comparator and 454,895 native ripple-ledger differentials PASS independently. No Agda 2.9/parallel_checker executable; **new proof declarations are NOT kernel accepted**.

Full remaining max-cut: `nativeOriginalGraphWordFieldsSame` for original n/m, strict u<v<n ordering, full suffix/threshold and sparse budget, binary endpoint representation; `karpNativeThresholdDecisionSameOriginal` for signed ℤ versus exact LE atLeast; `karpFractranFirstEnabledSameVerifierStep` on COMPLETE original graph-word decoder; all-word acceptance and trace reconstruction; true polynomial bit-machine tape/motion/allocation clock; original `PR.InNP`; costed original E20/Cell Bits Cook–Levin; Karp-21 network; separate behavioural resource proof and `SATNotInP`. Canonical current phase/deliverable and exact remaining lemma table: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. No P≠NP theorem.


## 2026-11-09 current P0-B/D/E/F and original P1 prior-art cross-pollination

The canonical exact remaining cut, now authoritative over historical notes, is `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. All newly added Agdas are SOURCE-WRITTEN, **not Agda kernel accepted**.

- **P0-B/E whole original graph**: `Karp21NativeWholeRawGraphWordExact` executes original literal gamma n/m, 3m short-word guard, counted native signed raw-edge token stream, positive native gamma threshold, strict original u<v<n/sorted-unique edge validation, and no trailing bits. `Karp21NativeOriginalWholeGraphFieldsWeldExact.nativeOriginalGraphWordFieldsSame` source-writes equality of **whole same-input original Fin-free graph fields** incl. malformed rejection, consuming existing all-word signed-edge and native positive gamma source correspondences. Original Nat-producing header/endpoints/validation and bit clock remain OPEN.
- **P0-D/E original FRACTRAN machine**: `Karp21FractranOriginalRawListMachineExact` implements actual remaining original raw-edge list/certificate cursor/history/two-register score/live-rejected-finished state and ordered `advance/finish/reject` priority; `karpFractranFirstEnabledSameRawCursorStep` source-writes exact direct step. `Karp21FractranParsedRawThresholdMachineExact.karpFractranFirstEnabledSameParsedRawVerifierStep` adds actual binary positive threshold terminal decision, separate direct reference and cached refresh. **This is parsed-raw scope only; original all-word `karpFractranFirstEnabledSameVerifierStep` remains OPEN.**
- **P0-F**: `Karp21FractranParsedRawStepPotentialExact.cursorPotential`, `originalParsedRawStepStrictPotential`, `karpFirstEnabledStepStrictPotential` source-write strict decrease of remaining-edge-count+1 for every real parsed-raw first-enabled step, bounding high-level rule firings ≤ m+1. This does NOT bound original endpoint Nat decoding, bit-TM memory movement/width, tape-head operations, graph parsing and physical verifier clock.
- **P0-E numerical**: `Karp21BinaryNativeThresholdNumericalExact.compareLENumericalCorrect` source-writes ALL-WORD constructive strict Nat gap trichotomy for actual `Compare.compareLE`. `Karp21NativePositiveThresholdNumericFrameExact.nativePositiveThresholdParserSameOriginal` source-writes strict all-word positive gamma numerical outcome/suffix/rejection. These remain Agda-kernel OPEN.
- **P1 canonical Cook-Levin prior art**: `ConcreteTapeCanonicalCellBitsExact.canonicalWindowCodec`, `ConcreteTapeRunCNFWeldExact.runToEncodedCNFPath`, and `ConcreteTapeFlatAssignmentExact.flatTableauAssignment` already existed; `Karp21ConcreteTapeCanonicalRunFlatWeldExact.canonicalSameRunCNFPacket` now consumes them for the EXACT SAME concrete tape run/start row/flat bits, with original run length and start-row pullback. Global clause coordinate placement, endpoint clauses, accepting-run iff SAT and costed original E20/Cook-Levin remain OPEN.
- **Separate P-vs-NP**: actual original `PNotEqualsNPClayCoreExact.SATNotInP` still requires an uninhabited lower-bound proof; existing equivalence compiler is conditional, and P0/P1/P2 constructive work does not imply `SATNotInP`.

**Differential evidence**: independently tested parsed-raw signed score vs high-level first-enabled native positive threshold machine 63,001/63,001 PASS, including 7,000 random 128-bit signed weights; script `scripts/check_karp21_fractran_parsed_raw_threshold.py` is committed and called by focused preflight. Existing separate 71,025 comparator and 454,895 ripple binary-ledger differentials PASS. These do not prove Agda kernel acceptance, a bit clock, NP-completeness or P≠NP. Both original Karp Golden roots and focused referee now reach the new source owners.


## 2026-11-09 latest P0-E original signed N21 terminal acceptance

New `Karp21NativeThresholdOriginalSignedDecisionExact.agda` source-writes `compareAtLeastNumericalBoolean` on actual bit `Compare.compareLE`/Nat values and `signedThresholdBoolean` to identify the exact **original signed** criterion `Int._≤ᵇ_ (+W) ((+P) + (- (+N)))` with the native `Nat._≤ᵇ_ (N+W) P`, for ALL nonnegative register totals and threshold. `karpNativeThresholdDecisionSameOriginal` composes the REAL binary `Positive.meetsOriginalPositiveThreshold`/actual ripple add with proof-side ledger integer observation. This is a SOURCE-WRITTEN proof candidate awaiting Agda kernel, not an invented signed threshold oracle.

New `Karp21NativeParsedRawAcceptanceExact.agda`: `karpNativeParsedRawAcceptanceSameOriginal` consumes the ACTUAL source grammar native signed edge stream read, the actual `Paired.nativePairedLedger` (original endpoint/certificate), previously source-written `nativeSignedLedgerIntegerEqualsOriginalRawSparseScore`, and new signed threshold equality to source-write exact acceptance of the original signed `Runtime.rawSparseScore` and original `Int._≤ᵇ_` for all original certificate words after a successful original source edge stream. Both modules in Golden roots and focused referee.

**Still unpaid**: `karpFractranDecodePreservesAcceptance` across ALL original *graph word* malformed branches/header/strict validation (existing `nativeOriginalGraphWordFieldsSame` is only source-written); full N21 first-enabled whole-word step, trace/residual reconstruction; complete physical bit-TM clock and original `PR.InNP`; costed original E20/Cell Bits accepting-run iff SAT; Karp 21 full network; independent code-consuming behavioural fixed point and `SATNotInP`. No Agda 2.9/`parallel_checker` receipt, no Clay P≠NP proof. Source of truth phase/deliverable/exact-lemma: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`.


## 2026-11-09 latest original whole-word P0-E Fin-free acceptance source candidate

New `Karp21NativeWholeWordAcceptanceExact.agda`: `nativeWholeWordAccepts` runs the original full graph grammar with genuine native signed gamma weights, binary predecessor strict-positive threshold, strict original raw-edge validation and the actual binary ledger/threshold selection. `nativeWholeSuccessContainsActualEdgeReceipt` reconstructs the source signed-raw-edge stream receipt from the successful n/m/m*3/native-edge/native-threshold/validator original parsing branches, without caller-supplied arbitrary aligned values. `karpFractranDecodePreservesAcceptance` composes actual all-word `nativeOriginalGraphWordFieldsSame` and parsed-raw binary `karpNativeParsedRawAcceptanceSameOriginal` to match `Original.verifyFinFreeSparseGraphWord` on all original graph/certificate bitwords, **SOURCE-WRITTEN ONLY** (Agda 2.9 and parallel_checker unavailable; no kernel receipt). Imported into original `Karp21Everything` and `Karp21BinaryRuntimeEverything`; focused referee registers it.

Precise scope: original FIN-FREE verifier Boolean on all words, NOT original typed Fin/Cut verifier identification, NOT the actual whole-word FRACTRAN first-enabled transition simulation, NOT an all-word trace/reconstruction, NOT a polynomial binary-TM clock or original `PR.InNP`. Native parser still uses original Nat gamma header/endpoint values. P0-D typed/whole verifier step and P0-E `karpFractranTraceRebuildExact` remain open; P0-F/G, E20/Cell-Bits Cook–Levin, remaining Karp network and separate `SATNotInP` remain open. Latest canonical phase/deliverable/lemma ledger: `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`.


## 9 Nov 2026 — real remaining cut, binary endpoint implementation (current)

The current authoritative source-level proof/dependency audit is `Docs/roadmaps/Karp21ActualMaxCutBlockers20261109.md`, with ordered **B1–B6, D1/D2, E1/E2, F1–F4, G1–G4, P1.1–P1.4, P2 and independent P≠NP**. The historical "still missing comparator/all-word acceptance" entries above are superseded: `compareLENumericalCorrect`, `nativePositiveThresholdParserSameOriginal`, `nativeOriginalGraphWordFieldsSame`, `karpNativeThresholdDecisionSameOriginal`, `karpFractranFirstEnabledSameParsedRawVerifierStep`, `karpNativeParsedRawAcceptanceSameOriginal`, and `karpFractranDecodePreservesAcceptance` are already SOURCE-WRITTEN, awaiting exact-head Agda 2.9 kernel acceptance.

The new executable P0-B/F subcomponent runs original gamma(n) as LE binary bits (zero accepted) via `Karp21NativeUnsignedEndpointBitReaderExact.readGammaNatLE`, reads actual signed N21 raw edges with LE binary u/v and native signed weight via `Karp21NativeBinaryEndpointRawEdgeStreamExact.readOneBinaryRawEdge`, and validates strict u<v<n and original lex ordered pair policy via `Karp21NativeBinaryEndpointValidatorExact.validNativeBinaryEdges` without unary endpoints in these runtime functions. All-word source proof candidates `nativeUnsignedEndpointSameOriginal`, `binaryEndpointRawEdgeStreamSameOriginal`, `nativeStrictLessNumerical` and width lemmas are Golden-imported and focused-referee targets. Independent differential: 132,271 gamma endpoint/cursor and 19,440 strict validator cases PASS; `scripts/check_karp21_binary_endpoint_cut.py` is committed.

**Do not overstate:** the existing complete source graph parser still evaluates unary Nat n/m/endpoints; new binary raw-edge stream still takes original unary Nat edge count m. First real unpaid B1/B2 original strict validator correspondence, B3/B4 binary n,m header+length-budget, B5 original endpoint-history equivalence, B6 actual complete native bit graph remain. Physical tape/head/allocation bit-clock (F1–F4), source original `PR.InNP`, costed E20/Cell-Bits Cook–Levin, Karp network and distinct `SATNotInP` remain OPEN. Agda 2.9/parallel_checker not available here; source-written is NOT kernel-accepted. No terminal gate declared closed.


## 9 November 2026 — B1–B5 source proof candidates and complete binary N21 runtime

Canonical precise cut is now `Docs/roadmaps/Karp21ActualMaxCutBlockers20261109.md` (supersedes all older B1–B6 OPEN paragraphs) and first table of `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`. New B1/B2 owners `Karp21NativeBinaryStrictAfterOriginalExact.nativeBinaryStrictAfterSameOriginal` and `Karp21NativeBinaryValidRawEdgesOriginalExact.nativeBinaryValidRawEdgesSameOriginal` source-write exact original Graph.strictAfter and Original.validRawEdges decisions (source NatP._<?_/≟_ reflected constructively). New B3/B4 `Karp21NativeBinaryHeaderBudgetExact` runs actual gamma n/m to LE bitwords and `Karp21NativeBinaryCountBudgetExact` runs actual bitwise `3m ≤ input suffix length` BEFORE any edge-count loop; `NatP._≤?_` source decision reflection added. B5 `Karp21NativeBinaryEndpointHistoryOriginalExact.nativeBinaryEndpointHistorySameOriginal` source-writes exact original endpointConsistent repeated-label recurrence using native binary equality.

**Executable whole N21:** `Karp21NativeWholeBinaryGraphRuntimeExact.readNativeWholeBinaryGraphWord` reads original gamma headers, binary m-budget, signed original edge triples, strictly ascending binary endpoints, positive threshold/strict suffix; `readBinaryRawEdgesFuel` decrements binary m under actual input-length fuel instead of allocating unary m. `Karp21NativeWholeBinaryVerifierExact.verifyNativeWholeBinaryGraphWord` then executes the original sparse certificate, chronological binary endpoint consistency, actual two-register signed ripple ledger and native positive threshold. It **does not execute a unary decoded n/m/u/v**.

**New direct B6 proof candidates** `Karp21NativeBinaryCountFuelOriginalExact.nativeBinaryCountFuelSameOriginal`, `Karp21NativeBinaryCountBudgetFuelExact.binaryBudgetSuppliesFuel` and `nativeBudgetedBinaryRawEdgesSameOriginal` connect actual binary decrement/structural-fuel signed edge loop to original Graph.readRawEdges using genuine source guard 3m ≤ length. All modules Golden-imported and focused-referee registered. `scripts/check_karp21_binary_header_budget.py` and `scripts/check_karp21_whole_binary_verifier.py` tracked preflight regressions. Independent finite differentials actually executed: 147,070 n/m gamma+budget, 66,735 complete signed graph, 25,000 binary endpoint history, and 134,668 full signed Fin-free verifier examples PASS. Tests are finite; Agda 2.9/parallel_checker not installed, **ZERO newly kernel-accepted gates**. Integration modules importing not-yet-proved --safe original sources no longer falsely assert --safe.

**Actual remaining high-alpha leaves:** `nativeWholeBinaryGraphWordSameOriginal` and `nativeWholeBinaryVerifierSameOriginalFinFree` (source-written B6 count-loop is a dependency, not final); then original whole-word first-enabled FRACDASH machine and full trace, typed Fin/Cut same-word bridge; actual bit-TM tape/head/allocation/width simulation and `karpFractranBitMachineClockPolynomial`; original `PR.polynomialTimeVerifier`, certificate bound and `PR.InNP`; E20/Cell-Bits accepting-run Cook–Levin; original 21 Karp reductions/memberships and `CertifiedKarpNetwork`. Independent SATNotInP / behavioural fixed-point resource lower bound is NOT obtained and does not follow from NP completeness.


## 2026-11-09 current binary original N21 maximum cut (supersedes old B6/E2/D1 status)

The complete real original-wire LE-binary N21 graph reader and sparse signed verifier are already executable. This pass now **SOURCE-WRITES** the actual terminal proof chain:

- `Karp21NativeWholeBinaryGraphOriginalExact.nativeWholeBinaryGraphWordSameOriginal`: actual full binary gamma n/m/u/v signed graph parse, input-length binary-m loop, original strict edge validation and positive threshold ↔ literal original `Original.readRawGraphWord` on ALL graph words, including rejection; explicitly handles `m*3 ≡ 3*m`.
- `Karp21NativeBinaryCutLedgerOriginalExact.nativeBinaryCutLedgerSameOriginal`: actual chronological binary endpoint-history, arbitrary starting two-lane ledger, signed bit-token insertion and original `rawSparseScore` for all certificates.
- `Karp21NativeWholeBinaryVerifierOriginalExact.nativeWholeBinaryVerifierSameOriginalFinFree`: actual complete original binary verifier equals original Fin-free signed Max-Cut on all words/certificates.
- `Karp21NativeWholeBinaryTypedAcceptanceExact.nativeCanonicalTypedSparseVerifierSameWord`: same real binary program equals original **typed** Fin/Cut N21 decision via existing original theorem.
- `Karp21NativeWholeBinaryPriorityMachineExact`: executable source actual graph→binary first-enabled N21 state, independent original-wire binary reference step, ordered advance→finish→reject, explicit halted accepted/rejected and same step/cache theorem.
- `Karp21NativeWholeBinaryStepPotentialExact`, `Karp21NativeWholeBinaryFiniteRunExact`, `Karp21NativeWholeBinaryPriorityRunAcceptanceExact`: real binary first-enabled potential strictly decreases, finite run ≤ parsed edge count+1 top-level steps, complete terminal binary/typed N21 readout.
- `Karp21NativeBinaryAdderWidthBoundExact`: real carry-adder output bit-width ≤ combined operand widths+1, a genuine F2 sublemma.

**Status is SOURCE-WRITTEN ONLY:** exact-head pinned Agda 2.9 and `parallel_checker` remain unavailable; these proof candidates have not been accepted by the kernel and may require reductions/import/arithmetic repairs. All new owners are imported by the original Karp Golden roots and added to the fail-closed focused referee. Locally reran existing independent original Fin-free vs binary end-to-end differential 134,668/134,668 PASS, n/m+3m binary header 147,070/147,070 PASS, comparator 71,025/71,025 PASS; these test Python mirrors, not the newly written Agda.

**Still truly unpaid:** original event-by-event selected-edge `karpFractranTraceRebuildExact` (terminal acceptance is not a trace); selected original typed FRACTRAN state/step relation if required beyond the binary reference; full F1 tape/cell/head configuration, F2 global intermediate widths/allocations, F3 bit-tape transition simulation, F4 `karpFractranBitMachineClockPolynomial`; G1–G4 actual `PR.polynomialTimeVerifier`, certificate bound and original `PR.InNP`; P1 costed E20 and same-Cell/Bits accepting-run CNF ↔ SAT with original bit clock; P2 original E01–E19/N01–N20 and `CertifiedKarpNetwork`. Separately a universal `SATNotInP` polynomial-time lower bound remains an open mathematical problem. No P≠NP conclusion.

Canonical current proof inventory: `Docs/roadmaps/Karp21ActualMaxCutBlockers20261109.md` and `Docs/roadmaps/Karp21FRACDASHMachineMaxCut20261109.md`.


## 9 November 2026 E1 exact original selected-weight event trace — current

PR #1474 new `Karp21NativeWholeBinarySelectedEventTraceExact.actualFirstEnabledSelectedEvents` actually follows ordered `Machine.Compiled.directStep` on the **real binary original-wire graph/cert/state** and records selected signed-gamma weight tokens, distinguishing a malformed sparse certificate (no valid event trace) from a valid certificate below original threshold W (trace exists). Source theorem `nativeFirstEnabledSelectedEventsSameOriginal` compares full ordered observed signed-ℤ token events with independently original `Trace.rawSelectedTrace` on arbitrary binary source edge/certificate/history/ledger/threshold. New all-original-word `Karp21NativeWholeBinaryTraceRebuildExact.karpFractranTraceRebuildExact` composes B6 original signed graph word equality and that event lemma on the SAME graph/cert, not merely Boolean terminal acceptance. Also corrected actual D1 malformed-word rejection proof's reversed parser equation (`originalGraphRejectsWhenBinaryInitialRejected`). Both event owners Golden-imported/referee-targeted.

**Status: UNCHECKED AGDA SOURCE candidates; exact-head pinned Agda 2.9/`parallel_checker` kernel acceptance is still OPEN.** Further missing selected independent compiled FRACTRAN state/trace transport if applicable; selected physical bit-TM F1–F4 tape/head/width/cost, original `PR.polynomialTimeVerifier` and `PR.InNP`, costed E20/Cell-Bits accepting-run Cook–Levin, remaining original Karp 21 network and separate universal SATNotInP lower bound. No new P≠NP theorem. Canonical current cut: `Docs/roadmaps/Karp21ActualMaxCutBlockers20261109.md`.

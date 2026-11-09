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

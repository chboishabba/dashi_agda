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

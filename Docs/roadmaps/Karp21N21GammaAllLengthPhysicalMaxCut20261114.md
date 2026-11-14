# Original N21 physical gamma: all-k literal transition cut, 14 November 2026

## Actual source and mathematical payoff

The original canonical `Gamma.readGammaBinary` parses
`0^k · 1 · payload[k] · suffix` into `just (1 :: payload, suffix)` for any nonnegative k. Source is `Karp21GammaBinaryNativePayloadExact.readGammaBinaryPayloadExact` and `Karp21GammaBinaryGoldenCoreExact.zeroPrefix`.

Four new SOURCE-WRITTEN original-target Agda modules are on stacked PR #1502:

1. `Karp21NativeGammaAllLengthFiniteTablePhysicalExact.agda`: literal 3-control-state × 4 input-cell × 4 work-cell finite table, 1 input + 1 work tape. Each instruction moves a head at most one cell. Physical fuel/cell inequality and original gamma parser theorem on **every k**. k=0 halt at separator. No unit-time source Nat or higher-order interpreter opcode.
2. `Karp21NativeGammaAllLengthPrefixSimulationExact.agda`: source-written inductive proof for all k leading zeros, recording EXACTLY k Mark tally cells in the physical zipper, with input head stopping on the original separator.
3. `Karp21NativeGammaAllLengthPayloadSimulationExact.agda`: for every payload of k bits, source-written k-instruction physical payload traversal, replacing every Mark by the corresponding bit and preserving the untouched suffix at the input head; exact reversed physical work-bit storage.
4. `Karp21NativeGammaAllLengthSeparatorAndHaltExact.agda`: prefix-work-marker count equality, physical B1 separator transition to the first real payload bit, and final halt without consuming the suffix after all k Marks.

The source proofs use the original physical `Tape.machineStep`/`machineRun`, `TableProgram` local table, and literal `Γ` bit-word representation. They are not abstract receipts. An independent exact Python zipper-step model checks 31,713 positive original `k=0..9` words and seven malformed controls against the source parser.

**All-k instruction accounting:** for k>=1, exactly k prefix-zero steps, one separator, k payload steps and one final halt step = `2k+2`. For k=0, one separator/halt step. Since an original gamma token occupies `2k+1` bits, the selected token is processed in at most `input token length+1` local finite-table steps. Each physical step increases represented input/work cells by at most two, by the already-existing `machineRunCellBudget`. This is a rigorous machine DESIGN plus source-written stage theorems; it is **not yet an Agda kernel receipt** for a composite all-k theorem.

## Still unpaid, in strict dependency order

- **F1.4 — all-gamma composite theorem:** produce a single Agda theorem `physicalAllLengthGammaRunSameOriginal` composing the above four source lemmas with `Tape.machineRun` addition. Cover k=0, well-formed k>=1, truncated payload, missing separator, error status / accept-reject flag and suffix exact equality. Source modules have no current Agda 2.9 kernel receipt; fix any actual diagnostics.
- **F1.5 — original repeated token parser:** compile `readRawGraphWord` for all gamma n,m,u,v,signed weights and W using the literal table and physical input/certificate tapes, not an abstract `Nat` source parse.
- **F2.2 — complete space:** bound all persistent and temporary bit-tapes, copied words, history, edge ledger, stack, memory reuse and machine transition overhead.
- **F3 — source original step simulation:** prove `originalBitTapeStepSimulatesN21Rule` for selected ordered first-enabled FRACTRAN and actual same-word history/score/threshold, errors and traces.
- **F4 — global original machine clock:** prove `karpFractranBitMachineClockPolynomial` for the physical fully compiled N21 verifier, not just one gamma token. Then type exact `PR.polynomialTimeVerifier` and `originalN21InNP`.
- **Independent C gate:** `SATNotInP` remains open and is NOT implied by any number of physical parser steps or by certified NP-completeness.

## Local checks

```sh
python3 scripts/check_karp21_gamma_all_length_physical.py
scripts/run_agda29_parallel_check.sh DASHI/Mathematics/Complexity/Karp21StackedSourceConvergence20261114.agda
```

The first is an exhaustive **finite** differential, the second is the actual Agda checker (not run in the current model execution container). An `Exact.agda` file or a formally specified `TableProgram` is no claim of kernel-accepted correctness. Original Karp (1972), Conway FRACTRAN (1987), and first Git commit priority remain preserved by original PRs and per-file history.


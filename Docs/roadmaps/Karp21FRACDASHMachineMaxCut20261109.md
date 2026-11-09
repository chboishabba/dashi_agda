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

# Qwenputer: architecture formalisation and binary/ternary max-cut

Date: 2026-11-02. Status: **source-written finite Agda reconstruction; no kernel acceptance or exact-checkpoint equivalence yet**.

## Source and ownership ledger

External original: **Divyansh Agrawal**, *Qwenputer: a computer compiled into the weights of a pretrained language model*, version 0.1.0 (2026), MIT. [Source repository](https://github.com/divagr18/qwenputer), [22 October 2026 technical account](https://divagr.com/blog/qwenputer), [RV32 detailed architecture](https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md), [CHIP-8/Qwen3.5 architecture](https://github.com/divagr18/qwenputer/blob/main/docs/q35.md), [object store](https://github.com/divagr18/qwenputer/blob/main/docs/q35-store.md). Software citation: Agrawal (2026), `agrawal2026qwenputer` in upstream `CITATION.cff`. Do not reassign authorship of upstream compilation or measurements to DASHI.

Prior fast-weight/delta-rule ancestry: **Imanol Schlag, Kazuki Irie and Jürgen Schmidhuber** (2021), *Linear Transformers Are Secretly Fast Weight Programmers*, ICML 2021. Qwen/Qwen3.5 pretrained model authors retain their own upstream model ownership. RISC-V ISA and CHIP-8 are externally established architectures; a model-inspired adapter is not an original definition of their ISAs.

Internal pre-existing theorem ownership (reuse rather than duplicate):

- `DASHI.ComputerScience.TemporalStorageFibreExact`: time/address/head and representation fibres.
- `DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact`: binary bit embeds as nonzero balanced trit, left inverse, zero excluded; this **is not** binary=ternary.
- `DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact`: executable finite register machine, load/store/branch/ALU and bounded run.
- `DASHI.ComputerScience.ShorStandardBinaryTernaryStoredProgramComputerExact`: stored binary and framed-ternary program equivalence on specified finite examples.
- `DASHI.ComputerScience.TekumFiniteSemanticsExact`, `TekumSSPFRACTRANBridgeExact`: distinct signed-radix semantics and representation fibres. Earlier Tekum work credits **Laslo Hunhold**, arXiv:2512.10964 (2025); external FPGA source credits **Thomas Schlögl and Dietmar Fey**, DOI 10.1007/978-3-032-03281-2_3. Reusing that lineage does not make Tekum part of Qwenputer.
- `DASHI.Combinatorics.FractranComputationEquivalence`: source-step/halts/run certificate boundaries for reductions; **no universal CPU equivalence** follows.
- Relevant PR archaeology: [#1083 Tekum](https://github.com/chboishabba/dashi_agda/pull/1083), [#839 binary/ternary CS fibre](https://github.com/chboishabba/dashi_agda/pull/839), [#1442 signed-history expert](https://github.com/chboishabba/dashi_agda/pull/1442). The PR references identify existing work, not first-implementation timestamp certificates.

New repository-owned formal reconstructions:
`DASHI.ComputerScience.QwenputerGatedDeltaArchitectureExact` and
`DASHI.ComputerScience.QwenputerHybridStateAndFileStoreExact`.
The additional `DASHI.ComputerScience.QwenputerRv32LayerScheduleSourceExact` records all 11 attributed P2 stages, the reported head counts (summing to 99), and the aggregated 42,012 MLP units without guessing the L3/L4 split. The aggregate `DASHI.Unified.QwenputerBinaryTernaryTOEExact` exports the bounded witnesses into the TOE roots.

Both are **new DASHI models motivated by Agrawal**. Their proofs must not be described as kernel-checked until the pinned Agda toolchain accepts them. This PR contains source-written code only.

## Repository implementation lineage

GitHub commit objects provide source-presence identifiers for this new tranche. These are **first source-written appearances**, not the first kernel-accepted proof receipts. The precise author/committer UTC timestamps were not returned by the available commit metadata and are not inferred from PR chronology.

| Source-written owner | First commit containing its new source |
|---|---|
| Finite GDN RAM, trace and representation bridge | [`e0d67c3be228c956ddf2c65375c03c340a55c9c4`](https://github.com/chboishabba/dashi_agda/commit/e0d67c3be228c956ddf2c65375c03c340a55c9c4) |
| Token ownership, snapshots, finite file store | [`c40dcfcc8ed1e6b49a6294914bc92ddf9af8ca36`](https://github.com/chboishabba/dashi_agda/commit/c40dcfcc8ed1e6b49a6294914bc92ddf9af8ca36) |
| RV32 source P2 layer schedule | [`a8045910e443847dd038f1f81fc12a300b79bc07`](https://github.com/chboishabba/dashi_agda/commit/a8045910e443847dd038f1f81fc12a300b79bc07) |
| TOE binary/ternary aggregate | [`ff9cab3cba92d006bdfc96c9d6d570c8cec24c36`](https://github.com/chboishabba/dashi_agda/commit/ff9cab3cba92d006bdfc96c9d6d570c8cec24c36) |
| Exhaustive small-state Python oracle | [`5fefb9ab9cd9876ea69067d9437cd618cf140b91`](https://github.com/chboishabba/dashi_agda/commit/5fefb9ab9cd9876ea69067d9437cd618cf140b91) |

## Complete architecture decomposition and source boundaries

The source has **distinct generations**; never merge their layer budgets, RAM capacity or validation results.

| Surface | Source-level architecture | Typed/finite consumer | Missing same-object proof |
|---|---|---|---|
| Qwen3.5 backbone | Original 32 transformer layers, original pretrained weights unchanged | `baseQwen35` and `Rv32SourceParameters` metadata | exact Qwen state evolution |
| Compiled CPU | RV32IM + Zba + bignum unit; 11 compiled layers prepended; source P3 hidden width 3968 and vocabulary 478,656 | `rv32ReportedParameters` and `InstructionSimulation` contract | full opcodes, decode, XLEN=32, zero register, signed/unsigned semantics, exceptions/ECALL, bignum, firmware |
| Compiled primitives | Gated DeltaNet RAM, SwiGLU truth tables, threshold tests, half-unit margins, SIMD nibble arithmetic | finite typed `Location`, `Ram`, `writeRam`, `readRam` | matrix-to-typed-RAM refinement at each layer, numerical exactness |
| GDN recurrence | gate alpha=1, beta=1, one-hot read/write; key-head/value-head row mapping | `readWriteSame`, `readWriteOther`, `registerHeadUnchangedAfterDataWrite` | actual heads, addresses, vector widths, kernel floating point |
| Earlier abstract RAM trace | DASHI-only ADDR, VAL, STEP toy protocol, **not RV32 on-wire tokens** | `advance`, `singleWriteReadsBack`, `singleWritePreservesOther`, PC/count proofs | real trace vocabulary, ordering, multi-record instructions |
| Tool-call bridge | captures Qwen native `calc` call at closing tag; firmware outputs `tool_response`; chip token ownership | `TraceToken` and `TokenOwner` separate | tokenizer/class decoder and printed response bisimulation |
| Host driver | prefill loads firmware/RAM snapshot; handles decode/cache and executor; **not an arithmetic tool executor** | `BOOT` finite transition; generic snapshot functions | real `RvChat` cache, startup, lockstep |
| Isolation | Qwen's old attention/GDN state muted for chip tokens; `tau`, `mu`, output code and chip exit | `circuitTraceMutesLanguage`, `languageTracePreservesChip` | actual mute/anti-sink/exit RMSNorm byte-for-byte |
| Numeric implementation | bf16 exact gadget ranges, RMSNorm ballast, fp32 margin, per-layer precision | numerical prerequisites documented | whole compiled IR-to-HF weight numerical compiler correctness |
| GPU execution | HF and Triton circuit paths, lockstep trace reference, optional batch mode | `InstructionSimulation` open witness | IR ↔ HF ↔ Triton GPU same-object; batch nonidentity must be tracked |
| CHIP-8 v1 | distinct earlier CHIP-8 CPU and bignum macros built from similar primitives; source describes 12 chip layers | typed `chip8Core` component | CHIP-8 instruction set/source compiler proof |
| File store | distinct experimental versions; put, append, get, list, delete, named directory and content heads | finite three-name total interpreter and proofs, `filesSurviveNewConversation` | source's hash directory, chunk linkage, 512-file model, real snapshot |
| Security/oversight | separate experiments: compiled monitoring, opaque state tracking | source coverage tagged only | model-specific monitor guarantee, confidentiality, threat model and test protocol |

For the RV32 P2 compiler the upstream layer table in `experimental/riscv/docs/rv32.md` explicitly records L1 control/head state; L2 PC/link bookkeeping; L3–4 ROM/decode; L5 registers/quotient and ALU stage 1; L6 digit-file read/ALU stage 2; L7–8 RAM/multiplication, load/branch/Zba; L9 DROM/multiplier/division; L10 division compare and register destination selection; L11 output code. Upstream reports 99 heads and 1,040,595 nonzero weights at P2. These are **source reports**, not DASHI-reproduced compiler measurements.

The V1 `docs/q35-store.md` 4B store reports 640 chunks × 104 tokens = **66,560** token capacity, with 3-name-style semantics much simpler than its actual 128-directory-entry/chunk-chain layout. The separate later `rv-store` experimental branch has different capacity/limits. Do not fold the 66,560 estimate into the separate ~53,000-token claim. Source snapshot size and file count must be attributed to their exact version.

Source experimental evidence: compliance and programs compared with QEMU, arithmetic benchmarks (40 samples per set), and circuit-owned output/lockstep checks. This is **upstream computational evidence**, not our independently executed validation or theorem. A response can be wrong even with a correct CPU result when the language model misuses or misprints it. An instruction trace matching QEMU does not prove every possible instruction execution.

## Finite proofs added by this tranche

1. **R01 exact row overwrite**. `sameLocationRefl` and `readWriteSame`: a selected row returns the written value. Here a location has two head classes and three rows.
2. **R02 noninterference**. `readWriteOther` proves that different addresses retain the old value under an explicitly supplied inequality witness. `registerHeadUnchangedAfterDataWrite` is the concrete distinct-head instance.
3. **R03 token microprotocol**. `ADDR`, `VAL`, `STEP` compose into `singleWrite`; write value, non-target rows, PC, instruction count and pending address have executable equations.
4. **R04 binary-to-balanced-ternary**. Reuses `BinaryBalancedTernarySubcarrierExact`. `decodedEmbeddedWrite` proves decode-after-embedded-write on the selected row; `embeddedOtherPreserved` proves noninterference. The zero trit remains outside the image.
5. **R05 conditional compiler simulation**. `InstructionSimulation` requires a concrete decoding and a commutation proof. `simulationTwoSteps` composes two *supplied* exact step witnesses; there is **no Qwenputer instance**.
6. **R06 token ownership**. `route` has executable orthogonal Qwen/chip state components; `circuitTraceMutesLanguage` and `languageTracePreservesChip` hold for this abstract route.
7. **R07 file API**. Finite three-name store supports get/put/append/delete/list with read-after-put, read-after-delete, noninterference, append-to-missing and append-to-existing lemmas, plus concrete traces.
8. **R08 snapshot**. State restoration on a fresh language state preserves the saved chip/file component by construction; it does not formalise real serialized cache integrity.

## Exact remaining max-cut, in dependency order

| Target | Required theorem / witness | Prerequisites | Status |
|---|---|---|---|
| W01 | recover upstream commit IDs, ISA/IR vocabulary, exact codebook and source version pins | author source | OPEN |
| W02 | full finite vector/matrix GDN recurrence equals the selected-row `writeRam` under representable ranges | R01–R02 and source math | OPEN |
| W03 | bit-nibble, carry, sign, mul/div/rem, Zba and bignum truth-table semantics through the 11-layer IR | W02, RV32 source | OPEN |
| W04 | every RV32IM/Zba instruction's reference transition commutes with compiled `ADDR/VAL/STEP` trace; no dummy `Machine.step` substitution | W03, ISA source, R05 | OPEN |
| W05 | code ROM/DROM, program counter, call stack, register x0, address map, memory bounds and firmware ABI same-object | W04 | OPEN |
| W06 | RMSNorm/ballast, SwiGLU BF16 and FP32 ranges, token ownership, anti-sink and no-Qwen-state-mutation hold for actual serialized weights | W02–W05 | OPEN |
| W07 | real Qwen tool-call parse/print, 80-token capture and 62-digit firmware scope, error handling, trace invisibility and no host arithmetic | W05–W06 | OPEN |
| W08 | HF compiled weights / IR / Triton evaluator bisimulation incl. reproducible build, kernel version, batch variance, and state snapshot | W03–W07 | OPEN |
| W09 | CHIP-8 earlier compiler, BIOS and macros get own codebook/step simulation without conflating with RV32 | W02, upstream CHIP-8 owner | OPEN |
| W10 | real hash directory, chunk allocator, collision policy, persistence, 5-tool filesystem semantics, capacity and off-model save/restore | R07–R08, W06–W08, exact version | OPEN |
| W11 | independently reproduce source compliance, arithmetic, KL/accuracy, performance and microprotocol checks; archive command/seed/hardware/version receipts | W08–W10 | OPEN |
| W12 | typed privacy/security/monitoring limits and same-object relation to separate oversight and hidden-RNN experiments | W06–W11 and primary sources | OPEN |
| W13 | integrate bounded RAM/trace compression into distributed expert-history experiment; measure end-to-end state bytes, latency, CE and orbit residual, not just symbolic storage | W08, separate distributed-inference owner | OPEN |
| W14 | full fixed-width binary ↔ balanced-ternary word codec over address/ALU/register representations, and correct execution after both encodings | R04 plus existing ternary 27 programme | OPEN |

**Max-cut rule:** R01–R08 are the new bounded finite theorem surfaces. W01–W14 are *not* completed by construction, source claims, compiler analogy, structural coincidence, or a passing screenshot. Completing all of Qwenputer requires actual source compiler verification and independently executable evidence. A proof for the repository's radix-neutral machine cannot by itself establish proof of RV32. E8, FRACTRAN, 369 and ternary are optional representation consumers, not assumptions needed for one-hot RAM correctness.


## Continuation tranche: explicit repository archaeology and exact lemma closure

Date 2026-11-02. All new statements in this tranche are **source-written, not Agda kernel-accepted**. No CI or local Agda checker was run. This tranche adds the following modules to the same PR and its existing TOE/CS roots:

- `QwenputerOneHotDeltaMatrixRefinementExact`: DeltaScalar with explicit difference/replacement laws; selected-row overwrite, non-target-row invariance, data/register separation, and a pointwise commuting square to the pre-existing RAM owner. A constructive Boolean-XOR scalar instance is supplied; it is explicitly **not** BF16.
- `QwenputerRv32RecordCommitExact`: P0/P1/P2 *real source token-family names* (V, R, QS, QD, BD, FLT, HEX, F0/F1/F2, NT, J, ST0/ST1, SS0/SS1, HALT). A typed prefix/commit grammar and exact arbitrary-length prefix theorem show each well-formed modelled record commits exactly once at its terminal token, for a **supplied** abstract instruction transition. Real RISC-V decoding is not assumed. This corrects earlier illustrative ADDR/VAL/STEP wording: that protocol is only a DASHI finite RAM toy model.
- `QwenputerBinaryTernaryRamTraceSimulationExact`: an **arbitrary-length** list of exact binary RAM writes has the same decoded observable memory at every addressed cell under the existing binary-in-balanced-trit embedding. The relation is pointwise and proof-relevant; no function-extensionality or equality of bit/trit carriers is assumed.
- `QwenputerBinary32Framed27CodecExact`: explicit four-byte, 32-bit binary word and lossless framed-27 ternary encoding using the *existing* three-bit→two-trit antipodal codec and 9-bit→three-framed-27 codec. The eight payload bits of each byte occupy a nine-bit word with a fixed zero padding bit. All 32-bit values round-trip. This is a representation theorem, not an RV32 architecture or storage-efficiency theorem.

### Source pin audit (the upstream's own anchors, not new DASHI priority)

- Source architecture table: [Divyansh Agrawal, RV32 inside Qwen3.5, P2 section, commit `3c33d0f` (short source identifier)](https://github.com/divagr18/qwenputer/blob/main/experimental/riscv/docs/rv32.md). This is *not* a recovered full source SHA. A future archive must pin the entire source commit and exact relevant compiler files.
- Source P0 commit rule: PC is inferred from instruction records; `R` refreshes the anchor and does not itself commit an instruction. The final `F0/F1/F2`, `NT`, `J`, store or `HALT` token ends a record. Source P2 extends the stream with `QS`, `QD`, `BD`, and control `SC`. The new typed model does not assert that all source formats are fully parsed or that every P2 token transition has been implemented.
- P2 **uses one-hot** quotient heads because a previous eight-row multi-hot read left FP32 residues; the source's ROM is a controlled two-hot exception. An unqualified theorem that *all* source attention queries are one-hot is false.
- The P2 source table sums to 99 key heads and 42,012 MLP units, with L3–L4 MLP units reported jointly at 4,138; the repository does not fabricate their split.
- Distinguish P0, P1, P2 standalone, P3 merged Qwen tool, CHIP-8 and object-store v1. Their capacities, tokens, ISA subsets, numerical behavior and verification environments are not interchangeable.

### Exact reuse/search ledger

The connected GitHub searches covered the explicit term families:
`Qwenputer`, `GatedDeltaNet`, `DeltaRule`, `oneHot`, `RecurrentState`, `RISC-V`, `RV32`, `ALU`, `compiler`, `trace`, `BitVector`, `Word32`, `microcode`, `bisimulation`, `ternary`, `balanced ternary`, `Tekum`, `storage`, `address`, `memory`, `register`, `firmware`, `SwiGLU`, `RMSNorm`, `BF16`, `FastWeight`, `GDN`, `Chip8`, plus PR searches for machine, codec, binary/ternary, state isolation, signed-history and distributed inference. GitHub code search covers the default branch; this explicitly does not establish exhaustiveness over all past/branch source history.

Recovered exact owners:
`BinaryBalancedTernarySubcarrierExact`,
`FixedNineBitFramed27WordStorageExact`,
`BinaryThreeBitTwoTritAntipodalCodecExact`,
`BinaryThreeBitTrit27FibreLiftExact`,
`TinyRadixNeutralRegisterMachineExact`,
`TinyISAClosedProgramCodebookFibreExact`,
`ShorStandardBinaryTernaryStoredProgramComputerExact`,
`TemporalStorageFibreExact`,
`FractranComputationEquivalence`,
`BinaryFloatingPoint`,
`SelfDescribingProofJacquardTapeExact`,
`FiniteStochasticBisimulationExact`,
`TernarySoftCarryLogicExact`,
`FibreLocalPackedStorageExact`, and
`StorageRecomputeResidualOptimizationExact`.
The latter five are useful consumers or comparator boundaries, not evidence that the actual Qwenputer circuit is already verified.

PR lineage consulted:
[#839](https://github.com/chboishabba/dashi_agda/pull/839) binary/trit CS fibres,
[#1083](https://github.com/chboishabba/dashi_agda/pull/1083) Tekum,
[#1386](https://github.com/chboishabba/dashi_agda/pull/1386) finite-27 codec,
[#1390](https://github.com/chboishabba/dashi_agda/pull/1390) ternary codec convergence,
[#1442](https://github.com/chboishabba/dashi_agda/pull/1442) finite signed-history experts,
[#1445](https://github.com/chboishabba/dashi_agda/pull/1445) machine/CNF bitwords and
[#1456](https://github.com/chboishabba/dashi_agda/pull/1456) this tranche.
First-implementation priority cannot be inferred from PR title or number; individual earliest commits still require source archaeology.

### Recut of exact max-cut after implementation

- **W02 (partly paid)**: abstract one-hot matrix/RAM commuting square and Boolean-XOR instance now source-written. Actual bf16 difference arithmetic, gate/beta exactness, whole-head output normalization, two-hot ROM and real Qwen tensor equality remain **OPEN**.
- **W04 (partly paid)**: source-named record grammar and terminal-once invariant source-written. Exact RV32 step semantics and compiler-token bisimulation remain **OPEN**.
- **W14 (partly paid)**: pointwise simulation of arbitrary-length writes, and a complete padded 32-bit binary↔framed-27 representation roundtrip now source-written. Correctness of an *actual* 32-bit RV32 ALU in the framed ternary storage and exact endian/address/program equivalence remain **OPEN**.
- **W01/W03/W05–W13**: not yet closed by these new constructions. They require authentic source IR, codebook, register/ROM/RAM map, real compiler/export, finite numerical preconditions or measured hardware execution.

#### Remaining terminal theorem requested before full Qwenputer promotion

For a fixed source commit `c`, compiled checkpoint `W(c)`, and reference RV32 machine `M(c)`, build a concrete decoder `decode_c` and prove for **every valid compiled state** and emitted instruction record `r`:

`decode_c (compiledRun W(c) r s) ≡ referenceStep (decode_c s)`,

together with token-owner isolation, no-spurious-state-update, required exact numerical bounds and compositional run semantics, then independently replay actual QEMU compliance and C/MicroPython programs. This theorem is not supplied by the new finite proof models and is not presently promoted.



### Source qualification and later strengthening

The P2 source reports the 32 KiB RAM at 0, DROM at 0x20000 (128 KiB) and ROM at 0x40000 (256 KiB). `QwenputerRv32LayerScheduleSourceExact.p2Memory` records these values. The P3 source says its new 80-token capture window is at 0x8000 with 16 bytes per token. The new arithmetic lemmas prove only the stated **1280-byte capture budget** and that the capture starts at the numerical end of P2 RAM; they do **not** invent a P3 memory-extension implementation.

`QwenputerOneHotDeltaMatrixRefinementExact.matrixAndRamSameAfterEveryWrite` strengthens the prior selected-row result to **arbitrary-length** matrices of typed vector writes, under a provided DeltaScalar algebra. It is exported to TOE. `QwenputerHybridStateAndFileStoreExact.allCircuitStepsMuteLanguage` and `allLanguageStepsPreserveChip` likewise strengthen the abstract state isolation equations from one token to any natural-number-length burst.

`QwenputerRv32RecordCommitExact` now includes the source's `BYTE` putchar record, plus its `SC` control constructor. The latter remains opaque because the exact P2 `spec.py` implementation and any instruction-commit interpretation have not been reconstructed. Real program counter anchoring, R refresh timing, QD quotient-digit semantics, BD carry and memory writes are explicit W04/W05 gaps, not silently discharged.

**Corrected version-scoped claim:** According to the upstream RV32 documentation, MicroPython ran on P2's standalone core and executor. The P3 merged Qwen model's MicroPython bridge build was not yet complete. It is incorrect to promote the P2 MicroPython demonstration to a test of MicroPython *inside* the P3 merged language model. The blog's general wording cannot replace the detailed source's version distinction.

**Verifiability restriction:** The user's repositories are accessible through the GitHub connector. The upstream `divagr18/qwenputer` Python `spec.py` and `ref.py` files were not retrievable from that connector in this execution (404). We could read the public upstream architectural documentation, but did **not** inspect or replay those concrete source files. The full-source decoder/compiler proof cannot honestly be marked complete.

## Local follow-up checks (not executed in this GitHub-only tranche)

```bash
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerGatedDeltaArchitectureExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerHybridStateAndFileStoreExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerOneHotDeltaMatrixRefinementExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerRv32RecordCommitExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerBinaryTernaryRamTraceSimulationExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/QwenputerBinary32Framed27CodecExact.agda
scripts/run_agda29_parallel_check.sh DASHI/ComputerScience/ComputerScienceFibreFoundationValidationExact.agda
```

Finite-state auxiliary regression (independent of Agda, not yet executed here):

```bash
python3 scripts/check_qwenputer_finite_semantics.py
```

This enumerates all 64 six-bit RAM states, six addresses, both writes, all queried rows, one ADDR/VAL/STEP transition, ternary-image preservation, all 4^3 three-name store states with three suffixes, and the reported head/MLP totals. Its success would provide a computational regression only, never a kernel proof or checkpoint verification.

For final promotion use the pinned Track A toolchain and existing repo rules. The source branch/PR establishes implementation existence, not type-check, CI or a theorem's first validated timestamp.

## Suggested cross-repo contracts

For `dashi_lean4`, use Agda as the golden finite trace/RAM owner. Only add a Lean mirror after checking an existing Lean bitvector/ISA or finite-state trace owner. For distributed inference, compare signed-history expert transfers and E8/ternary coordinate charts against the exact canonical state, with measured time/bytes and independently scored outputs. No inference that a ternary encoding improves throughput without a measurement.

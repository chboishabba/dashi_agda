# DASHI Max-Cut / OpenAI Math — exact proof-state and dependency cut
**Date:** 2026-10-31. **Source branch:** `chboishabba/dashi_agda@integration/openai-math-corpus` (PR #1212). Lean secondary `chboishabba/dashi_lean4@integration/openai-math-corpus` (PR #78).
**Definition:** “max-cut” here is dependency-graph prioritisation. OpenAI family 102 graph Max-Cut hardness is a **separate mathematical problem**. Do not conflate them.

## The result actually pursued
For any ORIGINAL `ConcreteBooleanCircuit inputs` with gate count `g`, prove a **same-assignment and same-count** reduction from its accepting input vectors to a width-3 `SAT.CNF (Fin (inputs + g))`, with bounded variable count, canonical bit encoding, construction/runtime/visited-space cost. Keep *Agda source proof* and *Lean kernel* evidences independent.

## Implemented source owners (not all kernel-accepted)
| Layer | Concrete owner/declaration | Exact evidence/status |
|---|---|---|
| Original DAG/gate semantics | `PNotEqualsNPConcreteBooleanCircuitDAGExact.evaluateProgram/evaluateCircuit` | Prior in-repo Agda source, PR #1040 lineage; **do not duplicate** |
| Original shared SAT equivalence | `PNotEqualsNPConcreteCircuitSharedSemanticsExact.sharedAcceptanceExact` | Prior source, existential SAT not automatically #SAT |
| Canonical auxiliary assignment | Same semantics owner `assignmentFromProgram`, `sharedConstraintsGiveRealization` | Prior source; Cook assignment has unconstrained Nat→Bool tail |
| Countable finite model | `OpenAIMathFiniteSupportedTseitinModelsExact.FiniteSupportedModel` | #1212 source |
| Numerical source-input versus canonical-gate count | `finiteSupportedTseitinCountExact` | #1212 source-written, **Agda kernel pending** |
| Finite CNF bits/splitting | `bitsVecRoundTrip`, `globalFiniteVectorsRoundTrip`, `inputVectorLookupExact` | #1212 source-written, reuses older canonical block/tape slice owners |
| Classical 3-bit CNF | `FixedWidthTruthTableCNFExact.truthTableCNF`, `CNFVariableRenamingExact`, `CNFPlacedConstraintConjunctionExact` | Established original source; fixed width 3 only |
| Original full list-CNF | `OpenAIMathSharedTseitinGateCNFExact.circuitPlacedCNF` and `circuitPlacedCNFClosedClauseCount` | #1212 source-written: **exact 4g+1 ordered clauses** |
| Original whole CNF gate-relations semantics | `WholeCircuitPlacedMeaning`, `wholeCircuitPlacedCNFSound/Complete` | #1212 source-written, **not** yet global gate evaluation |
| Output-determination improvement (2026-10-31) | `localGateOutputForced`, `localGateOutputComplete`, `placedGateOutputForced`, `placedGateCNFOutputSound/Complete`, `compiledProgramLastGateOutputForced` | **New #1212 source**, original CNF owner, inherited `Rename.pullbackLookup`; kernel pending |
| Optional optimized same-CNF | `OpenAIMathSharedTseitinOptimizedCNFExact.optCircuitEqualsOriginal`, `optCircuitThreeClauseBudget` | #1212 source-written; one clause constant, two NOT, three AND/OR: **≤3g+1 ordered clauses**, without changing canonical old owner |
| Exact finite count comparison (two CNFs) | `optCircuitCountEqualsOriginal` | #1212 source-written pointwise count equality, **not input count** |
| Elementary list CNF normalization | `duplicateClauseCountInvariant`, `tautologyRemovalCountInvariant`, `duplicateLiteralCountInvariant` | #1212 source-written, **not yet a Lean Finset implementation** |
| Independent executed code | Local Python finite gate output 22,500 placements incl. 4,784 aliases, prior bounded 375 DAG fixtures/10,850 valuations; broader earlier receipts separate | **Executable evidence**, not Agda/Lean kernel |
| OpenAI fixed-width machine/count theorem | `openai/math` family 378 `SqrtLogSpace.exact_count_and_sat` | External Lean original ownership; upstream source and formalization separate from DASHI vendor pin |

## Priority DAG / genuine outstanding cut

**P0 — kernel smoke / trust** (independent verification gate). Exact checkout Agda + pinned standard library: typecheck the three existing #1212 modules and their transitive dependencies; zero unsolved metas/postulates where the chosen “golden” safe scope requires; do **not** add a protected ESD dependency or promote source-written statements before kernel receipts. Then port source-accepted owners to Lean; avoid duplicating unfinished code.

**P1 — LAST missing semantic induction (highest mathematical leverage).** Prove that `ProgramPlacedGatesValid` implies the **original** previous gate values are `Circuit.evaluateProgram` on `inputVectorFromGlobal`. Recursive proof on `GateProgram`: use `Rename.pullbackBits extendEarlierFin` to preserve all earlier values; use the **new** `compiledProgramLastGateOutputForced` for each fresh gate; prove chronological global gate suffix is the reverse of `evaluateProgram` (original newest-first convention). Close both soundness and completeness. This is unpaid—not a mere naming mismatch.

**P2 — real count equality from INPUT circuits to COMPILED CNF.** Transport P1 through the existing `FiniteSupportedModel`, `finiteSupportedTseitinCountExact` and `sumFiniteBits` to obtain
`countSourceCNF (circuitPlacedCNF c) ≡ countAcceptedCircuitInputs c`.
Then compose the already source-written `optCircuitCountEqualsOriginal` to obtain the optimized count without repeating a second induction. Include the zero-gate case and duplicate-wire countercontrols. **Not yet proved in Agda.**

**P3 — upstream SAME-CARRIER finite representation.** Write/evaluate Agda list literals as actual `Finset (SAT.Literal (Fin v))`, and list of clauses as `Finset Clause`; show pointwise truth under dedup, exact count equality, width≤3, and Finset.card≤3g+1. Never claim `Finset.card=3g+1`: different ordered clauses can collide after literal dedup. The current elementary Agda normalization lemmas are donors, not the completed Lean conversion.

**P4 — encoded binary size and uniform compute.** For v=inputs+g, width 3 and m≤3g+1, reuse OpenAI `Encoding.formulaBitLength_upper`:
`L ≤ v + 2 + (24v+28)(3g+1)`.
Prove the concrete conversion algorithm, unary/framed output, finite enumeration and **runtime and visited-space** overhead on the target machine model, then apply OpenAI 378. This is not automatic from source-list clause count or a decision-oracle query bound.

**P5 — existing external cross-model donors, NOT a new priority claim.** `TSavo/eth-bridge` (2026-10-27, original external contributor) has `Bridge.BitLength.formulaBitLength_poly`, `Bridge.FrontEnd.pre_polyT`, `Bridge.Main.ethIsFalse_of_claim` crossing OpenAI canonical CNF to Anthropic's 3SAT Turing framework. Actual sources inspected; their Lean theorem bridge does **not** automatically prove DASHI's distinct Agda list CNF count semantics. Prefer import/adaptation over reimplementation; retain original authorship, verify original pinned versions and trust receipts.

**P6 — graph Max-Cut 102 as a DIFFERENT problem.** Native Agda #1438 and Lean #103 already own the 27-vertex 54-edge bipartite weighted grid, its selected optimal checkerboard and typed QID atlas. For strict positive weights, connectedness permits a two-optima-up-to-complement theorem, but **Agda kernel proof outstanding**. OpenAI 102 requires unrestricted variable-size simple unweighted graph instances and gap-preserving polynomial reductions. No fixed 27-vertex quotient proves this hardness; separate from the #1414 27 *functions* C3 quotient.

**P7 — QID/Ibrahim/TOE and priority.** Reuse source-indexed QID concept bindings and actual instance identity firewall; retain original #772 Ibrahim snowball/Pareto and Monster3B custody, C3 even/odd original owners, and ESD import-only prohibition. Only import into `EverythingTOESymmetryResolved369`/`Unifier` after the relevant mathematical carrier and kernel proofs pass. Link every derived object to original mathematical published author, original in-repo PR commit/date, actual new code author, executed numerical receipt, and kernel receipt as **separate** fields.

## Boundary and branch policy
- P0–P4 concern **original concrete SAT circuit**, not ETH independently proved by DASHI and not P=NP.
- Separate **source written**, **finite executable test**, **Agda checked**, **Lean checked**, **same-object application**; never promote between columns.
- Branch PR #1212 is the active integration owner. PR #1438 weighted grid and #1414 orbit symmetry are distinct owners; no modifying ESD, no CI requirement for research source progress.
- This document is the concise state-of-work index. Existing longer plans retain detailed dependency archaeology; update this ledger when a gate actually changes status.

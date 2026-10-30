# OpenAI Math Corpus Agda Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Record the pinned OpenAI mathematics corpus as an attribution-safe cross-prover source for Agda.

**Architecture:** Mirror only immutable upstream identity, cross-prover authority status, routing metadata and focused exports. Lean proof objects are never re-labelled as Agda proofs.

**Tech Stack:** Agda, Git/GitHub.

**Spec:** `docs/superpowers/specs/2026-10-16-openai-math-corpus-design.md`

## Global Constraints

- Pin `openai/math` exactly at `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
- Record upstream Lean toolchain exactly as `leanprover/lean4:v4.34.1`.
- Preserve Apache-2.0 attribution.
- Keep manuscript, upstream Lean and Agda theorem authority distinct.
- No kernel-green claim without execution evidence.

## Review Focus

- Cross-kernel theorem promotion must remain false by default.
- Relevance routing must not pay same-object transport.
- Upstream movement must not alter the pinned receipt.
- The focused rollup must not create a dependency on the upstream Lean environment.
- Regression assertions must match the production names exactly.

---

Execution method: native/inline; CI is not a blocker for this tranche.

### Task 1: Regression owner
- [x] Create `OpenAIMathCorpusRegression.agda` before production.
- [x] Preserve source-order RED boundary.

### Task 2: Upstream receipt
- [x] Create `OpenAIMathUpstreamReceiptExact.agda` with exact pin/toolchain/license and promotion-state vocabulary.

### Task 3: Priority atlas
- [x] Create `OpenAIMathPriorityAtlasExact.agda` with routing-only programme classifications.

### Task 4: Focused rollup
- [x] Create `DASHI/Research/OpenAIMath/Everything.agda`.

### Task 5: Repository export and PR
- [ ] Add the focused rollup to the nearest safe canonical research/global rollup.
- [ ] Audit exact pin and non-promotion boundaries.
- [ ] Open a draft PR with kernel-pending status.


## 29 October 2026 — Source-first new proof: unique auxiliary-gate extension

**Existing owners actually inspected (default-branch source, not PR summaries):**
- `DASHI/Mathematics/Complexity/PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda` contains `sharedConstraintsGiveRealization`, `assignmentFromProgram`, `assignmentFromProgramInputCorrect`, `assignmentFromProgramGateCorrect`, `acceptedInputGivesSharedSatisfiable`, `sharedSatisfiableGivesAcceptedInput`.
- `PNotEqualsNPConcreteCircuitSharedCompilerExact.agda` owns gate-index numbering and actual shared/Tseitin formula construction.
- `PNotEqualsNPConcreteCircuitSharedUpperBoundExact.agda` owns linear formula **syntax-node** size bounds. Its upper bound is NOT a bit-encoding bound or TM runtime theorem.
- `PNotEqualsNPConcreteBooleanCircuitDAGExact.agda` owns actual acyclic gates and a finite input vector.
- Prior #1040 (created 2026-09-24, merged by 2026-10-04) retains original DASHI source ownership, before the public OpenAI October 26 ETH release. Historical Cook/Levin and Tseitin prior mathematics are inherited, not DASHI-invented.
- Existing #772 BIDI recursive selective invalidation/Pareto owner and #1129 polynomial SAT frontier remain independent. Agda #1414 distinct 27→11→7 and parity owners were separately reviewed; no duplicate C2 apparatus is made here.

**New in THIS existing Agda OpenAI-ingestion PR #1212:**
- `DASHI/Research/OpenAIMath/OpenAIMathSharedTseitinUniqueExtensionExact.agda` (commits `537d8b2369f8c37e7fb5d5ddcc08927dd489ca8b`, implicit-index repair `13b64a8bee7ec6bebf9052b608dee711ed7ed8c1`, shared-acceptance extension `3c0a0672971ce365735f0dbbf5bce5411751a363`).
- Exact finite-coordinate carrier distinguishes `Fin inputs` from `Fin gates` and maps to original gate variable numbering. `canonicalAgreementOnUsedCoordinates` directly composes previously constructed `sharedConstraintsGiveRealization` with `assignmentFromProgramInputCorrect`/`GateCorrect`. `uniqueAuxiliaryGateValues` and `uniqueUsedCoordinates` establish pointwise that any two satisfying assignments with equal input vectors agree on every **USED** circuit variable. `acceptedFormulaRealization` and `uniqueAcceptedFormulaModelsOnUsedCoordinates` upgrade the statement to models of the actual shared acceptance formula, not an invented surrogate.
- Focused research `Everything.agda` now imports this source owner via commit `931cd5fd44d9fc10ba6744c0cd2e7ed6971e4519`. No protected ESD/global root edits.
- Independent executable finite test `scripts/check_openai_shared_tseitin_parsimonious.py` committed `c635b177c5b78d4628d7684de62adae730db534e`. An independently authored local equivalent script **EXECUTED and PASSED 59,290 exhaustive small Boolean DAG/output cases**, with gate-only implication and unconstrained-tail negative controls. The GitHub-committed script was not run in the exact checkout; Agda compiler is not installed here; no kernel receipt.

**Genuinely new precise limit:** `Cook.Assignment` is an unbounded `Nat → Bool`, and the shared constraints do not fix its unused tail. Thus literal global uniqueness or equality of counts over ALL `Nat → Bool` assignments would be false/ill-typed as a finite #SAT statement. The source-witness theorem proves uniqueness only on the `inputs + gates` finite support, sufficient as the **functional determination component** of a parsimonious encoding; finite supported-model cardinality and an explicit bijection remain unpaid.

### Updated graded max-cut / Pareto tasks
- [x] Reuse exact older DAG/Tseitin proof terms and prove unique auxiliary extension on all used variable indices (SOURCE-WRITTEN, Agda KERNEL PENDING).
- [x] Preserve original #1040 owner, record independent 59,290-case local computational evidence and negative controls.
- [x] Import the new owner via dedicated OpenAI Research `Everything.agda` while leaving global TOE roots unchanged until kernel acceptance.
- [ ] Kernel-check on pinned Agda/stdlib; eliminate any syntactic/type inference errors, record exact compiler SHA and trusted axiom audit.
- [ ] Finite-support model bijection: formally count *only* valuations of `Fin (inputs+gates)`, and prove acceptance-model cardinality equals accepting-input cardinality with unique auxiliary extension. This is the exact missing #SAT lemma.
- [ ] Connect existing `Cook.BooleanFormula` to bounded-width `OAI.Algorithms.SubexponentialSAT.SAT.CNF (Fin n)` using a computable **parsimonious** CNF compiler. Verify actual literal clause width, variable count (including fresh gates), canonical `Encoding.formulaBitLength` and bit/runtime overhead; ordinary polynomial-time reduction is insufficient to preserve a claimed `2^{o(n)}` bound in the original parameter.
- [ ] Port or witness the OpenAI 378 **source proof** in a separately pinned Lean environment; keep existing Oct-6 `openai/math@1581d4...` vendor immutable until the upgrade is explicitly performed. Upstream actual solution is `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` in `SqrtLogSpace/Final.lean`, not the Comparator challenge containing `sorry`.
- [ ] Reconcile the graph Max-Cut 102 (variable-size simple unweighted gap theorem) vs our fixed finite orbit objectives; preserve the two-vertex strict-loss counterexample and no automatic approximation-hardness transfer.
- [ ] Source/date audit and selective invalidation via #772; record theorem vs framework, inherited classical art vs original DASHI proof, source-written vs executed vs kernel acceptance.

**Status:** A narrow, high-value conditional bridge is committed. OpenAI's announced ETH refutation is NOT re-proved in Agda; neither #SAT finite counting bijection nor polynomial-encoding/complexity transfer is closed. New source and rollup need exact-head Agda typecheck.


## 30 October 2026 — FINITE-SUPPORT FIRST, no duplicate SAT compiler

**Before authoring:** checked actual default-branch `PNotEqualsNPConcreteBooleanCircuitDAGExact`, `PNotEqualsNPConcreteCircuitSharedCompilerExact`, `PNotEqualsNPConcreteCircuitSharedSemanticsExact`, `PNotEqualsNPConcreteCircuitSharedUpperBoundExact`, and pre-existing `PNotEqualsNPQ1TruthTableRepairGeneratorExact.vecExtensionality`. Searched repository code for `finite model cardinality`, `Vec Bool enumerate`, `unique extension`, `≡-by-lookup`, and `vecExt`. Inspected *current heads* of Agda #1212/#1414/#1407/#1040 and Lean #78, not just PR summaries. Also directly checked OpenAI `math/lean/OAI/Computability/MaxCut/Model.lean`, `SubexponentialSAT/SqrtLogSpace/Final.lean`, and docs 378. No ESD write.

**New in existing original Agda #1212 branch:** `DASHI/Research/OpenAIMath/OpenAIMathFiniteSupportedTseitinModelsExact.agda`, commits `155c14b8f4fc0b5082dceb046023af2494504511`, `d3cd8bae127599f63191cb90ea3c275cba6a376a` (reuse existing vector extensionality rather than local duplicate), and `bcfa3390f6bec022426d4f8ec60da776edd8ef4d` (bridge actual Cook shared formula). Focused `DASHI/Research/OpenAIMath/Everything.agda` imports it as of `c63c6041ab8bbd4e11577c452970d55ffd7fc5bb`.

**Formal content at SOURCE WRITTEN / KERNEL PENDING:**
- `FiniteSupportedModel circuit` has precisely finite `Vec Bool inputs` and `Vec Bool (gateCount circuit)` as counted data; `auxiliaryCorrect` ensures all gate bits are the actual DAG evaluations; `outputTrue` ensures acceptance.
- `encodeAccepted` and `decodeSupported` between the *same original circuit*'s accepting input Sigma and supported model; `decodeEncodeAccepted` is an exact round trip, and `encodeDecodeInput`/`encodeDecodeAuxiliary` recover **every finite data coordinate** using the earlier Q1 vector extensionality owner, without duplicating proof algebra.
- `finiteSupportedGivesSharedSAT` and `sharedSATGivesFiniteSupported` directly reuse the source-owner `acceptedInputGivesSharedSatisfiable`/`sharedSatisfiableGivesAcceptedInput`; thus this normal form is linked to the **original** shared/Tseitin formula, not a surrogate.
- This does not yet establish literal record equality including proof fields, nor a formal `Nat`-valued counting theorem. Arbitrary `Cook.Assignment = Nat → Bool` tail bits remain uncounted because the source constraints do not fix them.

**Executed external-to-kernel finite regression:** a locally executed new independent Python enumeration passed `59,293` acyclic DAG/output cases (including no-gate circuits, 1–2 input wires, gate depths through three), with exactly equal number of accepted inputs and finite canonical Tseitin models, and a negative control confirming a one-way gate implication can double the number of witnesses. The existing `scripts/check_openai_shared_tseitin_parsimonious.py` was subsequently **extended in place**, rather than duplicated, to include the three zero-gate output cases and assert the resulting total of 59,293 (commit `cb96df6eba34118ed42a47a891490c7a7457e626`). An independently authored local equivalent was executed; the exact-head committed script and Agda kernel still have no execution receipt. Hence mark **local numerical EXECUTED**, **source-written proof**, **Agda KERNEL PENDING** as three distinct receipts.

**New 29 October research snowball / independent authorship:** Jizhou Guo's follow-up in `aster2024/openai-math-followups/tensor-contraction-consequences` (paper dated 2026-10-29) gives **conditional** sparse-graph TSP, Hamiltonian cycle/path, longest-path, Steiner-tree and other algorithmic consequences under *Theorem D.1* from OpenAI's ETH manuscript. The follow-up itself says the OpenAI Lean family-378 fixed-width counting theorem does **not** verify that separate contraction theorem. This is a promising TSP/A-star path for existing `PathfindingFibreFamilyExact`, but no unconditional theorem transfer or runtime/space improvement may be claimed. Preserve original OpenAI manuscript and Jizhou Guo follow-up ownership independently, not as original DASHI constructions. Reference https://github.com/aster2024/openai-math-followups#tensor-contraction-consequences .

### Updated max-cut / Pareto / Ibrahim worklist
- [x] Reuse #1040 input→DAG evaluation and Tseitin semantics, #1040 machine-model boundaries, and existing Q1 `vecExtensionality`; new finite-supported *data* round trips, actual SAT satisfiability arrows (source).
- [x] Independent local 59,293-case exact enumeration and one-way implication counterexample (executed Python), while preserving original ownership of the previous committed finite script.
- [ ] Exact-head Agda typecheck including entire OpenAIMath rollup and transitive Q1 owner; do not call source-written code Agda kernel accepted until receipt. Verify dependency closure and no postulates in imported trust base.
- [ ] **Full parsimonious cardinality:** choose existing finite enumeration and decidable-equality owners, prove model-proof irrelevance / finite support bijection, then `#accepted inputs = #supported SAT valuations` as actual Nat counts, not merely an assumed bijection.
- [ ] **OAI CNF:** explicit bounded-width (including width-three or justified width-k) definitional conversion with *unique auxiliary extensions* and no spurious multiplicities; bit-encoding size, input/variable growth, uniform executable computation and counting preservation.
- [ ] **OAI 378:** transfer exact count onto actual `SAT.CNF (Fin n)` and `Encoding.formulaBitLength`, with real machine step and all-prefix visited-space bound; never relabel an oracle-call or syntax-node theorem as a machine runtime proof.
- [ ] **Max-Cut 102:** use upstream `Graph.cutSize` `u<v` on symmetric loopless 0/1 adjacency, positive scale, and output bits. Reuse existing `FiniteWeightedThresholdGraph` only through an explicit actual objective-preserving adapter; orbit-invariant maximum need not equal unrestricted maximum (two-vertex swap).
- [ ] **TSP Guo:** inspect Theorem D.1's exact hypotheses and status; formalize a specific sparse-graph reduction only if counts/size/time and input encoding can be transported, independently from OpenAI 378. Existing A* admissibility remains open, not implied by conditional sparse TSP algorithms.
- [ ] **Attribution:** retain classical Cook/Tseitin, #1040 original Agda author, #1212 new finite model, #1414 original C3 owners, #772 Ibrahim Pareto worklist and Monster 3B custody, and Guo independent follow-up by source/date and proof status.


## 2026-10-30 second source-first continuation — actual Nat-valued finite #SAT equality

**Confirmed live repository source:** Agda #1040 owns the real `ConcreteBooleanCircuit`, `evaluateProgram`, `evaluateCircuit`, shared Tseitin compiler, and existential SAT equivalence; the older Q1 truth-table owner owns `vecExtensionality`. The current #1212 finite support already has `FiniteSupportedModel`, `encodeAccepted`/`decodeSupported`, and arrows to the ORIGINAL Cook SAT formula. Also inspected live #1414 `PolynomialC3S3RationalCharacterAlgebraExact.agda`, now containing `positiveField`/`negativeField` and reflection transport: do not duplicate those parity operators. Inspected `DASHI/Unified/Everything.agda` actual imports (Ibrahim/Pareto/369 owners) and upstream actual OpenAI family-102 MaxCut model and family-378 exact-count machine source; reviewed current heads Agda #1212/#1414/#1407 and Lean #78/#80. Default-branch searches included `sumAll`, `enumerateAssignments`, `countAssignments`, `vecExt`, `bitCardinality`, `countModels`; no exact reusable numerical count-of-shared-circuit declaration was found, so the missing finite count lemma was extended **inside the existing owner**, not a new SAT compiler.

**NEW CODE** in `DASHI/Research/OpenAIMath/OpenAIMathFiniteSupportedTseitinModelsExact.agda`:
- Commit `65fea890b54d281b9d41febf4b44afe0415a10a4`: `sumBoolVectors` enumerates finite Boolean vectors structurally with Nat weights; `sumBoolVectorsExt` and `sumBoolVectorsZero` reuse structural induction; `equalBoolVectors`, `sumExactlyOneEqualVector`, `countAcceptedAuxiliaries` prove exactly one canonical auxiliary vector for an accepted input and zero for rejection. `countAcceptedCircuitInputs` and `countFiniteSupportedTseitin` are **two separately computed Nat-valued counts**, and `finiteSupportedTseitinCountExact` proves their equality by indexed summation and the unique extension.
- Commit `d3c1719f7097b9fe4f3c92decb80b60b57883f9b`: `equalBoolVectorsSound`/`equalBoolVectorsRefl` and `finiteSupportedModelIsCounted`/`countedPairGivesFiniteSupportedModel` connect the counted *Boolean predicate* in BOTH directions to the already-existing original `FiniteSupportedModel` proof carrier. This closes the former disconnect between a syntactic count expression and actual modeled gate correctness. All source declarations are Agda **SOURCE-WRITTEN; KERNEL PENDING**, no postulates, holes, or unsafe termination pragmas in the amended source.
- Independently executed local Python full regression **59,293** finite circuit/output cases, including zero gates and rejection, with exact equality of accepted input count to canonical auxiliary model count and a counterexample for one-way implications. This is an executed finite computational test, NOT Agda kernel proof. GitHub exact script execution still pending.

**Scope of new theorem:** `#(accepted input vectors) = #(accepted finite input+gate vectors)` for each actual concrete DAG, with used coordinates only. This is **a real numeric finite count theorem at source level**, not just model equivalence, but it does not establish an arbitrary encoded `CNF (Fin n)` counting theorem until the actual bounded-width CNF encoding is proven parsimonious and bit-length/resource bounds are transported. The original Cook assignment `Nat -> Bool` has infinitely many irrelevant coordinates, so no cardinality of all Cook.Assignment objects is inferred. The theorem's source status must not be promoted to Agda-kernel-accepted, and no claim of a better time complexity than OpenAI is licensed.

**Next max-cut / Pareto obligations**:
- [x] Source-write exact Nat finite-input-vs-finite-Tseitin-model count equality, plus both semantic-direction links to counted carrier (Agda kernel pending).
- [x] Execute 59,293-case finite regression with mismatch/one-way negative control independently.
- [ ] Actual pinned Agda/stdlib kernel typecheck and transitive trust audit. In particular verify pattern clauses, rewrite reductions and the source import graph; if any fails, correct before promoting to theorem receipt.
- [ ] Map existing shared logical gate formula to *three-literal clauses* with a parsimonious gate-variable extension, `n+g` variable count, explicit clause bound, explicit encoding bits. This is the next necessary interface to OpenAI family 378.
- [ ] Compose bit-level runtime and polynomial all-prefix tape-space bounds, not just original formula syntax-node or oracle-query bounds. No automatic P=NP consequence.
- [ ] For family 102, preserve literal finite simple unweighted `Graph.cutSize` / positive `ScaledGraph.scale` and uniform polynomial binary printer. Prove explicit quotient objective identity and unrestricted-optimum loss guard before any claim of gap preservation. Existing weighted-threshold residual graph is a proximal source, not same-object.
- [ ] Highest-alpha external follow-up: Jizhou Guo's 29 October sparse-graph TSP consequences are **conditional on manuscript Theorem D.1** and distinct from published Lean family 378. Preserve source authorship and avoid converting TSP/A* heuristic experiments into a machine theorem.
- [ ] Prior #772 Ibrahim/Monster 3B custody, source/author dates, selective invalidation and golden-Agda/Lean-secondary authority must remain attached to any later TOE import.


## 2026-10-30 third continuation — proximal *existing* fixed-width Cook–Levin CNF reused

Further actual default-branch source search for `CNF`, `toCNF`, `3CNF`, `bounded-width CNF`, `Tseitin`, `sumAll` found the previously developed source owners:
- `DASHI/Mathematics/Complexity/FixedWidthTruthTableCNFExact.agda`: `Bits n`, `CNF n`, `truthTableCNF`, `truthTableCNFSound`, `truthTableCNFComplete`, `canonicalTruthTableCNFEquivalence`; its truth-table compiler is exponential in WIDTH `n`. **Only use with a fixed local window** (3 here), not directly on the whole input circuit!
- `DASHI/Mathematics/Complexity/CNFVariableRenamingExact.agda`: exact local-to-global variable placement, `renameCNF`, `pullbackBits`, `renamedCNFEvaluation`, and placement proof.
- `DASHI/Mathematics/Complexity/CNFPlacedConstraintConjunctionExact.agda`: `compilePlaced`, `compilePlacedAll`, `compilePlacedAllSound`, `compilePlacedAllComplete`.
- `DASHI/Mathematics/Complexity/FixedWidthCNFToCookFormulaExact.agda`: existing CNF→Cook `cnfEvaluationOnBits` and exact SAT witness arrows, but NOT a new Cook→CNF count theorem.
- `DASHI/Mathematics/Complexity/CookLevinPolynomialSizeExact.agda`: native replicated fixed-template polynomial SIZE results for tableau encodings, not automatically the original circuit-machine runtime bound.

**New code in original Agda #1212:** `DASHI/Research/OpenAIMath/OpenAIMathSharedTseitinGateCNFExact.agda` commit `c90781f2ab819aff40a7702834945cead39749f1`; imported via existing `Everything.agda` commit `081989b92faa4a3b5b013841f015a3e4e2e1b0f7`. Its `localGateConsistent` is literally parameterized by the prior `Circuit.Gate inputs gates` constructors; `actualGateWindow` takes their actual source-evaluated output/operand values; `localGateCNF` calls the original **three-bit** `CNF.truthTableCNF`, with source-written `localGateCNFSound`, `localGateCNFComplete`, and `actualGateCNFAccepts` directly calling existing CNF theorems. No new CNF compiler, no duplicated parity, no unsupported whole-circuit equivalence claim. Fixed width 3 makes at most 8 rejected rows per gate even when input width or gate count grows. Both const and unary gates use explicit dummy operands; repeated references require no disjointness assumption. Source-written, Agda kernel pending.

Extended existing `scripts/check_openai_shared_tseitin_parsimonious.py` in place at `9347030d6367993ec933717dfa6b3daed709a2dc`: 40 checks (5 gate kinds × all 8 local assignments), each requiring exact CNF/gate truth equivalence and ≤8 width-3 clauses. An independent local Python calculation **EXECUTED and PASSED** all 40, each kind producing four forbidden 3-clauses. This is separate from the previously executed 59,293 finite whole-DAG counting regressions. Exact GitHub script checkout execution and Agda kernel both remain pending.

**Next actual global assembly / highest-alpha cut:** instantiate each `Circuit.appendGate` as a `CNFPlacedConstraintConjunctionExact.PlacedPredicate 3 (inputs + totalGates)` with **certified Fin-index renaming**: output variable = existing `Compiler.gateVariableIndex`, left/right operands = the existing `WireRef` owners, true output literal = existing `Circuit.outputWire`. Reuse the existing original `CNFVariableRenamingExact` and `compilePlacedAll` proof; keep each local window at width 3, control `n+g` distinct variables and ≤8g+O(1) clauses, establish parsimonious finite model-count equality to the source `countAcceptedCircuitInputs`. Then audit actual OpenAI canonical bit encoding length and machine runtime/space. This global placement and bit bound are **still unpaid**, not an excuse to build a second compiler. A pure whole-input truth-table CNF would cost (2^n) and destroy the ETH parameter claim.

**Trust ledger:** classic Cook/Tseitin authors, prior DASHI CNF/Cook–Levin proof owners, newly authored #1212 adapter, OpenAI 378 machine theorem, independent Oct-29 Guo conditional TSP, and Ibrahim Monster 3B custody remain separately credited. No ESD or CI edits. No #SAT theorem has been kernel-verified in this pass.


## 2026-10-30 fourth continuation — original compiler gate numbers into placed CNF

**Actual prior code inspected before this implementation:** the original `Circuit.WireRef` and `Circuit.Gate` constructors; `Compiler.gateVariableIndex inputs index` and `gateConstraintFormula`; the earlier `Semantics.gateVariableIndexBelowNext` proof; the P-vs-NP `PNotEqualsNPCookIndexedFormulaBridgeExact` use of `Fin.fromℕ<` and `FinP.toℕ-fromℕ<`; fixed-width CNF `CNFVariableRenamingExact.placedTruthTableCNFSound/Complete`; the original `CNFPlacedConstraintConjunctionExact.PlacedPredicate` and `compilePlaced`. Existing owners, not an invented global CNF ontology.

**Commit `53e1aa92734709aea0c91c66634d93b8d60ca2ce`** extends the already existing `OpenAIMathSharedTseitinGateCNFExact.agda` with `newOutputBelow`, `wireNumberBelow`, `wireFin` and `gateWindowRename` (actual three local slots to finite global indices), `gateOutputIndexExact` (matches original Tseitin creation-time output number `inputs+gates`), `placedGate`, `placedGateCNF`, and `placedGateSound/Complete` inherited directly from CNF renaming owner. These are SOURCE-WRITTEN proof declarations; no Agda kernel receipt. Every original constant, NOT, AND and OR gate is covered; input or earlier gate references share the original variable indices, and constant/NOT dummy inputs may alias output harmlessly because the local predicate ignores them.

**Concrete distinction:** `placedGateCNF` has finite global variable width `inputs+suc gates` but every local template still depends on only THREE bits and has at most eight (actually four for these gate kinds) 3-literal forbidding clauses. This step is **not** the global program assembly: previously placed clauses must be embedded consistently as the program grows, the final output literal must be added, and the accepted-input vs CNF model-count bijection must be proved. The earlier numeric `finiteSupportedTseitinCountExact` can then transfer via the source model, but cannot substitute for this missing CNF semantics/bit-encoding/complexity proof.

**Exact max-cut distinction maintained:** OpenAI 102 needs unrestricted simple unweighted graph `Graph.maxCut` and scaled polynomial graph-printer gap; a group orbit-restricted optimum can be strictly smaller. `FiniteWeightedThresholdGraph` is proximal but not same-object. Nothing in one gate's placement proves UGC hardness or transfer to TSP.

**Pareto next:** assemble full concrete DAG with the original `CNFPlacedConstraintConjunctionExact` and original compiler index numbering; prove fixed finite `inputs+gates` count and ≤8g+O(1) clauses and source count bijection; compare to upstream `Encoding.formulaBitLength` on canonical `SAT.CNF (Fin n)`, then machine time/space. Keep historical Cook/Tseitin, original Agda #1040/CNF proof owners, later #1212 adapter, external OpenAI/Guo, and Ibrahim 3B custody separately attributed. All new Agda declarations kernel-pending; no CI or ESD modifications.


## 2026-10-30 fifth continuation — placed global variable indices and four-clause theorem

Confirmed original in-repo source owners and actual theorem signatures before writing: `PNotEqualsNPConcreteCircuitSharedCompilerExact.gateVariableIndex`, `PNotEqualsNPConcreteCircuitSharedSemanticsExact.gateVariableIndexBelowNext`, `PNotEqualsNPCookIndexedFormulaBridgeExact` canonical `Fin.fromℕ<` and `FinP.toℕ-fromℕ<` precedent, `CNFVariableRenamingExact.placedTruthTableCNFSound/Complete`, `CNFPlacedConstraintConjunctionExact.PlacedPredicate`, and original `CookLevinGridReplicationExact.listLength`. Checked actual latest #1414 parity source with `positiveField`/`negativeField` and live #1212/#1407/Lean #78 owner status; these are not duplicate SAT carriers.

- [x] `OpenAIMathSharedTseitinGateCNFExact`: source-write a literal 3-slot `gateWindowRename` into `Fin (inputs+suc gates)` for each ORIGINAL concrete circuit gate using the inherited gate numbering and proved bounds, and `gateOutputIndexExact` for the actual Tseitin creation-time number. `placedGate`/`placedGateCNF` call the original placed CNF compiler and `placedGateSound/Complete` use the original renaming lemmas. Commit `53e1aa92734709aea0c91c66634d93b8d60ca2ce`.
- [x] Exact **4 CNF clauses** per constant, NOT, AND, OR gate, not merely the generic ≤8 rejected rows: `localGateCNFClauseCountFour`, `renameCNFClauseCountExact`, `placedGateCNFClauseCountFour`. The general count transport under `renameCNF` is proved by literal structural recursion, rather than the invalid assumption that `listLength (renameCNF f xs)` is definitionally the same as `listLength xs` for unknown `xs`. Source commit `fa96e6791fe2d6214b49dea6d072a1e3f5791436`, correction `9d8fc791a747aebef1efcd46102f19aa6372afea`; AGDA KERNEL PENDING.
- [x] Extended the existing `scripts/check_openai_shared_tseitin_parsimonious.py` rather than duplicate a test harness: local 5-gate-kind × 8 triples, and placed Fin slot mapping, including repeated wires and source gate numbering; made sure the placed test **evaluates compiled forbidding clauses** instead of merely comparing an expression to itself (commit `832b87843744f3bd38460567eef9442cfb2488e5`). Independently EXECUTED local equivalents: **40** local 3CNF cases, **2,164** global placed gate/assignment cases, and the earlier **59,293** full finite DAG model-count cases. GitHub exact-head script execution and Agda kernel still absent.

**Unpaid high-impact next gate:** assemble the literal `GateProgram` recursively, embedding older clauses without altering their variable identities; add the output-wire unit constraint; prove exact global CNF satisfiability AND numerical parsimony by reusing `finiteSupportedTseitinCountExact` and `CNFPlacedConstraintConjunctionExact`; derive the total clause count (4g+1), variable count (n+g), and actual `Encoding.formulaBitLength` (the OpenAI encoding may inflate bits), before a machine-step/space transfer. A single placed gate is not an NP-hardness reduction or an ETH machine theorem; no direct connection to graph Max-Cut 102 or conditional Guo TSP is presumed. Maintain Agda golden / Lean secondary, historical Cook--Levin/Tseitin credit, #1040 and earlier CNF source authoring, #1212 new specialization, and Ibrahim/Monster original ownership.


## 2026-10-30 sixth continuation — complete *syntactic* original DAG to 3-CNF, 4g+1 clause budget

**Existing owners checked in source this tranche:** `DASHI/Unified/BalabanIbrahimParetoSnowballTOEExact` and `TOE369MaxCutKernelBidiTernaryExact` (actual protected theorem aliases and original Ibrahim/Monster provenance/firewalls), `PNotEqualsNPConcreteBooleanCircuitDAGExact` original `GateProgram`/reverse gate refs, `PNotEqualsNPConcreteCircuitSharedCompilerExact` creation-time variable numbers, `PNotEqualsNPCookIndexedFormulaBridgeExact` `Fin.fromℕ<`, `CNFVariableRenamingExact`, `CNFPlacedConstraintConjunctionExact.Placed.append`, and `CookLevinGridReplicationExact.listLength`. Read Agda PRs #1212/#1414/#1407 and Lean #78/#80 *live heads and underlying code*. The OpenAI exact graph `Graph.cutSize` and #378 machine proof were checked, not conflated with max-cut governance or the 27-orbit representation.

**Commit `b6cf62fd668650133a35c7515dddcd7b69be2761`**, corrected at `67db57f7e07ad5907cb85684c6961786c24c1951`, extends the same existing `OpenAIMathSharedTseitinGateCNFExact.agda` source:
- `extendEarlierFin` embeds every original variable into the one-gate-larger finite universe with certified numeric identity; `programPlacedCNF` recursively reuses `Rename.renameCNF` on the older clauses and `Placed.append` for the next four-clause placed gate.
- `fourPerGate` and `programPlacedCNFClauseCount` source-write the literal four-per-gate clause recurrence.
- `wireNumberBelowAtCircuitEnd`, `outputWireFin`, `outputUnitCNF` use original `Circuit.outputWire` rather than introduce a new acceptance variable.
- `circuitPlacedCNF`, `outputUnitCNFClauseCount`, `circuitPlacedCNFClauseCount` source-write the global complete *syntactic* CNF and exact (4g+1) clause budget in the finite `inputs+gates` variable carrier. **Important correctness repair:** `Placed.append` and `Grid.append` are separate definitions and NOT definitionally equal on neutral lists. The actual `placedAppendLength` theorem proves the length of the *used* append recursively. A premature direct invocation of `Grid.lengthAppend` was replaced, not left as an unjustified proof.

**Finite executable independent verification:** a new locally executed Python implementation enumerated **59,293** complete original DAGs/outputs with zero through three gates, one/two inputs, repeated source wires, all finite global assignments, and exact true-circuit count vs exact **full assembled CNF model count**, checking `4g+1` clauses and the source's newest-first gate variable indexing. **PASS**. Extended the previously existing `scripts/check_openai_shared_tseitin_parsimonious.py` in-place (commit `6f2337defbe9ea4c3644212f0a9d76ddae6fe0d4`) to check source accepting-input count = unique-gate extension count = full placed-CNF model count in its original 59,293-case loop, with explicit creation-order ↔ newest-first conversion. This exact committed script has not been re-executed from a GitHub checkout. Other independent local executable checks: 40 local width-three gate evaluations, 2,164 placed gate/CNF cases, one-way-gate failure control. Executed checks are NOT Agda kernel acceptance.

**NEW IMPORTANT STATUS DISTINCTION:** Global *syntax* and **literal clause count** are now source-written; **GLOBAL SOUNDNESS/COMPLETENESS and NUMERICAL PARSIMONY for that actual CNF are NOT source-proven yet**. The previous numeric `finiteSupportedTseitinCountExact` proves the source finite-model count, not that `circuitPlacedCNF` is equivalent to it. The missing same-object theorem must relate `CNF.evaluateCNF(circuitPlacedCNF c) bits` to the original `Shared.sharedAcceptanceFormula c` and finite gate input/auxiliary semantics via the existing CNF placement, original compiler numbering and original `FiniteSupportedModel`. Then explicitly compile `CNF.Bits` / list clauses to OpenAI canonical `SAT.CNF (Fin n)` (finite set semantics remove duplicates; check multiplicity effects), verify `Encoding.formulaBitLength` and actual bit-time/space. Four clauses per gate does NOT imply fixed encoded-bit overhead per gate when variable names grow.

**Highest-alpha / Pareto wall:** Focus on above missing global semantic transport, fixed-width output encoding and source machine bounds, before any alleged algorithmic speedup. The Oct-29 Guo sparse TSP theorem remains conditional on manuscript D.1, not a consequence of formalized 378; family 102 polynomial-scale unrestricted approximation-hardness remains separate; the current 27/11/7 C3 symmetry only offers finite special cases absent a uniform graph/objective-preserving reduction. Agda golden kernel status for all new declarations is **PENDING**; never promote to verified. Retain Cook/Levin/Tseitin history, original DASHI #1040, prior CNF owners, new #1212 adaptation, OpenAI/Guo original authors and Ibrahim Monster 3B custody independently. No ESD files or CI changes.


### 30 October final arithmetic closure on placed CNF
Commit `18a7c173f3f8b385d3423aeffd2d428063c4cefe` extends the same source module with `fourPerGateMultiply` (reuse `Data.Nat.Properties.+-comm`) and `circuitPlacedCNFClosedClauseCount`, making the total actual Nat formula `gateCount * 4 + 1` rather than leaving it only as a recursively described count. This is SOURCE-WRITTEN/KERNEL-PENDING and is semantically about the *existing original DAG compiler's* clause list. No new CNF representation, speed claim, full semantic equivalence, or Monster identification was added.

# Schlögl–Fey Source-Maximal Circuit Formalisation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalise as much of Schlögl–Fey’s binary-coded ternary signed-digit FPGA adder as the available source actually exposes, and prove circuit-depth/resource claims only when the construction supports them.

**Architecture:** Separate source extraction from theorem construction. First build a provenance owner recording exact equations/truth tables/stage topology from the paper; only if that owner contains a complete local cell/network specification may the formal circuit lane proceed. Otherwise strengthen the empirical receipt and stop at an explicit source boundary.

**Tech Stack:** Agda, existing `TernarySignedDigitAdderSemanticsExact`, `TernarySignedDigitBinaryCodeBridgeExact`, `SchloeglFeyFPGASourceBoundaryExact`, source citations/documentation.

**Spec:** `docs/superpowers/specs/2026-10-03-tekum-paper-max-cut-design.md`

## Global Constraints
- Do not infer a gate equation, LUT truth table, carry-chain topology, or stage count absent from the source.
- Report measured FPGA timing/resource results as attributed empirical receipts unless independently derived from a formal network.
- The existing ternary code mapping `-1→00`, `0→01`, `+1→10`, `11` reserved remains authoritative.
- TDD applies once a source-complete network interface exists; source extraction itself is provenance work, not production theorem code.

## Review Focus
1. Device-family-specific primitives versus abstract Boolean gates.
2. Reported clock frequency versus combinational depth.
3. LUT count formulas versus individual benchmark table values.
4. Carry-chain implementation versus LUT-only implementation.
5. Any width-independent timing statement that is empirical rather than structurally proved.

---

### Task 1: Source extraction and provenance gate

**Files:**
- Create: `Docs/SchloeglFeyCircuitSourceExtraction.md`
- Create or modify: `DASHI/ComputerScience/SchloeglFeyCircuitSourceExact.agda`
- Modify: `DASHI/ComputerScience/SchloeglFeyFPGASourceBoundaryExact.agda`

**Interfaces:**
- Produces either a complete `SourceDigitCell` / `SourceNetworkShape` sufficient for formalisation, or a typed `CircuitConstructionUnavailable` boundary with page/table/equation provenance.

- [ ] Inspect the available paper/chapter for exact per-digit equations, truth tables, intermediate signals, stage count, neighbour dependence, carry-chain primitives, LUT assumptions, resource formulas, and timing argument.
- [ ] Record each recovered item with source location; record each missing item explicitly.
- [ ] Set a single typed gate `constructionSufficientForKernelCircuit : Bool` from those source facts, with no inference from benchmark outcomes.
- [ ] Commit `Schloegl-Fey: extract circuit construction provenance`.

### Task 2A: If source construction is sufficient — local digit cell

**Files:**
- Create: `DASHI/ComputerScience/SchloeglFeySignedDigitCellExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: source-extracted cell equations only.
- Produces: `digitCell`, `digitCellCorrect`, explicit local depth/resource constants.

- [ ] Add failing truth-table regression reproducing every source cell row.
- [ ] Verify RED.
- [ ] Implement the exact source cell equations.
- [ ] Prove local signed-digit semantic correctness.
- [ ] Verify GREEN + commit.

### Task 2B: If source construction is insufficient — strengthen receipt only

**Files:**
- Modify: `DASHI/ComputerScience/SchloeglFeyFPGASourceBoundaryExact.agda`
- Modify: `Docs/TekumBalancedTernaryFormalisation.md`

- [ ] Encode exact reported LUT/resource/timing observations with page/table provenance.
- [ ] Keep `gateNetworkReconstructed`, `constantDepthKernelTheorem`, and `resourceFormulaKernelTheorem` false.
- [ ] Commit `Schloegl-Fey: sharpen empirical FPGA source receipt`.

### Task 3: If Task 2A exists — n-digit network and word correctness

**Files:**
- Create: `DASHI/ComputerScience/SchloeglFeySignedDigitNetworkExact.agda`

**Interfaces:**
- Consumes: `digitCell`, local correctness.
- Produces: `adderNetwork n`, `adderNetworkCorrect`, source-exact boundary treatment.

- [ ] Add failing width-1/2/4 network regressions and general semantic theorem requirement.
- [ ] Verify RED.
- [ ] Build the source-defined neighbour/local network recursively.
- [ ] Prove word-level semantic addition correctness by composition of cell theorems.
- [ ] Verify GREEN + commit.

### Task 4: If source topology supports it — depth and resource theorem

**Files:**
- Create: `DASHI/ComputerScience/SchloeglFeyAdderDepthResourceExact.agda`

**Interfaces:**
- Consumes: formal network topology.
- Produces: exact `networkDepth`, `resourceCount`, source-model theorems.

- [ ] Add failing regression for source benchmark widths and the claimed general structural bound.
- [ ] Verify RED.
- [ ] Derive depth from the network graph/stages; prove `networkDepth n ≤ C` only if `C` follows from source topology independently of measured frequency.
- [ ] Derive resource count only to the granularity justified by the abstract primitive model.
- [ ] Compare theorem outputs with source benchmark receipts without treating agreement as proof.
- [ ] Verify GREEN + commit.

### Task 5: Capstone boundary update

**Files:**
- Modify: `DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda`
- Modify: `Docs/TekumBalancedTernaryFormalisation.md`

- [ ] Update the capstone to distinguish `sourceCircuitExtracted`, `digitCellCorrect`, `networkCorrect`, `constantDepthDerived`, and `empiricalTimingReceiptPresent`.
- [ ] Run all available static/focused/full checks.
- [ ] Commit `Schloegl-Fey: finalize source-maximal formalisation boundary`.

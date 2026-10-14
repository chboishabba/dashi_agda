# IIT Hyperfabric Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the finite IIT-4 + hyperfabric programme from system-phi calibration through full distinctions/relations/big-Phi and consumer-descent receipts.

**Architecture:** Keep the causal fabric `H`, local synthesis law `mu`, and current state `s` as independent coordinates. IIT partitions act on gluing/causal connections; gate laws remain local to `(A,B)->C` synthesis cells. Python performs exhaustive finite evaluation and emits receipts; Agda owns exact structural claims and promotion boundaries.

**Tech Stack:** Agda, Python 3 standard library/pandas for local analysis, existing DASHI theorem owners, GitHub PR #1148 branch.

**Spec:** `docs/superpowers/specs/2026-10-14-iit-hyperfabric-completion-design.md`

## Global Constraints

- Reuse existing repo owners before introducing new algebra/topology definitions.
- Do not identify IIT-3 historical counterexamples with IIT-4 `bigPhi`.
- Do not identify 1->3 topological pants with 2->1 causal synthesis without an explicit reversal witness.
- Do not treat C3^3 recentering as a canonical symmetry of the non-periodic ternary cube.
- Do not claim Agda-green without an actual Agda/CI receipt.
- Preserve attribution/source boundaries on all externally acquired facts.

## Review Focus

- Zero-probability repertoire inputs must fail/branch explicitly rather than silently divide by zero.
- Equal-cardinality algebras (Z9 vs F3^2) must remain distinguishable in types and receipts.
- Directional partitions must alter only selected causal connections, never mutate local gate definitions.
- Big-Phi output must not be populated from `phi_s` alone; distinctions and relations must be present.
- Python receipt schema and Agda receipt consumer names must stay synchronized.

---

### Task 1: Source-faithful finite IIT-4 system kernel

**Files:**
- Create: `DASHI/Biology/IIT4FiniteExecutableKernelExact.agda`
- Create: `scripts/iit4_finite_reference.py`
- Create: `scripts/check_iit4_finite_reference.py`
- Modify: `DASHI/Biology/IITPhiIntegrationEverything.agda`
- Modify: `DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda`
- Modify: `scripts/check_iit_phi_integration_maxcut.sh`

**Interfaces:**
- Consumes: `IIT4FiniteCausalStructureExact`, `IIT4FiniteProbabilityRepertoireExact`, `IIT4SystemPhiInputExact`.
- Produces: finite repertoire receipts, directional partition enumeration, MIP witness, exact/symbolic `phi_s` evaluation surface.

- [ ] Add validation imports/contract names first and confirm the owner is absent.
- [ ] Implement typed nonzero probability inputs and exact finite cause/effect repertoire constructors.
- [ ] Implement finite directional partition enumeration/admissibility interface and MIP witness surface.
- [ ] Implement Python reference functions `enumerate_partitions`, `partitioned_repertoire`, `system_phi` and JSON receipt emission.
- [ ] Add regression fixtures for the current two-bit XOR example and zero-probability cases.
- [ ] Run Python checker; record pass receipt; keep Agda kernel status separate.

### Task 2: XOR-grid calibration through fibre/gluing

**Files:**
- Create: `DASHI/Biology/IITXORGridFibreCalibrationExact.agda`
- Create: `scripts/iit_xor_grid_calibration.py`
- Create: `scripts/check_iit_xor_grid_calibration.py`

**Interfaces:**
- Consumes: `IITCausalPantsFibreGluingExact`, `IITXORGridFibreCircuitBridgeExact`, Task 1 evaluator.
- Produces: recurrent XOR-grid TPM/fabric receipts and calibration summary.

- [ ] Encode the existing XOR grid as local XOR cells plus explicit gluing edges.
- [ ] Add feed-forward control fabric with otherwise matched local gate law.
- [ ] Evaluate every finite state for candidate grids small enough for exhaustive enumeration.
- [ ] Record MIP/cut scaling and verify feed-forward controls yield `phi_s = 0`.
- [ ] Add firewall that calibration does not manufacture IIT-4 big-Phi.

### Task 3: Matched gate/fabric sweeps

**Files:**
- Create: `DASHI/Biology/IITMatchedFabricGateExperimentExact.agda`
- Create: `scripts/iit_matched_fabric_gate_sweep.py`
- Create: `scripts/check_iit_matched_fabric_gate_sweep.py`

**Interfaces:**
- Consumes: Task 1 evaluator, causal-pants fibre owner.
- Produces: same-fabric/different-gate and same-gate/different-fabric receipts.

- [ ] Fix canonical fabrics: open path, cycle, small grid, pants chain.
- [ ] Fix gate families: XOR, OR, AND, triXor.
- [ ] Exhaustively scan statewise `phi_s` and selected MIPs for tractable fixtures.
- [ ] Emit factorized summary keyed by `(fabric, gate, state)`.
- [ ] Prove in Agda that experiment axes are independently replaceable and neither axis alone definitionally determines `phi_s`.

### Task 4: 369 same-cardinality algebra controls

**Files:**
- Create: `DASHI/Biology/IIT369MatchedAlgebraControlExact.agda`
- Create: `scripts/iit_369_algebra_controls.py`

**Interfaces:**
- Consumes: Base369 finite ring laws, F3^2 phase-product bridge, Task 3 sweep interface.
- Produces: matched F3, Z9, F3^2 finite transition systems on controlled fabrics.

- [ ] Reuse repo-native F3/triXor, Z9/nonary addition, and F3^2 componentwise law.
- [ ] Add exact same-cardinality Z9-vs-F3^2 control fixture.
- [ ] Enumerate transition graph invariants and IIT system-phi receipts under matched topology.
- [ ] Record explicit theorem that carrier cardinality observation cannot recover the algebra law.

### Task 5: Pants/hyperfabric indexed fixtures

**Files:**
- Create: `DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda`
- Create: `scripts/iit_hyperfabric_fixture_scan.py`

**Interfaces:**
- Consumes: causal-pants fibre owner, ternary pants frontier, typed hyperfabric core.
- Produces: indexed `(A,B)->C` cell families and gluing-path experiment fixtures.

- [ ] Define path-indexed causal cells with named A/B input sockets and C output.
- [ ] Define open, closed, branching, and higher-order-compatible gluing fixtures.
- [ ] Preserve graph/stalk/global-section partition semantics as separate experiment labels.
- [ ] Scan tractable fixtures and emit recurrence, MIP, and `phi_s` summaries.

### Task 6: Pointed ternary-27 / face-gluing experiment

**Files:**
- Create: `DASHI/Biology/IITPointed27HyperformExperimentExact.agda`
- Create: `scripts/iit_pointed27_gluing_scan.py`

**Interfaces:**
- Consumes: pointed-27, origin+26, cyclotomic cell chart, face Cech/cocycle owners.
- Produces: selected-cubie + admissible-face-gluing experiment states.

- [ ] Reuse exact 27=1+26 and 9=1+8 owners.
- [ ] Encode selected cubie, active face witness, pairwise edge transport and corner cocycle as separate fields.
- [ ] Compare same selected cubies with distinct admissible gluing classes where available.
- [ ] Keep C3^3 recentering labelled as a chosen algebraic chart, not geometric canonicalization.

### Task 7: Distinctions, relations, and full IIT-4 structure

**Files:**
- Create: `DASHI/Biology/IIT4FiniteDistinctionExact.agda`
- Create: `DASHI/Biology/IIT4FiniteRelationExact.agda`
- Create: `DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda`
- Extend: `scripts/iit4_finite_reference.py`

**Interfaces:**
- Consumes: Task 1 system evaluator.
- Produces: mechanism/purview enumeration, `phi_d`, relation enumeration, `phi_r`, finite cause-effect structure and `bigPhi` input package.

- [ ] Enumerate nonempty mechanisms and purviews on finite carriers.
- [ ] Compute maximally irreducible cause/effect purviews and `phi_d` receipts.
- [ ] Build finite relation candidates and `phi_r` receipts without collapsing them into distinction scores.
- [ ] Construct cause-effect structure package only after distinction/relation receipts exist.
- [ ] Add regression that `phi_s` alone cannot inhabit a complete structure package.

### Task 8: Aaronson-style IIT stress family

**Files:**
- Create: `DASHI/Biology/IITXOR369StressFamilyExact.agda`
- Create: `scripts/iit_xor_369_stress_scan.py`

**Interfaces:**
- Consumes: Tasks 2-7.
- Produces: calibrated XOR/369 finite stress cases using IIT-4 quantities, with historical-version firewall.

- [ ] Scale tractable recurrent XOR fabrics and record `phi_s`/distinction/relation summaries.
- [ ] Run matched 369 fabrics at comparable finite sizes.
- [ ] Separate historical IIT critique claims from newly computed IIT-4 quantities in all output metadata.
- [ ] Do not infer consciousness from rank/order results.

### Task 9: Consumer-descent tests

**Files:**
- Create: `DASHI/Biology/IITIIT4ConsumerDescentExact.agda`
- Create: `scripts/iit_consumer_descent_receipt.py`

**Interfaces:**
- Consumes: finite IIT observable packages, `ConsumerDescentMinimalObserverExact`, brain/MaleCNS consumer owners.
- Produces: factorization proofs or explicit non-descent witnesses for declared consumers.

- [ ] Define IIT observation surfaces (`phi_s`, distinctions-only, full structure) as observers.
- [ ] Reuse consumer sufficiency/fibre-constancy equivalences.
- [ ] Produce concrete collision witnesses where two source states share an IIT observation but differ for a declared consumer.
- [ ] Keep biological/phenomenal identity as an unpromoted interpretation unless a consumer factorization is actually paid.

### Task 10: Receipt loop, aggregate, and completion audit

**Files:**
- Create: `DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda`
- Create: `scripts/check_iit_hyperfabric_completion.py`
- Modify: `DASHI/Biology/IITPhiIntegrationEverything.agda`
- Modify: `DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda`
- Modify: `scripts/check_iit_phi_integration_maxcut.sh`
- Modify: PR #1148 body/status text.

**Interfaces:**
- Consumes: Tasks 1-9.
- Produces: one completion ledger distinguishing source-written, Python-verified, and kernel-verified claims.

- [ ] Define a stable JSON/CSV receipt schema and verify every scanner emits it.
- [ ] Add aggregate imports and static contract requirements for every new owner.
- [ ] Add completion ledger booleans/typed statuses for `phi_s`, `phi_d`, `phi_r`, `bigPhi`, XOR calibration, 369 controls, hyperfabric fixtures and consumer descent.
- [ ] Run all Python checkers available in the environment and save outputs.
- [ ] Query GitHub workflow/commit status; claim Agda-green only if actual evidence exists.
- [ ] Refresh PR description with exact current diff and remaining blockers only.

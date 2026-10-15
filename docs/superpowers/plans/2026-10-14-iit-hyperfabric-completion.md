# IIT Hyperfabric Completion Implementation Plan

> **For agentic workers:** use the repo's formal-development workflow. Formal completeness is established by the Agda aggregate and Agda kernel checking; Python is reserved for numerical / finite-combinatorial verification.

**Goal:** Complete the finite IIT-4 + hyperfabric programme from system-phi calibration through distinctions/relations/Phi and consumer-descent boundaries.

**Architecture:** Keep causal fabric `H`, local synthesis law `mu`, and state `s` independent. IIT partitions act on causal connections. Gate laws remain local to `(A,B)->C` cells. Graph, stalk-restriction, and global-section partition semantics remain distinct.

**Verification authorities:**

1. **Agda:** `agda DASHI/EverythingIITPhiIntegrationMaxCut.agda` is the authority for formal imports, theorem surfaces, type separation, and promotion firewalls.
2. **Python finite numerics:** `python scripts/iit_numeric_verification.py` is the authority only for executable finite IIT values and finite combinatorial counts.
3. **PyPhi:** `scripts/iit4_pyphi_oracle.py` is the external full-CES numerical oracle when a compatible PyPhi runtime is installed.

There are deliberately no Python source-presence checkers and no grep-based shell pseudo-proofs.

## Global constraints

- Reuse existing repo owners before introducing new algebra/topology definitions.
- Keep IIT 4.0 (2023) and the 2026 intrinsic-information requirement explicitly versioned.
- Do not identify historical IIT/XOR values with IIT-4 structure `Phi`.
- Do not identify 1->3 topological pants with 2->1 causal synthesis without an explicit reversal witness.
- Do not treat `C3^3` recentering as a canonical symmetry of the non-periodic ternary cube.
- Treat “369” as the repo's **3/6/9 algebra family plus ternary 27/composition geometry**, not merely the cardinality sequence `3^n`.
- Equal cardinality never licenses algebra identification (`Z6` versus `S3`, or `C9` versus `C3 x C3`).
- Never promote a Python numerical receipt to an Agda proof.
- Never claim Agda-green without an actual Agda/CI receipt.

---

## Task 1 — Versioned finite IIT-4 system kernel

**Owners:**
- `DASHI/Biology/IIT4FiniteExecutableKernelExact.agda`
- `scripts/iit4_finite_reference.py`

**Implemented surface:** finite factored TPMs, cause/effect specification, directional partitions, independent causal marginalisation of cut inputs per target factor, normalized MIP selection, unnormalized system `phi_s`, and separate 2023/2026 semantics.

**Numerical regression:** unified verifier checks 54 three-unit directional partitions, recurrent XOR/OR/AND/triXor, feed-forward controls, and the 2026 deterministic cap.

## Task 2 — XOR-grid calibration

**Owners:**
- `DASHI/Biology/IITXORGridFibreCalibrationExact.agda`
- `DASHI/Biology/IITXORGridFibreCircuitBridgeExact.agda`
- `scripts/iit_xor_grid_calibration.py`

The actual 2x2 repo fixture is represented as local XOR synthesis plus a separate recurrent gluing graph. Under the shared factored finite evaluator the 2023 statewise profile is `{0, 0.5}` with 12/16 zero states; deterministic 2026 `phi_s` is zero throughout.

## Task 3 — Matched fabric/gate sweeps

**Owners:**
- `DASHI/Biology/IITMatchedFabricGateExperimentExact.agda`
- `scripts/iit_matched_fabric_gate_sweep.py`

One shared numerical kernel evaluates both controlled axes:
- hold fabric fixed, vary XOR/OR/AND/triXor;
- hold XOR fixed, vary feed-forward/recurrent/grid fabric.

No second bespoke IIT evaluator is retained.

## Task 4 — 369 matched-algebra controls

**Owners:**
- `DASHI/Biology/IIT369MatchedAlgebraControlExact.agda`
- `DASHI/Biology/IIT369PantsGluingBridgeExact.agda`
- `DASHI/Foundations/HexTruthS3CarrierBridgeExact.agda`
- `DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact.agda`
- `scripts/iit_369_algebra_scan.py`

This is deliberately not just a `3^n` test. Two same-cardinality controls are first-class:

- **Six states:** `HexTruth`/cyclic `Z6`-like addition versus the noncommutative `S3` permutation product. The repo owns an exact six-state carrier chart and proves that it cannot preserve both products. The matched recurrent numerical fixture observes the same IIT-4 (2023) system-phi profile `log2(36)` for both.
- **Nine states:** cyclic `C9`/NonaryTruth addition versus `C3 x C3` / `F3^2` componentwise addition. The repo proves the group laws are not isomorphic; the matched recurrent numerical fixture observes the same 2023 system-phi profile `log2(81)` for both.

These are consumer/non-identifiability results for the tested IIT observation. The numerical collisions are not the algebraic separation proofs.

## Task 5 — Path-indexed pants / hyperfabric fixtures

**Owners:**
- `DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda`
- `DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda`
- `scripts/iit_hyperfabric_fixture_scan.py`

Local synthesis, gluing path, typed seam compatibility, and partition semantics remain separate coordinates. Numerical scanning currently evaluates graph-level causal partitions only; stalk/global-section obligations remain formal typed surfaces.

## Task 6 — Pointed ternary-27 gluing envelope

**Owners:**
- `DASHI/Biology/IITPointed27HyperformExperimentExact.agda`
- pointed-27 / origin+26 / recentered-26 / cyclotomic / triadic non-descent owners
- `scripts/iit_pointed27_gluing_scan.py`

The numerical/combinatorial layer checks the exact finite incidence envelope: 27 points, strata `1+6+12+8`, 54 point-face incidences, six 9-point faces, twelve 3-point face-pair overlaps, eight one-point corner triples, and `27^3` three-selected-cubie choices. Geometry alone does not manufacture a TPM.

## Task 7 — Distinctions, relations, and structure Phi

**Owners:**
- `DASHI/Biology/IIT4FiniteDistinctionExact.agda`
- `DASHI/Biology/IIT4FiniteRelationExact.agda`
- `DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda`
- `scripts/iit4_structure_reference.py`
- `scripts/iit4_pyphi_oracle.py`

`phi_s`, `phi_d`, `phi_r`, and structure `Phi` remain separate typed quantities. The lightweight Python structure reference verifies arithmetic/combinatorics only; the PyPhi adapter is the external source-faithful full-CES numerical route and records runtime package provenance separately from the calibration source revision.

## Task 8 — XOR / 369 stress family

**Owners:**
- `DASHI/Biology/IITXOR369StressFamilyExact.agda`
- `scripts/iit_xor_369_stress_scan.py`

Stress comparisons are versioned and alphabet-aware and include binary XOR, ternary triXor, six-state `Z6/S3`, and nine-state `C9/F3^2` controls. System-phi ordering is never promoted to a consciousness ordering or silently identified with big-Phi.

## Task 9 — Consumer descent

**Owner:** `DASHI/Biology/IITIIT4ConsumerDescentExact.agda` plus existing consumer-descent / brain / MaleCNS owners.

This task is formal, not a Python truth table. Exact non-descent witnesses include same-cardinality observations losing algebra identity and selected ternary-27 cubies losing the irreducible triadic face. The numerical verifier may report observed IIT collisions, but consumer factorisation claims are owned by Agda.

## Task 10 — Aggregate and verification loop

**Owners:**
- `DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda`
- `DASHI/Biology/IITPhiIntegrationEverything.agda`
- `DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda`
- `DASHI/EverythingIITPhiIntegrationMaxCut.agda`
- `scripts/iit_numeric_verification.py`
- `.github/workflows/iit-phi-integration-maxcut.yml`

The completion ledger separates source presence, numerical-program presence/execution, PyPhi-oracle execution, and Agda-kernel execution. It does not let one authority substitute for another. The workflow has separate numeric and Agda jobs and contains no source-grep pseudo-proof.

## Acceptance sequence

Run in a suitable checkout:

```bash
python scripts/iit_numeric_verification.py
python scripts/iit4_pyphi_oracle.py --help   # then run selected full-CES fixtures with installed PyPhi
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
```

The first command establishes finite numerical/combinatorial regression targets only. A fresh PyPhi oracle run establishes full-CES numerical values for selected fixtures. The final command (or equivalent CI kernel evidence) establishes formal Agda validity.

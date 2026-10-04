# Tekum P-adic Dual-Chart Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the finite reversal-conjugated Tekum precision projection agrees with the executable triadic `CylinderSystem` refinement, without identifying Tekum real semantics with p-adic semantics.

**Architecture:** Stay entirely on finite trit carriers. Reuse the already-proved `Vec Trit n ≃ Kernel n`, `reverse` involution, and executable `refineKernel`; the final theorem is a representation-natural transformation only.

**Tech Stack:** Agda stdlib `Data.Vec`, `TriadicPAdicCodec`, `TriadicPAdicCylinderExact`, existing Tekum dual-chart owners.

**Spec:** `docs/superpowers/specs/2026-10-03-tekum-paper-max-cut-design.md`

## Global Constraints
- No claim that Tekum numeric values are p-adic values.
- No metric/order identification.
- Preserve low-order-prefix vs LST-first orientation explicitly.
- TDD: regression theorem surface first, then implementation.

## Review Focus
1. Dimension indices after one vs two refinements.
2. Reverse orientation at width 0/1/2 boundaries.
3. Distinguish kernel-constructor equality from `Data.Vec` equality.
4. Avoid silently changing the canonical p-adic cylinder orientation.
5. Keep numerical semantics out of this owner.

---

### Task 1: One-step dual projection / cylinder correspondence

**Files:**
- Create: `DASHI/ComputerScience/TekumPadicDualCylinderWeldExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: `TekumPadicDualChartExact.dualChart`, `TekumTriadicPAdicKernelBridgeExact.toKernel/fromKernel`, `TriadicPAdicCylinderExact.refineKernel`.
- Produces: `dualDropOne`, `dualDropOneToKernelRefine`, `kernelRefineFromDualDropOne`.

- [ ] Write failing static + small concrete width regression.
- [ ] Verify RED.
- [ ] Define the one-trit tail-drop conjugate and prove it maps through `toKernel` to `refineKernel`.
- [ ] Verify focused Agda + available full checks.
- [ ] Commit `Tekum: weld reversal dual chart to p-adic refinement`.

### Task 2: Two-trit Tekum precision correspondence

**Files:**
- Modify: `DASHI/ComputerScience/TekumPadicDualCylinderWeldExact.agda`
- Modify: `DASHI/ComputerScience/TekumPadicDualChartExact.agda`

**Interfaces:**
- Consumes: Task 1 one-step theorem + existing `dualPrecisionTwo`.
- Produces: `dualPrecisionTwoEqualsTwoCylinderRefinements`.

- [ ] Add failing regression for widths 2–5 and general theorem name.
- [ ] Verify RED.
- [ ] Compose the one-step theorem twice and rewrite with the existing dual two-trit projection.
- [ ] Verify GREEN + commit.

### Task 3: Capstone boundary update

**Files:**
- Modify: `DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda`
- Modify: `Docs/TekumBalancedTernaryFormalisation.md`

- [ ] Require the new finite naturality theorem in the static capstone regression.
- [ ] Mark only the finite orientation/naturality field as paid; retain literal p-adic numeric identity as `false`.
- [ ] Run focused + full available checks and commit `Tekum: close finite p-adic dual projection weld`.

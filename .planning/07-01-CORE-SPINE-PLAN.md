---
phase: 07-core-spine
type: execute
---

<objective>
Stabilize the core physics spine around `ClosureAxioms` and the signature forcing seam.

Purpose: Make the repository’s “physics-critical” dependency chain explicit and frozen so the real-operator work and GR/QFT bridge work attach to a stable interface.
Output: A concrete inventory of the core spine modules + a canonical dependency diagram + a short “frozen interface” checklist.
</objective>

<execution_context>
~/.claude/get-shit-done/workflows/execute-phase.md
./summary.md
</execution_context>

<context>
@.planning/PROJECT.md
@.planning/ROADMAP.md
@.planning/STATE.md

# Core interface seam (confirmed present):
@DASHI/Physics/ClosureGlue.agda

# Real-operator placeholder surface (currently identity-ish operators with nonexpansive proofs):
@DASHI/Physics/RealOperators.agda
@DASHI/Physics/RealOperatorStack.agda

# Signature seam / forcing surface (note: current `Signature31` file is a trivial witness):
@DASHI/Physics/Signature31.agda

# Canonical closure entrypoint and repo-facing index of Stage C ladder:
@DASHI/Physics/Closure/PhysicsClosureSummary.agda

# Optional: compile entrypoint
@DASHI/Everything.agda
</context>

<tasks>

<task type="auto">
  <name>Task 1: Inventory and classify the core spine modules</name>
  <files>.planning/07-01-CORE-SPINE-INVENTORY.md</files>
  <action>
Create `.planning/07-01-CORE-SPINE-INVENTORY.md` containing:
1) A module list for the physics-critical chain centered on `DASHI.Physics.ClosureGlue.ClosureAxioms` and the signature seam.
2) A classification tag per module: `core`, `plumbing`, or `experiment`.

Classification rules (keep them simple and enforceable):
- `core`: defines a primary record/interface or theorem that downstream proofs consume (e.g. ClosureAxioms, canonical closure entrypoints).
- `plumbing`: re-export/wrapper modules or instance wiring whose purpose is threading structure.
- `experiment`: validation harness, cost profiling, ZK/LMFDB/prototype-only tracks.

What to avoid and why:
- Do NOT move/rename any files yet; this is an audit phase and moving modules will create noisy diffs and break imports.
- Do NOT try to “fix” stubs here; just surface them (the plan for real operator substance comes next).
  </action>
  <verify>
A) `rg "module DASHI\\.Physics\\.ClosureGlue" -n` finds the core seam.
B) Inventory file exists and includes at least: `DASHI/Physics/ClosureGlue.agda`, `DASHI/Physics/Signature31.agda`, and `DASHI/Physics/Closure/PhysicsClosureSummary.agda`.
  </verify>
  <done>
Inventory document exists with: module list + classification + a short note on known stubs (e.g. trivial signature witness).
  </done>
</task>

<task type="auto">
  <name>Task 2: Produce the canonical dependency diagram for the closure→signature spine</name>
  <files>.planning/07-01-CORE-SPINE-DIAGRAM.md</files>
  <action>
Create `.planning/07-01-CORE-SPINE-DIAGRAM.md` containing ONE canonical diagram (ASCII is fine) for:

`Ultrametric` / `StrictContraction` / fixed point machinery
→ closure interface (`ClosureAxioms`)
→ (quadratic / signature forcing seam)
→ `sig31` surface (or what currently stands in for it)
→ Stage C canonical closure entrypoints.

Include a short “frozen interface” checklist:
- Which record(s) are the stable API surface (start with `ClosureAxioms`).
- Which modules should NOT be edited by bridge work (only used via adapters).

What to avoid and why:
- Do NOT invent new theorems here; only connect what is already present.
- Do NOT expand the diagram to include experiments; keep it to the physics-critical chain.
  </action>
  <verify>
Diagram file contains the literal identifier `ClosureAxioms` and references the actual file paths used in this repo.
  </verify>
  <done>
A single diagram exists that a new reader can use to locate the physics seam and understand where bridge modules should attach.
  </done>
</task>

<task type="auto">
  <name>Task 3: Compile check on the spine entrypoint</name>
  <files>(no files; command-only verification)</files>
  <action>
Run the Agda typecheck for the repo entrypoint (or, if too slow, at least the core seam files):
- Prefer: `agda -i . -i /usr/share/agda/lib/stdlib DASHI/Everything.agda`
- Fallback: `agda -i . -i /usr/share/agda/lib/stdlib DASHI/Physics/ClosureGlue.agda`

What to avoid and why:
- Do NOT attempt to fix failures in this plan unless the failure is a trivial import/path issue in a file we just created.
- If typecheck fails, capture the first error and stop; the next plan will decide whether this is a bridge blocker or an experimental-track break.
  </action>
  <verify>
The command exits successfully, or we capture the first failing module + error text in the plan summary.
  </verify>
  <done>
We have an explicit, current compilation status for the spine seam.
  </done>
</task>

</tasks>

<verification>
Before declaring this plan complete:
- [ ] `.planning/07-01-CORE-SPINE-INVENTORY.md` exists and is readable
- [ ] `.planning/07-01-CORE-SPINE-DIAGRAM.md` exists and references real module paths
- [ ] `agda -i . -i /usr/share/agda/lib/stdlib DASHI/Everything.agda` either succeeds or the first failure is recorded
</verification>

<success_criteria>

- Core seam is explicitly identified: `DASHI/Physics/ClosureGlue.agda` + `ClosureAxioms`
- Signature seam status is explicitly documented (including whether it is currently trivial/stubbed)
- A canonical dependency diagram exists and is small enough to be a stable “map”
- No code moved/renamed; this is audit + stabilization only
</success_criteria>

<output>
After completion, create `.planning/07-01-CORE-SPINE-SUMMARY.md` with:
- Accomplishments
- Files created
- Decisions made (especially what is considered “frozen interface”)
- Issues encountered (compile status)
- Next step: “Ready for 07-02 (Physics Bridge) and 07-03 (Real Operators)”
</output>

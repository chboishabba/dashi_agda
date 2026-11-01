---
phase: 07-repo-audit
type: execute
---

<objective>
Classify repository modules into: core, plumbing, experiments/tooling, and presentational indexes — without moving files yet.

Purpose: Reduce the “600-file labyrinth” feel by producing an explicit map of what matters for the physics proof spine vs what is infrastructure.
Output: A table-driven audit artifact that can later justify safe refactors (separate repo / subtree moves) without breaking compilation today.
</objective>

<execution_context>
~/.claude/get-shit-done/workflows/execute-phase.md
./summary.md
</execution_context>

<context>
@.planning/PROJECT.md
@.planning/ROADMAP.md
@.planning/STATE.md

# Experimental infrastructure surfaced by grep:
@Verification/Pipeline.agda
@Verification/CostProfile.agda
@Verification/LMFDB.agda
@Verification/ZK.agda

# Canonical closure summary entrypoint:
@DASHI/Physics/Closure/PhysicsClosureSummary.agda
</context>

<tasks>

<task type="auto">
  <name>Task 1: Create module classification table (no moves)</name>
  <files>.planning/07-04-REPO-CLASSIFICATION.md</files>
  <action>
Create `.planning/07-04-REPO-CLASSIFICATION.md` with a table:

| module path | category | why it exists | depends-on (optional) |

Categories:
- `core`
- `plumbing`
- `experiment`
- `tooling`
- `presentational`

Minimum coverage:
- Include the `Verification/*` modules explicitly as non-core.
- Include the closure seam modules (`DASHI/Physics/ClosureGlue.agda`, `DASHI/Physics/Signature31.agda`) explicitly as core/seam.

What to avoid and why:
- Do NOT attempt to fix architecture by moving code; this is only classification.
  </action>
  <verify>
Table file exists and includes at least 15 entries covering both core and experiments.
  </verify>
  <done>
Classification artifact exists and can serve as the basis for later safe refactor/moves.
  </done>
</task>

</tasks>

<verification>
Before declaring this plan complete:
- [ ] `.planning/07-04-REPO-CLASSIFICATION.md` exists
- [ ] Verification modules are categorized as non-core
</verification>

<success_criteria>

- Repo structure is documented in a way that makes the physics-critical path obvious
- No file moves performed
</success_criteria>

<output>
After completion, create `.planning/07-04-REPO-AUDIT-SUMMARY.md` with:
- Accomplishments
- Notable boundary decisions (what counts as “core”)
- Suggested safe refactor candidates (deferred; no actions taken)
</output>

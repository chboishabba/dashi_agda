---
phase: 08-signature-seam
type: execute
---

<objective>
Tighten the signature seam so `sig31` is no longer carried by a trivial witness and the repo’s signature path becomes theorem-critical.

Purpose: The bridge modules should attach to a non-empty, non-trivial signature seam. Right now `DASHI/Physics/Signature31.agda` returns `sig31` by definition; this plan identifies which signature theorems are real vs prototype, then refactors the surface so the trivial witness is isolated (or removed) without breaking the Stage C ladder.
Output: An inventory of signature seam entrypoints + a constrained change that makes the seam non-trivial (or explicitly marks the trivial module as prototype-only and ensures no canonical path depends on it).
</objective>

<execution_context>
~/.claude/get-shit-done/workflows/execute-phase.md
./summary.md
</execution_context>

<context>
@.planning/PROJECT.md
@.planning/ROADMAP.md
@.planning/STATE.md

# Signature seam surfaces (explicitly referenced earlier):
@DASHI/Physics/Signature31.agda
@DASHI/Geometry/Signature31FromConeArrowIsotropy.agda
@DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda
@DASHI/Geometry/Signature/Elimination.agda
@DASHI/Geometry/Signature31Lock.agda

# Canonical ladder index (to check what depends on what):
@DASHI/Physics/Closure/PhysicsClosureSummary.agda

# Realization-specific bridge currently in tree:
@DASHI/Physics/Signature31FromShiftOrbitProfile.agda
</context>

<tasks>

<task type="auto">
  <name>Task 1: Inventory all signature seam entrypoints and classify trivial vs theorem-critical</name>
  <files>.planning/08-01-SIGNATURE-SEAM-INVENTORY.md</files>
  <action>
Create `.planning/08-01-SIGNATURE-SEAM-INVENTORY.md` with:
- A list of modules providing `sig31` / Signature31 claims.
- For each module, categorize: `trivial`, `realization-specific theorem`, `assumption-based`, `canonical export`.
- Identify which modules the canonical Stage C ladder actually imports/exports (use `PhysicsClosureSummary.agda` as the starting index).

What to avoid and why:
- Do NOT change any code in this task; this is a dependency+classification audit.
  </action>
  <verify>
Inventory file exists and includes `DASHI/Physics/Signature31.agda` and at least one non-trivial signature path module (e.g. `...FromConeArrowIsotropy` or `...FromShiftOrbitProfile`).
  </verify>
  <done>
We have a concrete map of what signature seam modules exist and which ones are prototype/trivial.
  </done>
</task>

<task type="auto">
  <name>Task 2: Tighten the seam by isolating or removing the trivial Signature31 witness from canonical paths</name>
  <files>DASHI/Physics/Signature31.agda, DASHI/Physics/Closure/PhysicsClosureSummary.agda</files>
  <action>
Implement the smallest change that achieves BOTH:
1) The module `DASHI/Physics/Signature31.agda` is explicitly marked as prototype-only OR restructured so it no longer provides a trivial global theorem by default.
2) The canonical closure ladder should depend on a theorem-critical signature path (realization-specific is OK for now) or, if it currently does not, it must be explicit in the summary index which signature path is canonical.

Acceptable tightening moves (choose the minimal one):
- Option A: Rename/adjust exports in `DASHI/Physics/Signature31.agda` so the trivial function is not named like a theorem and cannot be imported accidentally as canonical.
- Option B: Update `PhysicsClosureSummary.agda` to re-export the theorem-critical signature source and stop re-exporting the trivial one.

What to avoid and why:
- Do NOT touch Stage C proofs beyond what is required to re-point imports/exports.
- Do NOT introduce new postulates in the core seam.
  </action>
  <verify>
- `agda -i . -i /usr/share/agda/lib/stdlib DASHI/Everything.agda` succeeds.
- Grep check: canonical exports in `DASHI/Physics/Closure/PhysicsClosureSummary.agda` do not route signature claims through the trivial witness module.
  </verify>
  <done>
The signature seam is tightened: trivial witness is isolated, and the canonical path clearly points at a theorem-critical source.
  </done>
</task>

</tasks>

<verification>
Before declaring this plan complete:
- [ ] `.planning/08-01-SIGNATURE-SEAM-INVENTORY.md` exists
- [ ] `DASHI/Everything.agda` typechecks
- [ ] Canonical closure summary index clearly distinguishes theorem-critical signature path from prototype/trivial path
</verification>

<success_criteria>

- Trivial signature witness cannot be accidentally treated as canonical
- The canonical signature seam is explicit and theorem-critical (even if still realization-specific)
- Repo still typechecks
</success_criteria>

<output>
After completion, create `.planning/08-01-SIGNATURE-SEAM-SUMMARY.md` with:
- Accomplishments
- Files modified
- Decisions made (what is canonical signature source now)
- Issues encountered
- Next step: either (a) strengthen the theorem-critical signature path, or (b) proceed to GR/QFT adapters knowing the seam is no longer empty.
</output>

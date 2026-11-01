---
phase: 07-physics-bridge
type: execute
---

<objective>
Plan and lay down thin “bridge” modules that attach to the signature forcing seam and expose a stable mapping surface toward GR/QFT structures.

Purpose: Make the bridge architecture explicit without importing a full GR/QFT library yet; define adapter boundaries so future work connects to the core spine without destabilizing it.
Output: A concrete bridge module skeleton set + an explicit mapping table from closure concepts to physics concepts.
</objective>

<execution_context>
~/.claude/get-shit-done/workflows/execute-phase.md
./summary.md
</execution_context>

<context>
@.planning/PROJECT.md
@.planning/ROADMAP.md
@.planning/STATE.md

# Core interface seam:
@DASHI/Physics/ClosureGlue.agda

# Signature seam:
@DASHI/Physics/Signature31.agda
@DASHI/Geometry/Signature31FromConeArrowIsotropy.agda
@DASHI/Geometry/Signature31FromIntrinsicShellForcing.agda

# Canonical Stage C surface / consumers:
@DASHI/Physics/Closure/PhysicsClosureSummary.agda
@DASHI/Physics/UnificationClosure.agda
@DASHI/Physics/UnifiedClosure.agda
</context>

<tasks>

<task type="auto">
  <name>Task 1: Write a bridge mapping spec (no code moves)</name>
  <files>.planning/07-02-PHYSICS-BRIDGE-MAPPING.md</files>
  <action>
Create `.planning/07-02-PHYSICS-BRIDGE-MAPPING.md` with a tight mapping table.

Center the spec on the already-existing core seam:
- `ClosureAxioms` fields: `S`, `U`, `T`, `sc`, `inv`, `iso`, `fs`.
- Signature seam output: `sig31` and whatever witness path currently exists.

Mapping table requirements:
- For each closure concept, give the physics concept it will map to, but keep it abstract and interface-like.
- Explicitly mark what is currently “stubbed/prototype” vs “theorem-critical”.

What to avoid and why:
- Do NOT claim we have full GR/QFT objects in Agda yet.
- Do NOT import new libraries; this is an adapter boundary definition.
  </action>
  <verify>
File exists and includes the literal identifiers `ClosureAxioms` and `sig31` and references real module paths in this repo.
  </verify>
  <done>
Bridge mapping spec exists and is specific enough to drive implementation of bridge module skeletons.
  </done>
</task>

<task type="auto">
  <name>Task 2: Add thin bridge module skeletons (no semantics yet)</name>
  <files>
DASHI/Physics/Bridge.agda,
DASHI/Physics/LorentzBridge.agda,
DASHI/Physics/CliffordBridge.agda,
DASHI/Physics/GR.agda,
DASHI/Physics/QFT.agda
  </files>
  <action>
Create the five modules listed in <files> as minimal compilable skeletons that:
- Import `DASHI.Physics.ClosureGlue` and re-export the bridge surface types.
- Contain only records/types/signatures and TODO-like placeholders expressed as parameters (avoid `postulate` unless already the repo’s chosen pattern in this layer).
- Make the attachment point explicit: bridge modules sit “above” the signature forcing seam and below any GR/QFT detail.

What to avoid and why:
- Do NOT thread experimental validation surfaces (`Verification.*`) into these modules.
- Do NOT re-export the entire Stage C ladder; keep bridges small and focused.
  </action>
  <verify>
`agda -i . -i /usr/share/agda/lib/stdlib DASHI/Physics/Bridge.agda` succeeds (and similarly for the other four modules).
  </verify>
  <done>
Bridge skeleton modules compile and clearly document where the GR/QFT adapters will attach.
  </done>
</task>

</tasks>

<verification>
Before declaring this plan complete:
- [ ] `.planning/07-02-PHYSICS-BRIDGE-MAPPING.md` exists
- [ ] All five bridge modules typecheck individually
- [ ] No new dependencies introduced
</verification>

<success_criteria>

- Bridge plan is explicitly centered on `ClosureAxioms` and the signature forcing seam
- Bridge modules exist as stable adapter boundaries
- No repository refactors; only additive skeletons + mapping spec
</success_criteria>

<output>
After completion, create `.planning/07-02-PHYSICS-BRIDGE-SUMMARY.md` with:
- Accomplishments
- Files created
- Decisions made (adapter boundaries)
- Issues encountered
- Next step: “Ready for 07-03 Real Operators”
</output>

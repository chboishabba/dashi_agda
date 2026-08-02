---
phase: 07-real-operators
type: execute
---

<objective>
Turn the current “generic contractive operator system” into a non-toy, theorem-critical real-operator instance by identifying and tightening the real operator definitions `Cᵣ`, `Pᵣ`, `Rᵣ`.

Purpose: The missing substance is real operators satisfying the closure axioms; this plan makes that gap explicit and drives it to the first credible non-toy instance.
Output: A stub inventory + a concrete decision on what is considered “real operator” vs “prototype identity” + first upgraded operator(s) with proofs needed by the stack.
</objective>

<execution_context>
~/.claude/get-shit-done/workflows/execute-phase.md
./summary.md
</execution_context>

<context>
@.planning/PROJECT.md
@.planning/ROADMAP.md
@.planning/STATE.md

# Existing operator definitions and stack wiring:
@DASHI/Physics/RealOperators.agda
@DASHI/Physics/RealOperatorStack.agda
@DASHI/Physics/RealOperatorStackShift.agda

# Metrics used by nonexpansive/strictness claims:
@DASHI/Metric/FineAgreementUltrametric.agda
@DASHI/Metric/AgreementUltrametric.agda

# Strictness and fiber contraction glue:
@DASHI/Geometry/StrictContractionComposition.agda
@DASHI/Geometry/FiberContraction.agda
</context>

<!--
Backend cross-reference: the current Dashi real-arithmetic policy is recorded
in DASHI/Analysis/CubicalHoTTRealBackendBoundary.agda and the finite rational
transport surface is in
DASHI/Foundations/UBP/RationalCertificateTransport.agda. Keep rationalizable
estimates in normalized ℚ before embedding into the Bishop ordered-real
authority; treat Cubical/HoTT reals as a comparative lane rather than a
replacement dependency. Bishop commit
d732b0340d729b264227a70fcf38383d8fb3ac3c closes the current K-abs/index
migration seam. This planning file concerns operator semantics and should not
silently expand either the Agda 2.9 migration or the exact-real backend scope.
-->

<tasks>

<task type="auto">
  <name>Task 1: Stub inventory + gap statement for Cᵣ/Pᵣ/Rᵣ</name>
  <files>.planning/07-03-REAL-OPERATORS-INVENTORY.md</files>
  <action>
Create `.planning/07-03-REAL-OPERATORS-INVENTORY.md` with:
- Exact current definitions of `Cᵣ`, `Pᵣ`, `Rᵣ` (quote the key lines / describe behavior).
- Which ones are identity/prototype and why that is currently “not yet physical”.
- What properties are already proved (e.g. nonexpansive) and which are missing for “credible”.

What to avoid and why:
- Do NOT change operator semantics in this task; this is an audit artifact that grounds later changes.
  </action>
  <verify>
File exists and explicitly mentions `Cᵣ`, `Pᵣ`, and `Rᵣ` and references the exact module paths.
  </verify>
  <done>
Operator gap is documented in a way that makes the next upgrade steps unambiguous.
  </done>
</task>

<task type="checkpoint:decision" gate="blocking">
  <decision>Define what counts as the first “non-toy” real operator instance</decision>
  <context>
Right now `Cᵣ` and `Rᵣ` are identity in `DASHI/Physics/RealOperators.agda` and `Pᵣ` is a small projection-like head-zeroing operation. To make the physics bridge credible, we need to decide what minimal nontrivial semantics is acceptable for the first upgraded instance, without destabilizing compilation.
  </context>
  <options>
    <option id="minimal-nontrivial">
      <name>Minimal nontrivial upgrade (Recommended)</name>
      <pros>Keep proofs manageable; upgrade exactly one of Cᵣ or Rᵣ to a meaningful transformation while preserving existing nonexpansive/strictness scaffolding.</pros>
      <cons>May still feel “prototype-ish”; requires a follow-on plan for full physical semantics.</cons>
    </option>
    <option id="operator-triad">
      <name>Upgrade full triad at once</name>
      <pros>Faster path to a coherent operator story (Cᵣ/Pᵣ/Rᵣ all meaningful together).</pros>
      <cons>High risk of breaking proofs and typecheck; larger diff and more debugging.</cons>
    </option>
    <option id="freeze-and-bridge">
      <name>Freeze operators as-is and focus on bridge scaffolding only</name>
      <pros>Lets bridge modules land quickly; minimal disruption.</pros>
      <cons>Confirms the current criticism: closure proofs are about a generic system, not a physical one.</cons>
    </option>
  </options>
  <resume-signal>Select: minimal-nontrivial, operator-triad, or freeze-and-bridge</resume-signal>
</task>

<task type="auto">
  <name>Task 2: Implement the chosen upgrade and preserve the proof obligations</name>
  <files>DASHI/Physics/RealOperators.agda, DASHI/Physics/RealOperatorStack.agda</files>
  <action>
Based on the decision, implement the smallest change that moves at least one operator away from identity while:
- preserving nonexpansive proofs or updating them to match,
- keeping `RealOperatorStack` compiling,
- and keeping the change localized to the operator layer.

What to avoid and why:
- Do NOT touch signature forcing / Stage C ladder in this plan; keep blast radius small.
- Do NOT move modules; only edit in-place.
  </action>
  <verify>
`agda -i . -i /usr/share/agda/lib/stdlib DASHI/Physics/RealOperatorStack.agda` succeeds.
  </verify>
  <done>
At least one of `Cᵣ` or `Rᵣ` is non-identity with corresponding proof obligations still satisfied.
  </done>
</task>

</tasks>

<verification>
Before declaring this plan complete:
- [ ] Inventory file exists
- [ ] Decision checkpoint completed
- [ ] `DASHI/Physics/RealOperatorStack.agda` typechecks
</verification>

<success_criteria>

- The “missing real operators” gap is documented concretely
- A clear decision is made about minimal acceptable non-toy semantics
- The code reflects that decision with a compile-checked operator upgrade
</success_criteria>

<output>
After completion, create `.planning/07-03-REAL-OPERATORS-SUMMARY.md` with:
- Accomplishments
- Decision made and rationale
- Files modified
- Compile status
- Next step: “Ready for 07-04 Repo Classification Audit”
</output>

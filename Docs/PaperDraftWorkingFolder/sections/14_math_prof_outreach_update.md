# 14. Math-Professor Outreach Update for Paper Strategy

Status: `docs-only; paper-strategy update; non-promoting`

## Compact O/R/C/S/L/P/G/F Summary

O: Paper 1 is owned by the DASHI paper-working folder and must remain a
constructive physics-unification manuscript with fail-closed typed receipt
governance, not a completed-physics paper. This worker owns only
`Docs/PaperDraftWorkingFolder/sections/14_math_prof_outreach_update.md`.

R: Integrate `Docs/MathProfOutreachSummary.md` and
`Docs/MATH_PROF_OUTREACH_CROSSWALK.md` into the Paper 1 strategy. The update
must keep outreach material non-promoting, make the math program credible, and
keep the physics program early.

C: Inputs read for this section are `Docs/MathProfOutreachSummary.md`,
`Docs/MATH_PROF_OUTREACH_CROSSWALK.md`,
`Docs/PaperDraftWorkingFolder/Paper1_Manuscript.md`,
`Docs/PaperDraftWorkingFolder/SourceLedger.md`, and
`Docs/PaperDraftWorkingFolder/ClaimLedger.md`.

S: The current manuscript already defines a conservative claim boundary: G2
schema adoption, G6 tracked commuting, G3 selected finite-support support, and
E8/Lila local-to-upstream boundaries are admissible; empirical validation, GR
recovery, continuum recovery, matter/gauge closure, and full unification are
blocked. The outreach update strengthens the orbit-shell/signature story and
identifies local scaffold modules, but it does not promote those scaffolds into
physics closure.

L: Outreach material should be ordered by paper use: introduction framing,
related-work/provenance positioning, future-work staging, and explicit open
gaps. Progress means better routing and cleaner claim discipline, not a larger
positive theorem inventory.

P: Reshape the introduction around the shell-orbit profile invariant and
Lorentz signature class `(3,1)` as the strongest credible mathematical
motivation; reshape related work around orbit-shell, signed block-preserving,
B4-neighborhood, wave-lift, graded-series, and bridge-scaffold provenance; and
reshape future work around the exact gaps still blocking physical promotion.

G: Outreach docs, archive crosswalks, and local summary files are
non-promoting. Paper 1 may use them to select emphasis and explain provenance,
but promoted claims still require current repo theorem, receipt, audit,
diagnostic, or blocker surfaces according to the source and claim ledgers.

F: The remaining gap is not exposition alone. DASHI still lacks one clean
natural dynamics law, a conserved physical quantity with settled
interpretation, an explicit continuum-limit theorem, strong matter/gauge/
constraint closure, realization-independent closure, and fully interpreted
wave-lifted graded or modular trace structure.

## Strategy Change

The math-prof outreach update should sharpen Paper 1 rather than broaden it.
The safe strategic change is to make the introduction more explicit about the
mathematical object that looks serious: a shell-orbit profile invariant that
selects the Lorentz signature class `(3,1)` in the present four-dimensional
framework. This should be presented as a symmetry and orbit-profile result or
research spine, not as a completed physical derivation.

The manuscript should therefore distinguish three layers earlier than it
currently does:

1. The mathematical spine: orbit-shell/signature structure, the `[24,6,2]`
   profile, signed block-preserving action, and the Lorentz signature class.
2. The local scaffold layer: explicit Agda modules and exported summary
   surfaces that make adjacent bridge objects concrete.
3. The open physics layer: dynamics, conservation, continuum, matter/gauge,
   and realization-independent closure obligations that remain unpromoted.

This framing improves credibility because it lets the paper say why the
program is mathematically nontrivial without implying that the physics program
has closed. The right tone is: "the orbit-shell/signature spine is a serious
mathematical reason to study the architecture; typed governance explains why
the physical interpretation remains gated."

## Introduction Update

The introduction should add a short paragraph after the existing
claim-control framing that identifies the orbit-shell/signature spine as a
motivation for the fail-closed architecture. The paragraph should avoid
phrases like "derives spacetime," "derives relativity," or "proves Lorentzian
physics." A safe formulation is:

```text
A central mathematical motivation for the present architecture is the
appearance of a shell-orbit profile invariant whose current theorem ladder
selects the Lorentz signature class (3,1) inside the four-dimensional
framework. In this paper that fact is treated as a symmetry and orbit-profile
signal, not as a completed physical unification claim. Its role is to motivate
the typed closure ledger: if such a profile is to become physical structure,
the intervening dynamics, conservation, continuum, matter/gauge, and
realization-independent closure obligations must be represented explicitly.
```

The introduction should also make the local scaffold layer visible without
over-selling it. The outreach summary identifies several local surfaces that
are no longer merely archive-side suggestions:

- `DASHI.Physics.WaveLiftEvenSubalgebra`
- `DASHI.Physics.OrbitShellGeneratingSeriesRootSystemB4`
- `DASHI.Physics.Moonshine.FiniteGradedShellSeriesRootSystemB4`
- `DASHI.Physics.Moonshine.FiniteTwinedShellTraceRootSystemB4`
- `DASHI.Physics.LorentzNeighborhoodDynamicCandidate`
- `DASHI.Physics.Closure.CanonicalGaugeConstraintBridgeTheorem`
- `DASHI.Physics.Closure.ParametricGaugeConstraintTheorem`
- `DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem`
- `DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem`

The paper should call these "local formal scaffolds," "bridge scaffolds," or
"summary surfaces," not completed laws. The orbit-shell generating series
should be upgraded from "promising next object" to "local formal object
already present," while the B4 comparison remains a neighborhood classifier
and negative/contrastive check, not a Lorentz confirmation by itself.

## Related-Work and Provenance Update

The related-work/provenance section should incorporate the outreach crosswalk
as a routing source for why certain mathematical neighborhoods appear in the
paper. It should not cite the crosswalk as theorem authority. The best use is
to group related material into four non-promoting contexts.

First, orbit-shell and signature context should be tied to
`Docs/OrbitShellProfilesAndLorentzSignature.md` and
`Docs/MinimalCrediblePhysicsClosure.md` when the manuscript needs repo-local
supporting surfaces. The outreach documents can explain why this material is
emphasized for math-professor readability.

Second, signed block-preserving and B4/Weyl-neighborhood context should be
used to clarify classification, not confirmation. The related-work prose
should say that the B4 shell-comparison surfaces help locate the neighborhood
of the invariant and constrain mistaken readings. They should not be made into
a positive physics result.

Third, wave, psi, and wave-lift context should be treated as background for
future bridges. `DASHI.Physics.WaveLiftEvenSubalgebra` gives the paper a real
local scaffold to mention if needed, but the manuscript should still say that
wave-lifted physical interpretation and theorem significance are open.

Fourth, graded-series, twined-trace, moonshine-adjacent, and JMD/Monster
material should stay in provenance or future work. The existence of finite
graded-shell and twined-trace scaffolds supports the claim that the repo has
formal objects in that direction. It does not support modular closure, a
graded-trace theorem with physical interpretation, or any Monster-dependent
Paper 1 claim.

## Future-Work Update

The future-work section should be made more precise by splitting the open
queue into mathematical completion tasks and physical promotion tasks.

Mathematical completion tasks include:

1. strengthening the orbit-shell theorem ladder around the `[24,6,2]` profile
   and the bounded one-minus family;
2. clarifying the signed block-preserving action as the stable symmetry
   picture;
3. turning B4/Weyl comparison surfaces into a clearer classification boundary;
4. interpreting finite orbit-shell generating series as local formal objects;
5. determining what, if anything, graded-shell and twined-trace scaffolds prove
   beyond finite scaffold status.

Physical promotion tasks remain much harder and should be stated as blockers:

1. no clean natural dynamics law is currently promoted;
2. no conserved physical quantity has a settled interpretation;
3. no explicit continuum-limit theorem is promoted;
4. matter/gauge/constraint closure remains scaffold-level, not strong closure;
5. no realization-independent theorem is present;
6. no fully interpreted wave-lifted graded object or modular/graded-trace
   closure is present.

The key editorial point is that the math route can be credible while the
physics route stays early. This is not a contradiction; it is the reason Paper
1 should remain a fail-closed architecture paper.

## Open Gaps To Keep Visible

The following gaps should be explicitly protected from accidental promotion in
Paper 1:

- Orbit-shell/signature selection does not by itself provide a dynamics law.
- The Lorentz signature class `(3,1)` is a signature-class selection signal,
  not sourced GR, Einstein equations, or continuum recovery.
- The B4 comparison classifies a neighborhood and supplies contrastive
  evidence, but it is not a physical confirmation route.
- `LorentzNeighborhoodDynamicCandidate` is a candidate scaffold, not a closed
  physical law.
- Gauge and spin-local bridge theorem surfaces are bridge scaffolds or
  summaries; strong matter/gauge/constraint closure remains open.
- Wave-lift and graded-series surfaces are local formal scaffolds; their
  physical and moonshine-adjacent significance remains open.
- Outreach archive and crosswalk material may route paper strategy, but cannot
  replace canonical Agda receipts, audits, diagnostics, or blocker surfaces.

## Exact Source-Ledger Update Proposal

Do not edit the source ledger from this worker lane. The proposed exact update
for `Docs/PaperDraftWorkingFolder/SourceLedger.md` is:

```markdown
## Math-Professor Outreach Update Context

- Source: `Docs/MathProfOutreachSummary.md`
- Source thread title: `Math Prof Outreach Stage`
- Online UUID: `69aa52b4-6f7c-839f-aa7f-d120ffe0c1ad`
- Canonical thread ID: `decf9e3cde5ccdec0c51ad8aab15999201503998`
- Source used: local DB summary
- Use in Paper 1: non-promoting manuscript-strategy context. Use to sharpen
  the introduction around the shell-orbit profile invariant and Lorentz
  signature class `(3,1)`, to identify local scaffold surfaces that may be
  named cautiously, and to keep the math program credible while preserving the
  physics program as early.

- Source: `Docs/MATH_PROF_OUTREACH_CROSSWALK.md`
- Source thread title: `Math Prof Outreach Stage`
- Online UUID: `69aa52b4-6f7c-839f-aa7f-d120ffe0c1ad`
- Canonical thread ID: `decf9e3cde5ccdec0c51ad8aab15999201503998`
- Source used: local DB crosswalk against repo docs/code
- Use in Paper 1: non-promoting evidence-routing context. Use to route
  orbit-shell/signature, signed block-preserving, B4/Weyl-neighborhood,
  wave-lift, graded-series, gauge-bridge, and open-physics-gap material into
  introduction, related-work/provenance, future-work, and exclusion language.
  Not theorem authority, not empirical authority, not literature authority, and
  not a substitute for current repo-local typed receipts, audits, diagnostics,
  or blocker surfaces.

Interpretation rule: math-professor outreach sources may reshape Paper 1
emphasis and explain why a mathematical or physical question is visible, but
they do not promote claims. Promoted Paper 1 claims must still cite current
DASHI theorem, receipt, audit, diagnostic, or blocker surfaces in the priority
order already recorded in this source ledger. Local scaffold modules named by
the outreach sources should be described as scaffolds or summary surfaces
unless their owning canonical receipt surface supplies the stronger theorem.
```

## Compact Manuscript Patch Queue

1. Introduction: add one paragraph on shell-orbit/signature motivation using
   the safe wording above.
2. Introduction or abstraction layer: add one sentence distinguishing the
   mathematical spine, local scaffold layer, and open physics layer.
3. Related work/provenance: cite the outreach summary and crosswalk as
   non-promoting routing sources after updating `SourceLedger.md`.
4. Future work: split the queue into mathematical completion tasks and
   physical promotion blockers.
5. Claim ledger review: preserve the current positive claim set; do not add
   orbit-shell/signature, wave-lift, B4, graded-series, gauge, or dynamics
   claims unless their canonical receipt surfaces are explicitly promoted by
   the owning lanes.

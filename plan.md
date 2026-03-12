# Dashboard Plan

## Phase
Stage C canonical bridge hardening complete; physics-closure execution checklist activated (active 2026-03-12).

## Current Milestone (2026-03-12)
Execute the canonical physics-closure chain in strict order:
`ProjectionDefectSplitForcesParallelogram`
→ `ContractionForcesQuadraticStrong`
→ `ContractionForcesQuadraticTheorem`
→ `ContractionQuadraticToSignatureBridgeTheorem`
→ `QuadraticToCliffordBridgeTheorem`
→ `ContractionSignatureToSpinDiracBridgeTheorem`
→ `CliffordToEvenWaveLiftBridgeTheorem`
→ `PhysicsClosureFull`.

Execution checklist source:
`Docs/PhysicsClosureImplementationChecklist.md`

## Milestones
1. Canonical spine declaration and import policy. (done)
2. Quadratic route consolidation to the split/parallelogram route. (done)
3. Signature route consolidation to theorem-primary causal classification. (done)
4. Canonical quadratic-to-Clifford bridge from normalized quadratic output. (done)
5. Canonical `WaveLift⇒Even` factorization theorem and bridge threading. (done)
6. Keep closure label registry and status docs synchronized as modules evolve. (active)
7. Strengthen Lemma A/B internals while preserving canonical interfaces. (active)

## Milestone Tasks
1. Keep canonical route map aligned to current implementation:
   `ProjectionDefect → ProjectionDefectSplitForcesParallelogram
   → ProjectionDefectToParallelogram → QuadraticForm
   → ContractionForcesQuadraticStrong → CausalForcesLorentz31
   → ContractionQuadraticToSignatureBridgeTheorem
   → QuadraticToCliffordBridgeTheorem
   → CliffordToEvenWaveLiftBridgeTheorem`.
2. Classify parallel modules as `alternative` or `validation`:
   - `QuadraticFromNorm`
   - `QuadraticFromProjection`
   - `QuadraticFromParallelogram`
   - `QuadraticEmergence`
   - `QuadraticFormEmergence`
3. Ensure closure planning references
   `ContractionForcesQuadraticStrong` for canonical contraction-to-quadratic
   tracking and seam management.
4. Update `PhysicsClosureValidationSummary` plan notes to consume canonical
   spine exports first, then optional cross-check packages.
5. Keep runtime guardrail:
   skip routine direct checks of `PhysicsClosureValidationSummary.agda`
   until runtime bound improves from the current ~1.25h observation.
6. Keep routine guardrail:
   skip routine direct checks of `PhysicsClosureValidationSummary.agda`
   while runtime remains around the current ~1.25h bound.
7. Maintain canonical-first references in repo-facing docs and closure plan
   notes as modules are added/promoted.
8. Re-run targeted checks for canonical bridge modules when updating bridge docs:
   `CliffordEvenLiftBridge`, `CliffordToEvenWaveLiftBridgeTheorem`,
   `CanonicalContractionToCliffordBridgeTheorem`,
   `KnownLimitsQFTBridgeTheorem`.

## Exit Checkpoint
- One canonical spine documented and used for closure claims.
- No parallel emergence route required by the closure claim path.
- Open seams listed once, on canonical modules only.

## Assumptions
- Existing projection-defect and energy-split theorem surfaces are stable.
- Alternate derivation modules will remain available as non-canonical checks.
- No theorem statement changes are needed to adopt canonical routing.

## Open Questions
- Should `ParallelogramToInnerProduct` or `InnerProductFromParallelogram`
  be the single exported polarization entrypoint?
- Should canonical exports reference `DASHI.Energy.EnergySplitProof` or
  `DASHI.Geometry.EnergySplitProof` as the stable split surface?
- Which currently exported theorem bundles still import
  `QuadraticFormEmergence` transitively and need rerouting first?

## Next Skill
`long-running-development` to execute
`Docs/PhysicsClosureImplementationChecklist.md` in-order, proving one
milestone group at a time with targeted Agda checks after each group.

## Active Signature Classification Focus (2026-03-11)

- Keep `ContractionQuadraticToSignatureBridgeTheorem` interface unchanged.
- Replace profile-only internals with a theorem-primary
  quadratic+causal+symmetry classification route:
  `ContractionForcesQuadraticStrong.uniqueUpToScaleWitness`
  -> normalized `Q̂core`
  -> causal elimination/classification
  -> `(3,1)` signature theorem.
- Split the new signature classification internals into two explicit lemmas:
  1) Euclidean/degenerate competitor elimination from cone+arrow compatibility.
  2) Spatial isotropy + one arrow direction + finite speed force `(3,1)`.
- Keep orbit-profile data as a secondary witness/cross-check path, not the
  core theorem driver.

## Closure Pipeline Governance

- `0.1` Governance baseline: done.
  `Docs/ClosurePipeline.md` is now the authoritative Stage C claim map with
  `canonical` / `supporting` / `experimental` labels.
- `0.2` Enforcement pass: done.
  Existing closure-relevant modules are now labeled in
  `Docs/ClosurePipeline.md` and repo-facing citation order is explicitly
  canonical-first.
- Next:
  keep the label registry synchronized with new module additions/promotions.

# Dashboard Plan

## Phase
Stage C spine simplification and routing cleanup (active 2026-03-11).

## Milestones
1. Canonical spine declaration and import policy.
2. Quadratic route consolidation to the parallelogram/polarization path.
3. Signature route consolidation to cone/isotropy canonical path.
4. Validation summary reroute to canonical-first imports.
5. Open seam registry narrowed to canonical path only.

## Milestone Tasks
1. Add canonical route map to docs:
   `ProjectionDefect → EnergySplitProof → Parallelogram → QuadraticForm
   → ConeTimeIsotropy → Signature31FromConeArrowIsotropy → Signature31Lock`.
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
`long-running-development` to execute module import and seam-surface rewiring
against this plan.

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

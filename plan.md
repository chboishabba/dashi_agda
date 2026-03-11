# Dashboard Plan

## Phase
Stage C spine simplification and routing cleanup (active 2026-03-11).

## Milestones
1. Canonical spine declaration and import policy.
2. Quadratic route consolidation to the parallelogram/polarization path.
3. Signature route consolidation to cone/isotropy canonical path.
4. Canonical quadratic-to-Clifford bridge from normalized quadratic output.
5. Validation summary reroute to canonical-first imports.
6. Open seam registry narrowed to canonical path only.
6. `Quadratic⇒Clifford` theorem surface hardened for downstream
   `WaveLift⇒Even`.
7. Canonical `WaveLift⇒Even` factorization theorem landed.

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
6. Add and wire
   `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`
   so canonical Clifford emergence consumes
   `ContractionForcesQuadraticStrong` normalized quadratic data and exposes
   an explicit universal-property seam.
6. Land a canonical split/parallelogram bridge module and route
   contraction→quadratic theorem surfaces through it without changing the
   contraction→signature bridge interface.
7. Expand strengthened contraction outputs to include explicit theorem-facing
   strength fields (`invariantUnderT`, `nondegenerate`,
   `compatibleWithIsotropy`) while keeping the existing normalization witness.
8. Extend `DASHI.Physics.CliffordEvenLiftBridge` with canonical grading and
   even-subalgebra interfaces, plus canonical wave-lift factorization fields.
9. Rewire `DASHI.Physics.ConcreteClosureStack` so `q2cl` and `wl` inhabit the
   strengthened theorem surface by construction.
10. Add/update `DASHI.Physics.WaveLiftEvenSubalgebra` so it matches the
    canonical bridge record and exposes a concrete factorization witness form.
11. Run targeted Agda checks for:
    `CliffordEvenLiftBridge`, `ConcreteClosureStack`,
    `CanonicalContractionToCliffordBridgeTheorem`, and
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
`update-docs-todo-implement` for strict docs/TODO/code/changelog synchronization
on canonical `Quadratic⇒Clifford → WaveLift⇒Even` completion work.

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

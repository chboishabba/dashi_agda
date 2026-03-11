# TODO

## Cleanup / Consolidation

- Runtime policy:
  do not run `PhysicsClosureValidationSummary.agda` in routine validation until
  runtime bounds are acceptable (currently ~1.25 hours).
- Canonical pipeline policy:
  use `Docs/ClosurePipeline.md` as the single Stage C claim path, and label new
  closure modules as `canonical`, `supporting`, or `experimental`.
- Make grouped wave-regime ladder modules authoritative for new imports:
  - `Closure/Algebra/WaveRegime.agda`
  - `Closure/Recovery/WaveRegime.agda`
  - `Closure/Consumers/WaveRegime.agda`
  - `Moonshine/Reports/WaveRegime.agda`
- Rewire canonical Stage C bundles and repo-facing summaries to use grouped
  ladder modules instead of direct per-rung imports where practical.
- Keep per-rung modules as compatibility wrappers only.
- Keep top-level compile green while doing the refactor.

## Base369 Normalization Hardening

Priority bucket: `P1`

- [x] Add closed-form cyclic constructors:
  `fromTriIndex`, `fromHexIndex`, `fromNonaryIndex`.
- [x] Add closed-form cyclic operators in `Base369.agda`:
  `triXor-closed`, `hexXor-closed`, `nonaryXor-closed`.
- [x] Prove triadic bridge first:
  `triXor-spin-correct : triXor-spin a b ≡ triXor a b`.
- [x] Keep existing recursive `spin`-based operators as compatibility
  definitions until downstream imports switch.
- [x] Follow-up: swap canonical exports to closed-form operators now that tri,
  hex, and nonary correctness bridges are in place.
- [x] Add first `abstract` barriers around heavy closure theorem-bundle
  summary aliases in `PhysicsClosureValidationSummary`.
- [x] Follow-up: extend `abstract` barriers to
  `CanonicalStageCTheoremBundle` and `CanonicalStageCSummaryBundle`, then
  re-measure targeted closure-summary typecheck time.
- [x] Next follow-up: expand the same pattern to remaining heavy
  moonshine/regime aliases in `PhysicsClosureValidationSummary` and re-check
  targeted bundle modules.
- [ ] Next follow-up: re-run direct
  `PhysicsClosureValidationSummary.agda` timing/validation once the upstream
  bridge-seam type error is cleared.
- [x] Pipeline enforcement: tag existing closure-relevant modules in docs as
  `canonical` / `supporting` / `experimental` and remove ambiguous duplicates
  from repo-facing claims.
- [ ] Keep `Docs/ClosurePipeline.md` label registry current whenever new
  closure modules are added or promoted.

## Track S — Canonical Spine Simplification

Priority bucket: `P0`

- Declare the canonical closure spine in theorem-bundle and summary docs:
  `ProjectionDefect → EnergySplitProof → Parallelogram → QuadraticForm
  → ConeTimeIsotropy → Signature31FromConeArrowIsotropy → Signature31Lock`.
- Classify quadratic/signature parallel routes as one of:
  `alternative`, `validation`, `experimental`.
- Rewire canonical Stage C and closure summaries so canonical claims do not
  depend on `QuadraticEmergence` / `QuadraticFormEmergence` as required steps.
- Keep `ProjectionDefectToParallelogram` and
  `ContractionForcesQuadraticStrong` as canonical bottleneck bridge modules.
- Keep a single seam registry on canonical modules only; remove duplicated seam
  placeholders from non-canonical derivation surfaces.

## Track T — Dynamical / Theorem Closure

Priority bucket: `P0`

Open physics-side requirements that remain genuinely unresolved:

- natural physical dynamics law
- conserved physical quantity with clear interpretation
- explicit continuum-limit theorem
- realization-independent proof
- full gauge/matter recovery as theorem rather than program

Current focus:
`DASHI/Geometry/ProjectionDefectToParallelogram.agda` and
`DASHI/Physics/Closure/ContractionForcesQuadraticStrong.agda`

- Replace the raw `Set` seam in `ContractionForcesQuadraticStrong` with a
  named uniqueness/compatibility seam record.
- Replace the placeholder-style pending field in
  `ContractionQuadraticToSignatureBridgeTheorem` with a named bridge seam
  record that makes the remaining quadratic/signature compatibility gap
  explicit.

- Replace trivial closure fallbacks on the minimum credible path.
  Current priority:
  `PhysicsClosureFullInstance` and `PhysicsClosureEmpiricalToFull` should use
  the real shift dynamics package, the intrinsic `(3,1)` theorem path, and
  the same concrete constraint-closure witness.
- Tighten downstream closure consumers so they depend on theorem-backed closure
  data, not only type-level metric availability.
- Extend the dynamics package beyond Fejer/closest-point/MDL if a concrete
  causal propagation or effective-geometry witness becomes available.
- Add a typed dynamics-status surface to the canonical shift package:
  propagation,
  causal admissibility,
  monotone quantity,
  effective geometry.
- Add a semantics-bearing dynamics witness companion to the canonical shift
  package and thread it through canonical Stage C and spin/Dirac consumers.
- Add a canonical constraint-closure status surface and a known-limits status
  surface so the broader physics runway is explicit without overstating
  recovery.
- Land the first scoped known-limits recovery witness on the canonical path
  and keep the next recovery target narrow:
  stronger local propagation / local-Lorentz follow-through before any GR/QFT
  claim.
- Keep the witness-bearing canonical spin/Dirac consumer on the authoritative
  Stage C path and treat broader matter/gauge recovery as the next runway
  layer, not as already solved closure.
- Add a concrete canonical constraint-closure witness on the authoritative
  Stage C path and use it as the baseline for the next minimal algebraic
  closure theorem beyond pure status tracking.
- Add a stronger known-limits recovery witness that carries actual propagation
  and effective-geometry witnesses, then target the next scoped theorem at
  stronger local propagation / local-Lorentz follow-through.
- Keep the canonical path on:
  a minimal algebraic-closure theorem for the concrete three-generator system,
  and a scoped known-limits local-recovery theorem for the current local
  Lorentz + propagation slice,
  plus a scoped effective-geometry theorem for that same regime,
  before widening toward richer gauge or GR/QFT claims.
- Land the next two scoped runway theorems in this order:
  a canonical gauge-contract theorem on top of the concrete closure baseline,
  then a canonical spin/local-Lorentz bridge theorem on top of the local
  recovery/effective-geometry baseline.
- Both scoped runway theorems are now on the canonical Stage C path.
  Next widening step:
  move beyond these scoped slices to a less toy gauge theorem or a broader
  known-limits recovery theorem.
- Next widening step:
  add a carrier-parametric gauge/constraint theorem with the current concrete
  carrier as its first instance,
  and add a local causal-effective propagation theorem beyond the current
  local propagation/spin bridge.
- After that:
  add a package-parametric gauge-constraint bridge theorem on the algebra
  side,
  and widen known-limits beyond the current local causal/effective propagation
  regime with a local causal-geometry coherence theorem.
- Keep legacy assumption-backed modules outside the canonical Stage C story.
  Current explicit legacy surfaces:
  `PhysicsClosureInstanceAssumed`,
  generic cone/isotropy compatibility placeholders,
  and prototype wave/unification modules.

## Track E — Observable Consequences / Forward Predictions

Priority bucket: `P0` first, then `P1`

- Package the current shift observables into one typed interface with three
  buckets:
  proved outputs,
  excluded alternatives,
  forward prediction claims.
- Keep the current proved outputs explicit:
  orbit-profile/signature consistency, seam certificates, MDL descent witness,
  exact shell-1/shell-2 profile outputs, and full 4D candidate exclusion.
- Add forward prediction claims separately.
  Current leading candidates:
  profile rigidity across new realizations,
  Fejer-over-χ² monotonicity,
  observable-space collapse,
  snap-threshold transition laws,
  witness-policy robustness,
  cone-split persistence.
- Add a parallel symmetry prototype track:
  finite graded shell series,
  finite signed/Weyl actions on shell states,
  twined fixed-point traces,
  and a wave-facing graded adapter.
- Treat the current finite graded/twined layer as landed infrastructure and
  move the next moonshine-facing work to:
  explicit twiner libraries, richer grading choices, and only then later
  modularity/umbral tests.
- Current immediate moonshine hardening target:
  add explicit twiner libraries for shift and `B₄`, plus a first
  graded/twined comparison report surface.
- Those are now landed.
  Next moonshine hardening target:
  broaden twiner coverage and expose a richer graded/twined comparison
  summary, then strengthen the wave-grading prototype summary.
- Keep that track explicitly pre-moonshine:
  no modularity theorem,
  no umbral identification,
  no Monster trace claim yet.
- [x] Add a validation table for each forward claim:
  source modules,
  confidence level,
  falsifier,
  preferred test harness or dataset.
- Prioritize validation in this order:
  profile rigidity,
  Fejer-over-χ²,
  observable-space collapse,
  snap-threshold laws.
- Observable-space collapse benchmark:
  add a typed harness/report sourced from `RealClosureKitFiber.obsFixed` and
  `obsUnique`, then expose its verdict through the repo-facing validation
  summary.
- Snap-threshold benchmark:
  now includes the shift reference plus secondary and tertiary boundary cases
  from the χ²-boundary library; next step is additional realization coverage.
- [x] Next snap-threshold prerequisite:
  define a severity/snap policy plus witness state for a non-shift realization
  (synthetic placeholder), then add its harness to the benchmark.
- [x] Next snap-threshold task:
  replace the synthetic placeholder harness with a synthetic one-minus harness.
- [x] Next snap-threshold task:
  add a closure-compatible non-shift severity/snap policy for the synthetic
  one-minus harness.
- [x] Next snap-threshold extension:
  add a second non-shift realization harness (Bool inversion).
- [x] Next snap-threshold extension:
  add a Bool inversion-specific snap witness and the B₄ harness.
- Next snap-threshold extension:
  lift the standalone `B₄` harness from shell-only severity to an
  orientation/signature-aware admissible witness surface.
- [x] Build the profile-rigidity harness first.
  Concrete sub-tasks:
  define the benchmark interface,
  add an alternate realization slot,
  emit a typed benchmark report,
  connect the report to the minimum-credible closure adapter.
- [x] The tail-permutation comparison is now the first negative control, not the
  first admissible alternate realization.
- Next validation task after the negative control:
  add one genuinely closure-compatible alternate realization that exposes the
  full orientation/profile/signature surface.
- [x] First canonical admissible alternate realization:
  the synthetic one-minus realization on the 4D Lorentz-family profile path.
- [x] Secondary admissible comparison:
  the 4D Bool inversion realization on the `(3,1)` mask.
- Next mathematically serious alternate realization after the current
  synthetic/bool-inversion pair:
  a Coxeter / Weyl-group realization of the same 4D shell-orbit data.
- First implementation step for that realization:
  add an independent `B₄` / hyperoctahedral shell/profile computation from
  explicit root-shell points and a Weyl-style action.
- Next sub-task after the independent report:
  classify the `B₄` shell neighborhood explicitly and only then decide whether
  orientation/signature promotion is even plausible.
- [x] Add an explicit admissible-realization interface so future comparison
  candidates cannot silently omit orientation/signature data.
- [x] Keep the synthetic one-minus admissible result recorded as `exactMatch`.
- [x] Keep the Bool inversion admissible result recorded as
  `signatureOnlyMatch`.
- [x] Add one aggregate validation/report object that exposes:
  self exact match,
  synthetic one-minus admissible result,
  Bool inversion secondary admissible result,
  tail-permutation negative control.
- [x] Lift that aggregate rigidity report into a closure-facing adapter so the
  minimum-credible Stage C entrypoint exposes both:
  theorem-backed closure data and current validation status.
- [x] Add one repo-facing closure summary surface that re-exports the current
  rigidity suite verdicts directly from the minimum-credible validation
  adapter.
- [x] After the summary surface lands, move the next runnable benchmark to:
  Fejer-over-χ² monotonicity.
- [x] Fejer-over-χ² benchmark sub-tasks:
  define the benchmark report type,
  define an explicit χ² falsifier-status type,
  add a shift reference harness,
  expose the current benchmark verdict from theorem-backed Fejér /
  closest-point / MDL witnesses.
- [x] Upgrade the χ² side from `pending` to an intermediate
  `interfaceWired` status when the snap / `chi2Spike` boundary is present.
- [x] Immediate χ²-side hardening:
  landed via a concrete shift-side χ²-boundary witness from the severity/snap
  layer; next decide whether to promote that witness into a broader falsifier
  theorem or an explicit counterexample library.
- [x] Immediate χ²-side implementation step:
  add a small typed shift-side boundary/counterexample library with more than
  one witness state, then surface it through the validation summary before
  attempting a larger falsifier theorem.
- [x] After that, the next Fejér benchmark target is a standalone formalized χ²
  falsifier theorem or counterexample witness.
- [x] Keep the positive side non-placeholder:
  benchmark facts/reports should carry the actual theorem witnesses instead of
  only boolean flags.
- [x] Add one falsifiability / deviation boundary to the same interface.
  Current minimum:
  mirror-signature exclusion plus failure of competing 4D candidate profiles.
- [x] Promote existing CSV/evidence modules into consumers/providers of the same
  observable package instead of parallel wrappers.

## Shared Integration

- Keep Stage A and Stage B documentation aligned with the new Stage C target:
  minimal credible physics closure.
- Keep the stronger archive-backed reading visible in docs and summaries
  without overstating any of the still-open physics gaps.
- Keep the outreach-facing docs aligned with the same evidence boundary:
  theorem-backed,
  scaffold present,
  physics interpretation still open.
- Ensure docs, TODOs, code, and changelog all distinguish:
  proved,
  evidence-backed,
  predicted.
- Refactor the intrinsic shell/orbit theorem path so theorem-critical records
  do not mention finite realization fields.
- Keep the Coxeter/Weyl scaffold explicitly separated from the admissible
  realization harness until the `B₄` realization exposes justified
  orientation/signature data.
- Add and maintain a repo-facing note for the mathematical framing of the
  orbit-shell result:
  `Docs/OrbitShellProfilesAndLorentzSignature.md`.
- Next `B₄` sub-task after the independent shell/profile report:
  add a typed shell-neighborhood status surface and only revisit admissible
  promotion if the neighborhood is Lorentz-compatible.
- Add a canonical shell-neighborhood classification layer shared by the shift
  reference, `B₄`, and future realizations.
- Add a bounded one-minus shell-family theorem for `m = 2..8`.
- Current theorem task:
  use the landed parametric `m` shell-1 theorem as the baseline one-minus
  classifier for the current shift family.
- Follow-on theorem task:
  decide whether the next theorem step is shell-2 / orientation follow-through
  or a second Lorentz-family realization.
- Immediate realization-search step:
  add an independent shell-side one-minus-family candidate for the 4D Lorentz
  neighborhood, classify it explicitly, and keep it non-admissible until the
  missing shell-2/orientation/signature pieces are justified.
- Current status on that search:
  synthetic one-minus candidate now carries shell-1 and shell-2 profiles,
  orientation/signature are bridged, and a minimal independent-dynamics
  witness is present; it now enters the admissible harness.
- Next realization-search implementation:
  grow the prototype Lorentz-neighborhood dynamic candidate scaffold into a
  genuinely independent dynamics-side realization, then decide whether it can
  move beyond prototype-only status.
- Immediate promotion-side implementation:
  add a typed synthetic-promotion bridge that records the current orientation
  and signature blocker explicitly, and only allow admissible-harness
  promotion when both become independently justified.
- Current promotion-side status:
  synthetic promotion bridge is now admissible-ready on the current path.
- Keep the canonical Stage C entrypoint authoritative in code:
  `DASHI.Physics.Closure.CanonicalStageC` is the recommended import surface,
  while legacy assumed/prototype modules remain compatibility-only.
- Current newest physics-first widening is also landed:
  a stronger extended local recovery theorem beyond the current coherence
  slice,
  plus a stronger algebraic-coherence theorem beyond the current
  package-parametric bridge.
- That next physics-first widening is now landed:
  one stronger recovered-local-regime theorem above the current local
  physics-coherence slice,
  and one stronger algebraic-stability theorem above the current
  algebraic-coherence slice.
- That next physics-first cycle is now landed:
  one stronger recovered-dynamics theorem above the current complete-local
  regime slice,
  one stronger algebraic-consistency theorem above the current
  algebraic-bundle/stability slice,
  one geometry-facing downstream consumer on the canonical ladder,
  and one richer moonshine comparison bundle.
- Current next physics-first cycle is now landed:
  one stronger recovered-wave-geometry theorem above the current
  recovered-wavefront slice,
  one stronger algebraic regime-invariance theorem above the current
  transport-invariance slice,
  one wave-geometry-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave family summary.
- Current newest physics-first cycle is now landed:
  one stronger recovered-wave-regime theorem above the current
  recovered-wave-geometry slice,
  one stronger algebraic regime-persistence theorem above the current
  regime-invariance slice,
  one wave-regime-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave-regime summary.
- Current latest physics-first cycle is now landed:
  one stronger recovered-wave-observables theorem above the current
  recovered-wave-regime slice,
  one stronger algebraic regime-coherence theorem above the current
  regime-persistence slice,
  one wave-observable-facing downstream consumer on the canonical ladder,
  and one richer moonshine twined-wave-observable summary.
- After the full parametric theorem lands, the next milestone is:
  a second Lorentz-family realization search.
- Add a finite orbit-shell generating series layer:
  orientation tag plus shell-1 / shell-2 orbit-size multiplicities.
- Build the shift series witness from theorem-backed current profile data.
- Build the standalone `B₄` series and compare it against the shift series
  without changing admissible-harness semantics.
- Add a concrete prototype wave-series module that lifts the finite shift
  series into a grade-0 wave-facing object while staying outside the
  theorem-critical closure path.
- If the series/wave path keeps looking symmetry-rich, keep the interpretation
  order explicit:
  Weyl/root-system/theta-like first,
  then Niemeier/umbral-style only if a genuine root-lattice shell model
  appears,
  and only then Monster/Moonshine once graded-module or trace-level structure
  exists.
- Current landed closure widening:
  wave-observable-transport-geometry coherence now has theorem surfaces,
  a canonical consumer, and summary exports on the authoritative Stage C
  path.

## Deferred Beyond Minimum

Priority bucket: `P2`

- Full realization-independent generalization beyond the current 4D framework.
- Full GR / QFT recovery.
- Niemeier / umbral-style modular organization, but only after a genuine
  root-lattice shell realization exists.
- Monster / Moonshine or broader symmetry closure, but only after a
  graded-module / trace bridge exists.

## Existing Empirical Gate

### Masked Orthogonal Split (empirical gate: PASS)

Layer: 3D closure embedding (`v_pnorm, v_dnorm, v_arrow`).
Quadratic: `G = diag([-1, 0.2034, -1])` (mask-based).
Projector: `P = G-orthogonal projector onto shape coords [0,1]` (`arrow=coord 2`).
Results (n=156 steps, dim=3):

- `||PᵀG − GP||_F = 0.0`
- `max |⟨PΔs, (I−P)Δs⟩_G| = 2.396e−16`
- `max |Q(Δs) − Q(PΔs) − Q((I−P)Δs)| = 6.661e−16`

Interpretation: Case A achieved in cone layer — exact G-self-adjoint
projection, vanishing cross-term, Pythagorean quadratic split holds to machine
precision.
- Current landed closure widening: wave-observable-transport-geometry regime now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime coherence now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime completeness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime soundness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime consistency now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime invariance now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime robustness now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime resilience now has theorem surfaces, a canonical consumer, and summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime harmony now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime balance now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime symmetry now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime convergence now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime fidelity now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime legibility now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime transparency now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime refinement now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime resolution now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime calibration now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
- Current landed closure widening: wave-observable-transport-geometry regime calibration now has theorem surfaces, a canonical consumer, and moonshine summary exports on the authoritative Stage C path.
Cleanup
- [x] replace stale giant summary exports with ladder-based summary exports
- [x] introduce short-path wrapper modules for closure wave-regime families
- [x] introduce short-path wrapper modules for moonshine wave-regime reports
- [x] add canonical closure and moonshine ladder map modules
- [x] resume `1/2/3/4` widening only after the cleanup compiles cleanly
- Active widening loop:
  next cycle continues with one more algebra rung, one more recovered-local
  rung, one more canonical consumer, and one more pre-moonshine summary on the
  cleaned wave-regime structure.
## Cleanup / Consolidation
- [x] Add a canonical `LocalProgramBundle` for the frozen local ladder.
- [x] Point `Closure/Canonical/Ladder` at grouped ladder surfaces rather than mirroring `CanonicalStageC`.
- [x] Rewire `PhysicsClosureValidationSummary` to grouped wave-regime imports only.
- [x] Rewire remaining canonical modules away from direct per-rung wave-regime imports.
- [x] Add the `Traceability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Auditability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Reliability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Verifiability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Repeatability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Reproducibility` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Portability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Interoperability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Composability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Maintainability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Extensibility` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Scalability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Durability` rung across algebra, recovery, consumer, and moonshine grouped summary surfaces.
- [x] Add the `Usability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Add the `Operability` rung across algebra, recovery, consumer, and moonshine summary surfaces.
- [x] Split `Compatibility` / `Composability` aliases on the canonical Stage C import surface so grouped ladder compiles stop depending on import-order collisions.
 - Landed `Sustainability` rung across algebra, recovery, consumer, and moonshine grouped wave-regime ladders.
- 2026-03-11: landed `Stewardship` rung across algebra/recovery/consumer/moonshine grouped wave-regime surfaces.

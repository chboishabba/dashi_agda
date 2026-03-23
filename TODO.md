# TODO

## Track N — Merge-Prep Nix / Zkperf Surface (2026-03-23)

Priority bucket: `P1`

- [x] Add a local `flake.nix` that mirrors the existing authoritative GitHub
  typecheck route through `DASHI/Everything.agda`.
- [x] Add a second Nix smoke-check surface for merge-relevant standalone roots
  plus recursive `Kernel/`, `Monster/`, and `Verification/` modules.
- [x] Add a local `dashi-agda.agda-lib` so Nix/dev-shell tooling has an
  explicit library surface to point at.
- [x] Make local `agda-record-all` recurse over the same merge-prep target
  surface instead of top-level files only.
- [x] Keep demo DA51/zkperf JSONL artifacts, if merged, documented as sample
  witness outputs rather than canonical reproducibility fixtures.
- [x] Generate and keep a local `flake.lock` for the merge-prep Nix surface.
- [ ] Follow-up after the writable-source fix:
  rerun `nix flake check`, `nix build .#check`, and
  `nix build .#merge-smoke` end to end and record the final outcome.

## Track U — Physics Closure Spine Completion (2026-03-12)

Priority bucket: `P0`

- [ ] Execute checklist in `Docs/PhysicsClosureImplementationChecklist.md` in
  strict order.
- [ ] Keep contraction→quadratic uniqueness transport centralized in
  `ContractionForcesQuadraticStrong`.
- [ ] Keep profile forcing surface narrow:
  `ConeArrowIsotropyForcesProfile` + shift instance only.
- [ ] Upgrade `DecimationToClifford` from interface shell to theorem-bearing
  factorization surface.
- [ ] Convert `PhysicsClosureFull` from supplied-field record to
  theorem-derived assembly where possible.
- [ ] Eliminate assumption-first canonical seams from
  `PhysicsClosureInstanceAssumed` and canonical constraint-closure route.
- [ ] Enforce canonical export path in:
  `CanonicalStageC`, `AxiomSet` (`AxiomLaws`), and `Everything`.

## Cleanup / Consolidation

- Runtime policy:
  do not run `PhysicsClosureValidationSummary.agda` in routine validation until
  runtime bounds are acceptable (currently ~1.25 hours).
- [x] Closure hygiene policy:
  `scripts/run_closure_hygiene.py` and
  `scripts/run_closure_hygiene.sh` now skip learned `heavy` and
  `aggregator` tasks by default, with an explicit `--include-heavy` flag for
  aggregate integration runs.
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
  `PhysicsClosureValidationSummary.agda` timing/validation when a longer
  runtime budget is available.
- [x] Pipeline enforcement: tag existing closure-relevant modules in docs as
  `canonical` / `supporting` / `experimental` and remove ambiguous duplicates
  from repo-facing claims.
- [ ] Keep `Docs/ClosurePipeline.md` label registry current whenever new
  closure modules are added or promoted.
- [x] Add canonical quadratic-to-Clifford bridge theorem module:
  `DASHI/Physics/Closure/QuadraticToCliffordBridgeTheorem.agda`, deriving a
  canonical bilinear form from normalized quadratic output
  (`ContractionForcesQuadraticStrong.uniqueUpToScaleWitness`) and exposing a
  universal-property seam on the theorem surface.
- [x] Wire canonical contraction-to-Clifford bridge exports to include the new
  quadratic-to-Clifford theorem surface in
  `CanonicalContractionToCliffordBridgeTheorem`.

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

- [x] Replace the raw `Set` seam in `ContractionForcesQuadraticStrong` with a
  named uniqueness/compatibility seam record.
- [x] Replace the placeholder-style pending field in
  `ContractionQuadraticToSignatureBridgeTheorem` with a named bridge seam
  record that makes the remaining quadratic/signature compatibility gap
  explicit.
- [x] Add canonical split/parallelogram bridge module:
  `DASHI/Geometry/ProjectionDefectSplitForcesParallelogram.agda`, and route
  contraction→quadratic theorem surfaces through it.
- [x] Replace passthrough fields in
  `quadraticEmergenceFromProjectionDefectSplit`
  (`Additive-On-Orth`, `PD-splits`) with direct derivations from the
  no-leakage/orthogonality + energy-split theorem pipeline.
- [x] Complete the quadratic-to-signature classification internals using the
  normalized quadratic from
  `ContractionForcesQuadraticStrong.uniqueUpToScaleWitness`, with theorem
  source rooted in causal/symmetry data instead of profile-only forcing.
- [x] Land explicit Lemma A in the canonical signature route:
  eliminate Euclidean/degenerate competitors via cone/arrow compatibility.
- [x] Land explicit Lemma B in the canonical signature route:
  spatial isotropy + one arrow direction + finite speed force `(3,1)`.
- [x] Keep orbit-profile equality as a secondary witness and negative-control
  eliminator on the signature route, not the primary theorem engine.
- [x] Add a theorem-level Lorentz lock package that separates:
  `(3,1)` witness,
  uniqueness of admissible signature,
  and non-admissibility of rival signatures (`sig13`, `other`,
  plus explicit rival tags `sig40`, `sig22`, `sig04`).
- [x] Strengthen `QuadraticToCliffordBridgeTheorem` from a raw
  presentation-level seam to an explicit factorization interface carrying:
  target carrier, factor map, and generator-compatibility law.
- [x] Complete canonical `Quadratic⇒Clifford` theorem surface as the exclusive
  upstream for `WaveLift⇒Even`.
- [x] Add canonical Clifford grading + even-subalgebra interfaces on
  `DASHI.Physics.CliffordEvenLiftBridge`.
- [x] Define canonical wave lift on the same closure state/carrier pipeline and
  ensure its image is built from even words.
- [x] Prove `WaveLift⇒Even` as factorization through `EvenSubalgebra.incl`
  (witness form), not only a loose parity predicate.
- [x] Thread the completed `WaveLift⇒Even` theorem into canonical bridge
  bundles (`CanonicalContractionToCliffordBridgeTheorem`,
  `KnownLimitsQFTBridgeTheorem`) without adding a parallel wave algebra.

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
- Keep anomaly-report wording strict:
  if Monster-labeled samples do not separate from controls under the current
  embedding, report that result as non-separation with at most a non-unique
  rigid substructure, not as a Monster fingerprint.
- Next moonshine-adjacent validation task:
  require baseline/control comparison tables for any rigid-slot or anomaly
  summary before promoting it into repo-facing docs.
- Next JMD-side anomaly test:
  build a matched Monster-vs-control regime table using
  `eigenspace`, `bott`, `Hecke`, `orbifold`, `DA51`, `j-fixed`,
  proof depth/reach/import counts, and trivector coordinates.
- Script scaffold status:
  `scripts/regime_test.py` is now the canonical local harness for these
  CSV-driven JMD regime occupancy/divergence checks.
- Run regime occupancy/divergence checks before any further Monster-language
  interpretation:
  Fisher/chi-square for categorical occupancy,
  Jensen-Shannon or related divergence on single and joint regime tuples,
  then small-sample leave-one-out classification if signal appears.
- Next DASHI-side anomaly test:
  build a delta-regime/source-vs-trace harness using `Δx`,
  cone compatibility, contraction/Fejér behavior, and transition frequencies
  rather than raw global vector similarity.
- Script scaffold status:
  use the `transitions` mode of `scripts/regime_test.py` once stepwise
  source/trace or regime-transition rows are available.
- Current cone-test scaffold status:
  use the `cone` mode of `scripts/regime_test.py` when stepwise trace rows are
  available with `mass`, `cycles`, `instr`, and related structural columns.
- Existing sibling-repo shortcut:
  the `dashifine-closure-embedding` preset now reads
  `../dashifine/.../closure_embedding_per_step.csv` directly without a manual
  reshape step.
- Current empirical reading from that shortcut:
  the structural cone itself is not the blocker on the checked trace family;
  the next DASHI-side refinement should focus on arrow canonicalization or
  guard tuning around the localized `phistar_50_76` `v_arrow` failures.
- Immediate diagnostics follow-up:
  extend `scripts/regime_test.py cone` with ultrametric/ternary violation
  reporting so those localized failures are grouped by structural signature,
  bucket radius, and nearest admissible-pattern distance.
- Current outcome:
  the localized `phistar_50_76` failures remain on an admissible structural
  ternary signature with zero nearest-signature distance, so the next
  refinement should target arrow guard semantics rather than structural cone
  relearning.
- Current bracket from the new arrow sweep:
  the remaining `phistar_50_76` arrow-only boundary cases clear progressively
  across tolerances near `4e-5`, `8e-4`, `8e-3`, and `8e-2`.
- Next decision:
  choose whether the repo wants
  1. a single canonical arrow tolerance,
  2. a boundary/interior split with explicit exception class,
  or 3. an arrow canonicalization step upstream of the guard.
- Active choice:
  implement option `2` first, so the current arrow-only cases become an
  explicit boundary class in the local diagnostics and any exported witness
  tables.
- Current result:
  that split is now implemented and the observed `dashifine` trace has only
  `arrow_boundary` exceptions.
  The next design choice is whether those four steps should remain explicit
  boundary witnesses or be absorbed by a canonical nonzero arrow tolerance.
- Current implementation status:
  the arrow-guard sweep is now landed, along with named arrow profiles:
  `strict`, `boundary`, and `lenient`.
  The local `dashifine` run currently resolves those as
  `56/4`, `59/1`, and `60/0` for `interior/arrow_boundary`.
- Stable local artifact status:
  `scripts/regime_test.py cone` can now write the current boundary witnesses to
  `artifacts/regime_test/arrow_boundary_latest.csv`.
- Current JMD-builder status:
  `scripts/build_jmd_regime_table.py` now emits a seeded
  `artifacts/regime_test/jmd_regime_table.csv` from the Agda tree and
  currently finds `844` rows total with `7` Monster rows and `6` matched
  control rows.
- Current seeded occupancy read:
  `eigenspace JS=0.5569`,
  `bott JS=0.0608`,
  `joint(eigenspace,bott,hecke) JS=0.6176`,
  and the leave-one-out classification now runs only on the matched `M/O`
  subset instead of leaking unlabeled `U` rows.
- New source-lattice anchor:
  treat the sibling repo `../kant-zk-pastebin` as the current explicit DASL
  source model for the bridge.
  The authoritative source grammar for this pass lives in
  `src/dasl.rs`, `src/sheaf.rs`, and `src/ipfs.rs` there.
- Cross-check on alternate sibling repo:
  `../dashi_lean4` is now confirmed not to fill the current JMD-side gap.
  It carries Lean-side DA51/moonshine/schema witnesses, but not the missing
  class/projection layer for `Basin` / `Eigen`:
  no DASL address grammar, no explicit `EigenSpace`, and no Bott/Hecke/
  orbifold class table for the HEPData family projection problem.
- Immediate source-integration task:
  extend `scripts/regime_test.py cone` with a parser/loader for that sibling
  repo so the execution export gains:
  a source-backed DASL eigen prior,
  a first-pass `basin_ok` grounded in source support/projection,
  and a stable JSON artifact for the parsed source model.
- Current source-integration result:
  that loader is now landed.
  On the checked `dashifine` trace family it preserves the existing
  structural/arrow split but adds a first source-backed mismatch:
  `48/60` steps are source-supported and `12/60` steps
  (all from `pTll_76_106`) currently miss support because the trace heuristic
  assigns `Hub` while the parsed DASL encoding prior is `Earth/Spoke`-only.
- Current witness status:
  `mdl_tail_boundary` is now promoted into the Agda family-classification
  witness and threaded through `PhysicsClosureCoreWitness`; the next decision
  is whether to keep that family witness as a parallel exported surface or
  integrate it into broader theorem/checklist modules.
- Current claim boundary for that task:
  do not upgrade this into a full class-projection theorem or a proof that
  `p47` is preserved automatically.
  The first pass should report explicit source support/projection metrics while
  keeping stronger gauge-compatibility claims deferred.
- Artifact semantics note:
  keep `source_support_ok` as the explicit runtime/export name for this current
  predicate.
  Treat `basin_ok` only as the bridge-facing compatibility alias until a richer
  source projector or class table is in place.
- Current execution-admissibility bridge status:
  `scripts/regime_test.py cone` can now export
  `execution_admissibility_latest.json`,
  `eigen_overlap_latest.csv`,
  and a concrete Agda witness module for the strict-profile checked trace.
- Immediate next JMD task:
  replace the current seed/graph-proxy regime values with stronger semantic
  metadata for the matched subset, especially for `Hecke`, `DA51`,
  `orbifold`, and `j-fixed`, before treating the JMD table as anything more
  than a local comparison scaffold.
- Immediate next DASHI-side task:
  decide whether the current `ArrowBoundary` cases remain the canonical witness
  class or whether an upstream arrow normalization step should absorb them
  while keeping the structural cone fixed.
- Immediate next source-bridge task:
  refine the current DASL-backed projector so `basin_ok` is not only a
  support-on-dominant-eigenspace check.
  In particular, decide whether `pTll_76_106` is:
  1. a real source mismatch,
  2. a trace-side `Hub` heuristic artifact,
  or 3. evidence that the parsed DASL source grammar needs a richer class table
  than the current encoding prior.
- Immediate sub-step:
  replace the current trace-side `Hub` heuristic first and rerun only the five
  current trace families with side-by-side legacy vs refined eigenspace labels.
  If `pTll_76_106` stops landing in `Hub`, treat the current unsupported block
  as a labeler artifact rather than a source miss.
- Current result:
  that classifier refinement is now landed and the current checked five-trace
  family does exactly that.
  `legacy_vs_refined_trace_agreement=4/5`;
  `pTll_76_106` moves from legacy `Hub` to refined `Spoke`;
  and the current strict-profile source-support proxy now clears all
  `60/60` steps.
- Immediate next source-side task:
  because the checked mismatch evaporated under the better labeler, the next
  worthwhile source-bridge step is no longer mismatch triage.
  It is enriching the DASL loader beyond the encoding prior so future source
  predicates can move from eigenspace support toward richer class-level
  projection.
- Immediate implementation target:
  promote the parsed DASL source prior from the small encoding subset to the
  full Monster-prime catalog already present in `../kant-zk-pastebin`.
  The next bridge rerun should therefore use a source model that explicitly
  includes all `15` Monster primes and their
  `Earth/Spoke/Hub/Clock` partition, not just the encoding-level map.
- Current result:
  that loader upgrade is now landed.
  The default DASL source mode is now `monster-primes`, the exported source
  catalog contains all `15` Monster primes, and the current eigenspace
  distribution is
  `Earth=0.4667`, `Spoke=0.4`, `Hub=0.0667`, `Clock=0.0667`.
  The checked `dashifine` trace remains stable under that richer source model:
  `56 Interior`, `4 ArrowBoundary`, `60/60 source_support_ok`.
- Immediate next source-side task:
  use the richer `monster-primes` source catalog to move beyond support-only
  checks and toward an explicit nearest-class or nearest-prime projection
  surface, rather than only dominant-eigenspace support.
- Current result:
  that explicit projection surface is now landed as a canonical
  class-to-prime proxy.
  On the checked five-trace family, Earth-family traces currently project to
  `p2 / T_2 / exponent 46`, while the refined `Spoke` family `pTll_76_106`
  projects to `p17 / T_17 / exponent 1`.
- Current claim boundary:
  this is a canonical source-projection proxy, not yet a geometric
  nearest-neighbor or full class-level projection theorem.
- Immediate next source-side task:
  add a less coarse distance or ranking on top of the current projection proxy,
  so source projection can be compared by more than eigenspace class and
  exponent ordering alone.
- Immediate implementation target:
  add a scored source-prime ranking surface over the current source catalog and
  export the top candidates in the runtime artifacts.
  Keep the claim boundary explicit:
  that scored ranking surface is now landed.
  Current result:
  an explicit primary source-projection mode is now landed so the repo can keep the
  conservative canonical projection as default while also supporting a
  scored-primary projection for experimental runs without rewriting the
  bridge-facing canonical fields.
  this should still be a controlled ranking heuristic, not a geometric
  nearest-neighbor theorem.
- Current result:
  that scored ranking surface is now landed.
  On the checked traces, Earth-family rows still rank `p2` first.
  The refined `Spoke` family `pTll_76_106` now shows the first interesting
  ranked split:
  canonical proxy = `p17`,
  scored shortlist = `p59`, `p71`, then `p17`.
- Current implementation target:
  keep the canonical projection rule unchanged, but export an explicit
  `projection_conflict` marker for rows where the canonical and
  primary-selected source representatives diverge.
- Current implementation target:
  keep the shortlist diagnostic even when scored ranking is enabled, and anchor
  the score to canonical consistency so conflicts mean more than attack-triple
  bonus alone.
- Current implementation target:
  export score-component breakdowns for the ranked and primary source
  projections so the next source-side passes can tune the metric explicitly.
- Current implementation target:
  add richer within-class terms from source-side metadata, especially `Hecke`
  proximity and a weak `Bott` cycle prior, then rerun the bridge on a larger
  set of compatible `dashifine` trace files rather than only the original
  five-family set.
- Current result:
  the richer score is landed and a three-batch `dashifine` summary is now
  recorded at `artifacts/regime_test/dashifine_trace_batch_latest.json`.
  Across `out`, `out_new`, and `out_all`, source support stays fully intact and
  the refined `Spoke` family remains canonically `p17`.
  The next local execution-side target is narrower:
  inspect the additional arrow-boundary families that appear in the larger
  batches, especially `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas`.
- Current result:
  that family-level inspection surface is now landed.
  `scripts/regime_test.py cone` now emits per-family arrow-boundary summaries,
  and the current larger-batch read is:
  `phistar_50_76` = small arrow-only tolerance ladder,
  `z_pt_7tev_atlas` = single moderate arrow break,
  `ttbar_mtt_8tev_cms` = strongest current outlier because it couples large
  arrow violations with `v_dnorm` failures.
- Current result:
  focused family drilldowns are now exportable.
  The current `ttbar_mtt_8tev_cms` onset is late and mixed-axis:
  first boundary at `t=10->11`,
  arrow sign flip = yes,
  immediate failure mode = `v_arrow` + `v_dnorm`,
  immediate signature change = no.
- Current terminal-step autopsy result:
  alternate `v_dnorm` constructions
  (`raw`, `log_abs`, `robust_z`, `winsor95`, `family_minmax`)
  still leave both terminal `ttbar_mtt_8tev_cms` `v_dnorm` deltas positive.
  Those reversals are numerically tiny (`~9.4e-13`, `~1.6e-13`), so the next
  check should map the failing steps to the underlying tail-bin physics or
  normalization pipeline rather than changing the cone geometry.
- Current raw-context read:
  the same focused export now shows `ttbar_mtt_8tev_cms` is a `7`-bin spectrum
  whose last bin (`x≈1350`) has the largest fractional uncertainty
  (`~8.19%`), and the first boundary onset lands at the late
  `alpha=1e4 -> 1e5` jump.
- Current stronger-witness read:
  despite that late mixed-axis boundary, the same family still has
  `closestpoint_frac=1.0` and `fejer_set_frac=1.0` in the local `dashifine`
  reports, while the explicit exception is on the MDL-exact descent surface
  (`MDL_monotone=False`, `2` violations, worst increase `0.694577`).
- Current classification result:
  the local family-summary surface now promotes `ttbar_mtt_8tev_cms` to the
  narrower `mdl_tail_boundary` class, instead of leaving it in the generic
  `mixed_hard_axis_outlier` bucket.
- Current lemma/count status:
  `TailBoundaryLemma.agda` now encodes the modest current-witness claim that
  an `MDLTailBoundaryFamily` can remain cone / Fejér / closest-point
  admissible while failing only at the MDL-exact layer.
  The current larger-trace count artifact reports `1/9` such families, and
  that one current case is both tail-localized and terminal-boundary.
- Current widened batch count:
  `scripts/tail_boundary_batch.py` now aggregates the currently compatible
  `dashifine` batches into `artifacts/regime_test/tail_boundary_batch_latest.json`.
  On the current three-batch set it reports `2` `mdl_tail_boundary` instances
  across `3` datasets, but still only one unique family:
  `ttbar_mtt_8tev_cms`.
  The same aggregate also now separates repeated controls cleanly:
  repeated `pTll` families plus `dijet_chi_7tev_cms` and `hgg_pt_8tev_atlas`
  stay interior, while `phistar_50_76` and `z_pt_7tev_atlas` repeat only in
  non-MDL boundary classes.
- Current compatible-dataset inventory:
  the same aggregate now records that there are only `3` compatible
  `closure_embedding_per_step.csv` batches currently available in
  `dashifine`.
  Among the `7` current tail-candidate families, only
  `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` leave the interior.
- Immediate next execution-side task:
  widen that aggregate beyond the currently compatible `dashifine` trio where
  possible, but within the current inventory the next-priority tail candidates
  are now explicit:
  `z_pt_7tev_atlas`, then the still-unresolved interior heavy-spectrum
  candidates `atlas_4l_pt4l_8tev`,
  `dijet_chi_13tev_cms_mgt6`, `dijet_chi_7tev_cms`, and
  `hgg_pt_8tev_atlas`.
- Current `z_pt` refinement:
  the focused `z_pt_7tev_atlas` drilldown confirms it is still a
  `single_arrow_break`, not a second `mdl_tail_boundary`.
  Present read:
  one late tail-localized boundary step at `t=9->10`,
  `arrow_delta≈0.0305551`,
  no non-arrow failure,
  all tested `v_dnorm` variants remain nonincreasing,
  and the family clears under the `lenient` arrow profile.
- Current first interior heavy-spectrum check:
  `atlas_4l_m4l_8tev` has now been drilled directly and stays fully interior:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the max-fractional-uncertainty tail bin.
- Current second interior heavy-spectrum check:
  `atlas_4l_pt4l_8tev` has now been drilled directly and also stays fully
  interior:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the max-fractional-uncertainty tail bin.
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
- 2026-03-11: landed `Accountability` rung across algebra/recovery/consumer/moonshine grouped wave-regime surfaces.

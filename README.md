## Repository Status

Archive-backed status update:

- The orbit/signature/shell-family story remains the strongest part of the
  repo and is now better supported by sibling-repo and archive material.
- The wave / psi / graded-series bridge is no longer only aspirational:
  archive material and sibling-repo scaffolding now make it a strong formal
  direction, though still not a closure theorem.
- The five-pillar closure interface exists, but currently acts as a packaging
  surface over earlier modules, not yet as the final bottleneck proof.
- Current mathematical bottleneck remains:
  prove the invariant quadratic + uniqueness-up-to-scale seams from the
  contraction/projection machinery and then derive the downstream
  signature/Clifford/gauge chain from that theorem.
- Local merge-prep tooling status:
  the repo now treats a Nix/zkperf surface as acceptable only if it preserves
  the existing authoritative CI route through `DASHI/Everything.agda` and also
  adds an explicit recursive smoke surface for merge-relevant nested modules.
  Demo DA51/zkperf JSONL witness files are acceptable as illustrative tracked
  artifacts for now, but they must be documented as non-authoritative sample
  outputs rather than as canonical reproducibility inputs.
- Routine Agda target policy now lives in `Docs/AgdaValidationTargets.md`:
  use focused canonical bridge modules in normal edit loops, treat
  `PhysicsClosureValidationSummary.agda` as heavy/avoid-by-default, and treat
  `Everything.agda` as an occasional bounded checkpoint rather than a routine
  inner-loop command.
- Representation-language clarification:
  `Docs/ColourInDashi.md` now fixes the repo-facing split between optical
  colour, perceptual colour, and QCD colour, and states the safe Dashi claim
  boundary: colour is a projection-stable observable on a structured latent
  signal, not a primitive property.
- Internal-symmetry clarification:
  `Docs/TriadicCarrierToSU3.md` now fixes the safe bridge from a triadic
  3-sector carrier to an `SU(3)`-like internal symmetry claim. Ternary
  counting alone is not enough; the lift requires conserved Hermitian norm,
  determinant-one admissible mixing, and an observable quotient.
- MDL toy clarification:
  `Docs/MusicalSymmetryMDL.md` now states the stronger basin target explicitly:
  replace direct symmetry reward with a compression/MDL proxy and ask whether
  symmetric attractor classes still dominate.
- Canonical closure routing now includes an explicit
  `ContractionForcesQuadraticStrong -> QuadraticToCliffordBridgeTheorem`
  step that builds a canonical bilinear-form interface from normalized
  quadratic data before spin/Dirac layers.
- Active closure seam tightening:
  keep the canonical bridge interface fixed while replacing the internal
  signature source with a causal-classification theorem on the normalized
  quadratic (`Q̂core`) under cone/arrow/isotropy/finite-speed/nondegeneracy
  assumptions.
- Archive coverage update:
  `Docs/PhysicsArchiveCoverageMap.md` now records the current high-signal
  local-DB support threads for the physics-closure spine. The current repo
  reading is:
  `Physics Closure in DASHI`,
  `Branch · Cone monotonicity analysis`,
  and `Branch · Snap Filtering Analysis`
  are direct formal support lanes, while
  `Branch · Topology and MDA/MDL`
  and the light-transport / phase-sync thread remain support lanes for
  continuum and physical-realization work.
- Photonuclear empirical lane visibility:
  `DASHI/Physics/Closure/PhotonuclearEmpiricalConstantsRegistry.agda`,
  `DASHI/Physics/Closure/PhotonuclearEmpiricalMeasurementSurface.agda`,
  `DASHI/Physics/Closure/PhotonuclearEmpiricalEvidenceSummary.agda`, and
  `DASHI/Physics/Closure/PhotonuclearEmpiricalValidationSummary.agda` now
  provide the empirical-first owner stack, with
  `Docs/PhotonuclearEmpiricalRegistry.md` as the canonical map. This lane is
  explicitly empirical-only and non-claiming.
- Sibling-repo support surfaces:
  `../dashitest` contains useful diagnostic and measurement artifacts for
  wave/interference, MDL, and regime-style language, but it is currently a
  support repo rather than a code dependency for this tree. The strongest
  cross-reference points are
  `../dashitest/dashiCORE/README.md`,
  `../dashitest/dashiCORE/docs/dashibrain_core_integration.md`,
  `../dashitest/dashifine/newtest/grayscott_krr.py`,
  `../dashitest/dashifine/newtest/triality_stack.py`,
  `../dashitest/docs/tree_diffusion_benchmark.md`,
  `../dashitest/docs/phase3_quotient_learning.md`,
  `../dashitest/docs/bad_day.md`,
  `../dashitest/trading/scripts/plot_action_entropy.py`, and
  `../dashitest/trading/scripts/plot_hysteresis_phase.py`.
  These are useful documentation-side analogues for measurement and
  interference language, not theorem evidence for the Agda closure stack.

Current theorem status:

- Stage A is complete: the orbit-profile discriminant selects Lorentz signature
  `(3,1)` in the current 4D framework.
- Arithmetic lane now records canonicalization progress: `normalizeAdd` is
  nonexpansive and lands in a canonical state, `CanonicalResidueZero`
  collapses the residue budget there, and `CancellationPressureFromCanonical`
  bounds the carry-budget pressure by the support proxy so normalized
  states satisfy the current arithmetic pressure guarantee.
- Stage B is complete for the current finite 4D realization: the
  cone/arrow/isotropy stack now drives shell enumeration through abstract
  interfaces rather than a shift-specific proof source.
- Stage C is still open: the current target is **minimal credible physics
  closure**, meaning a theorem-backed dynamics package plus an
  observable-consequence package for the same 4D framework. That package must
  distinguish what is already proved from what is only a forward prediction
  claim. The next concrete benchmark is profile rigidity across new 4D
  realizations.
- Current archive-backed Stage C priority order:
  1. derived dynamics law;
  2. realization-independent projection/delta theorem;
  3. signature forcing / execution-delta interface;
  4. continuum scaling law;
  5. physical reality bridge from wavefield / phase synchronization.
- Current `Δ -> quadratic` status is intentionally split into two lanes:
  the concrete cancellation-energy transport in
  `DASHI/Physics/Closure/DeltaToQuadraticBridgeTheorem.agda`
  now packages its witness surface repo-natively as
  `CancellationPressureCompatibility theorem dim≡15`,
  with
  `canonicalCancellationPressureCompatibility`
  as the thin concrete constructor from the current pair-pressure witness;
  that lane is still treated repo-side as an external compatibility input
  rather than an in-repo derivation from the current tracked-profile
  transport,
  and the sole remaining cancellation-side seam in that module is the
  `pressurePreserved` witness inside
  `CancellationPressureCompatibility`; the sharper forward proposal is
  a weighted valuation measurement
  layer
  `Φ(x) = (v_p(x) * sqrt(log p))_p`
  with
  `Q₊(x) = Σ_p v_p(x)^2 log p`
  as a positive diagonal surface that should feed, rather than replace,
  the existing canonical quadratic/signature stack.
  The first constructive helper surface for that lane now lives in
  `DASHI/Arithmetic/WeightedValuationEnergy.agda`.
  The bridge module now also exposes
  `WeightedValuationTransportCompatibility`
  plus
  `WeightedValuationForwardCandidate`
  so the weighted lane has a record-level admissibility/coherence package
  without identifying that lane with `Q̂core`.
  The weaker profile-side seam now also has its own arithmetic owner:
  `DASHI/Arithmetic/ArithmeticPrimeProfileBridge.agda`
  exposes
  `EmbeddedPrimeProfileMeasurement`,
  while
  `DASHI/Physics/Closure/DeltaToQuadraticBridgeTheorem.agda`
  carries
  `EmbeddedProfileScoreCompatibility`
  only as the explicit
  `deltaSum -> embeddedProfileScore`
  compatibility lane.
  The same module now also exposes
  `DeltaQuadraticSignatureCliffordPackage`
  so an already-packaged delta bridge can carry its normalized quadratic,
  inherited signature-31 data,
  and a specialized Clifford presentation handle
  without widening the cancellation-side claim.
- The three-body test case is now scaffolded repo-side as a theorem-thin
  regime-classification surface under `DASHI/Physics/ThreeBody/`.
  The intended reading is:
  state carrier + step operator + local energy/action +
  contractive/boundary/non-contracting regime split +
  wave-facing admissible path kernel.
  It does not claim a closed-form solution or a global contraction theorem.
  The next landed layer now also separates
  local state/regime improvement
  from
  global forecast depth:
  `Delta3Body`,
  `EnergyΔ3`,
  `Action3`,
  `LocalPredictiveHorizon`,
  and `ChaosBoundary`
  live in the same namespace so the three-body lane can express
  \"better local prediction over time\" without claiming unlimited
  long-horizon predictability in chaotic regions.
  `DASHI/Physics/ThreeBody/Bridge.agda`
  is now also explicitly anchored to the same basin-facing admissibility
  surface already carried by
  `DASHI/Physics/ThreeBody/PredictiveBoundary.agda`,
  rather than introducing a second bridge-local admissibility notion.
  `DASHI/Physics/ThreeBody/TheoremSurface.agda`
  now publicly re-exports that bridge surface alongside the theorem-thin
  predictability and branching surfaces, so downstream consumers can import
  one entrypoint and still reach the basin-anchored bridge package.
  The same namespace now also carries an interference/path-family layer:
  admissible paths aggregate into regime amplitudes, regime weights, regime
  distributions, and a boundary-generated branching surface.
  This lets the repo state the intended Dashi reading of chaos more sharply:
  point prediction degrades, but structured future branch weights can still
  be modeled as action-weighted interference over regimes.

## Visual Guides

The repo now carries a small figure set for the newer three-body and zeta
analysis lanes.

Figure provenance:

- the stable repo copies live under `Docs/Images/three-body/` and
  `Docs/Images/zeta/`;
- they were imported from the delivered external artifact drop in
  `temp-DOWNLOADED/`;
- the associated external Agda sketch is
  `temp-DOWNLOADED/ThreeBodyPredictability.agda`;
- the current repo-native formalism surfaces remain the authoritative source
  for names and claim boundaries.

### Three-body predictability view

![Illustrative three-body trajectory in a projected admissibility cone](Docs/Images/three-body/threebody_projected_admissibility_cone.png)

What this figure is for:

- It visualizes the current three-body lane as a projected
  admissibility/cone picture rather than as a closed-form trajectory solver.
- The lower-left interior region is the intended analogue of a more stable,
  more locally coherent regime.
- The orange boundary curve marks the transition surface where predictive
  horizon is expected to shrink and branching becomes more relevant.
- The upper/right region is the intended non-contracting or unstable side,
  where point prediction degrades and branch-structured forecasts matter more.

Relevant formalism sources:

- [`DASHI/Physics/ThreeBody/PredictiveBoundary.agda`](DASHI/Physics/ThreeBody/PredictiveBoundary.agda)
- [`DASHI/Physics/ThreeBody/Interference.agda`](DASHI/Physics/ThreeBody/Interference.agda)
- [`DASHI/Physics/ThreeBody/BundleIntensity.agda`](DASHI/Physics/ThreeBody/BundleIntensity.agda)
- [`DASHI/Physics/ThreeBody/PredictabilityTheorem.agda`](DASHI/Physics/ThreeBody/PredictabilityTheorem.agda)
- [`temp-DOWNLOADED/ThreeBodyPredictability.agda`](temp-DOWNLOADED/ThreeBodyPredictability.agda)

Interpretation boundary:

- This is an illustrative regime map.
- It is not a proved cone theorem for Newtonian three-body dynamics.
- It is useful because it matches the current theorem-thin repo split:
  cone interior, cone boundary, local contraction, local Lyapunov surfaces,
  basin-relative predictive horizon, and boundary-generated branching.

### Goldbach formal-object lane

The refreshed `Dashi on Quantum Computing` thread landed the Goldbach lane as
analysis-side formal objects rather than as a solved number-theory claim.

Relevant formalism sources:

- [`DASHI/Analysis/GoldbachFormalObjects.agda`](DASHI/Analysis/GoldbachFormalObjects.agda)
- [`CHANGELOG.md`](CHANGELOG.md)
- [`TODO.md`](TODO.md)

What this lane is for:

- It records the program surfaces `EnergyΔ`, `GoldbachCone`,
  `GoldbachAmplitude`, `GoldbachTheoremLadder`, and `GoldbachProgramPack`.
- It now also carries concrete sample-side witnesses rather than only abstract
  constructors:
  `sampleGoldbachExistenceWitness` for `2 + 2 = 4` and
  `sampleGoldbachExistenceWitness8` for `3 + 5 = 8`.
- It keeps the intended reading explicit: Goldbach is being formalized as a
  theorem-thin analysis/program lane, not claimed as a proof of strong
  Goldbach.
- It also keeps the zeta/Riemann connection in the same analysis-only
  boundary class: useful as a program direction, but not a proof of RH.

Interpretation boundary:

- This is a formal-object lane, not a solved Goldbach theorem.
- It does not claim a proof of strong Goldbach.
- It does not claim a proof of the Riemann hypothesis.
- It is intended to make the Goldbach program surface explicit while keeping
  closure claims out of the README.

### Zeta visualization pack

#### Critical-line magnitude

![Critical line magnitude plot for log absolute zeta](Docs/Images/zeta/zeta_logabs_critical_line.png)

Reading:

- The deep troughs are zero neighborhoods for `ζ(1/2 + it)`.
- This is the cleanest first visualization of where critical-line structure
  is concentrated.

Relevant formalism sources:

- [`DASHI/Analysis/AbelZeta.agda`](DASHI/Analysis/AbelZeta.agda)
- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- This is a visualization surface, not an RH proof surface.
- In repo terms it belongs to `Analysis`, not `Physics`.
- The current repo-native observation family now includes:
  `ZetaBoundaryContrastView` and `ZetaEtaTransferView`,
  both derived only from the Abel-summed sample surface.

#### Argument flow near the critical line

![Argument flow of zeta near the critical line](Docs/Images/zeta/zeta_argument_flow_strip.png)

Reading:

- The sharp seam near `σ = 1/2` is the main feature.
- This is the closest direct visual analogue to a phase-flow or boundary-crossing
  picture in the current Dashi language.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- The current repo only packages a visualization scaffold here.
- No analytic continuation, zero-density theorem, or spectral closure claim is
  encoded by this image alone.

#### Consecutive zero spacings

![Spacing of consecutive nontrivial zeta zeros](Docs/Images/zeta/zeta_zero_spacings.png)

Reading:

- The spacing sequence is irregular but visibly structured.
- This is the simplest figure for talking about local spacing regimes without
  pretending the repo already carries a canonical zero-statistics theorem.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)

Interpretation boundary:

- This is an exploratory spacing plot.
- It is not a GUE claim, pair-correlation theorem, or RH consequence theorem.

#### Dashi-projected zeta feature plot

![Dashi-projected zeta feature plot](Docs/Images/zeta/zeta_dashi_projected_feature_plot.png)

Reading:

- The x-axis is a phase-velocity-style feature.
- The y-axis is a zero-neighborhood-style score.
- Color is a local action-like score.
- The right-side high-phase cluster is the interesting regime in current
  Dashi language: it is the nearest analogue to a boundary/action/regime
  concentration rather than a flat cloud.

Relevant formalism sources:

- [`DASHI/Analysis/ZetaVisualization.agda`](DASHI/Analysis/ZetaVisualization.agda)
- [`DASHI/Analysis/AbelZeta.agda`](DASHI/Analysis/AbelZeta.agda)
- external source pack:
  [`temp-DOWNLOADED/zeta_visualization_pack/`](temp-DOWNLOADED/zeta_visualization_pack/)

Interpretation boundary:

- This figure is intentionally exploratory.
- It combines phase, local scoring, and zero-neighborhood heuristics.
- It is useful for regime thinking and visualization design, but it is not yet
  a canonical theorem object in the repo.
- Current validation snapshot:
  reference signed-permutation self-check = `exactMatch`,
  synthetic one-minus admissible candidate = `exactMatch`,
  Bool inversion secondary admissible candidate = `signatureOnlyMatch`,
  tail-permutation negative control = `mismatch`.
- Preferred next realization target:
  a Coxeter / Weyl-style 4D shell-orbit realization, beginning with an
  independent `B₄` shell/profile report and later promoted into the admissible
  harness only if its shell class becomes Lorentz-compatible and
  orientation/signature are justified.
- New Lorentz-neighborhood shell-side comparison:
  an independent synthetic one-minus-family candidate now matches the shift
  shell-1 and shell-2 profiles exactly and now serves as the canonical
  admissible alternate realization on the current Stage C path.
- New Lorentz-neighborhood dynamic search surface:
  a typed synthetic dynamics witness and a minimal independent-dynamics
  candidate now exist so the search for a second Lorentz-family realization
  is no longer shell-only.
- New synthetic-promotion status surface:
  the repo now records the exact blocker between the synthetic profile-aware
  candidate and admissible-harness promotion, instead of leaving that gap
  implicit.
- Synthetic promotion status is now complete on the current path:
  orientation and signature are bridged, a minimal independent-dynamics
  witness is present, and the synthetic one-minus candidate now enters the
  admissible rigidity harness.
- Stronger dynamics baseline:
  the canonical shift dynamics package now carries an explicit status object
  for propagation, causal admissibility, monotone quantity, and effective
  geometry, plus a semantics-bearing dynamics witness companion exported on
  the canonical path.
- New closure runway status surfaces:
  the canonical Stage C path now exports a concrete minimal
  constraint-closure status and a known-limits status surface so broader
  physics work can be staged without overstating recovery.
- New closure runway witnesses:
  the canonical Stage C path now also exports a first known-limits recovery
  witness and a witness-bearing spin/Dirac consumer surface.
- New closure runway theorem surfaces:
  the canonical Stage C path now also exports a concrete minimal
  constraint-closure witness and a stronger known-limits recovery witness that
  carries actual propagation and effective-geometry witnesses, not only status
  tags.
- New closure runway theorem slices:
  the canonical Stage C path now also exports:
  a minimal algebraic-closure theorem for the concrete three-generator system,
  a scoped known-limits local-recovery theorem for the current local
  Lorentz + propagation slice,
  and a scoped effective-geometry theorem for the same local recovery regime.
- Next canonical runway theorem slices:
  a scoped gauge-contract theorem on top of the canonical concrete closure
  baseline,
  and a scoped spin/local-Lorentz bridge theorem on top of the local recovery
  and effective-geometry baseline.
- Those two scoped runway theorems now live on the canonical Stage C path.
- The current widening beyond those scoped slices is now landed:
  a carrier-parametric gauge/constraint theorem with the current concrete
  carrier as its first instance, plus a second realized carrier instance,
  and a local causal-effective propagation theorem with a further local
  geometry-transport theorem on the current recovery baseline.
- Next widening step:
  a package-parametric gauge-constraint bridge theorem on top of the current
  carrier-parametric theorem, and a local causal-geometry coherence theorem
  above the transport slice.
- Those widening slices are now landed.
  Current newest physics-first widening is also landed:
  a stronger local recovery theorem beyond the current coherence slice,
  plus a stronger algebraic-coherence theorem beyond the current
  package-parametric bridge.
- That next physics-first widening is now landed:
  one stronger local recovered-regime theorem on top of the current local
  physics coherence slice,
  and one stronger algebraic-stability theorem on top of the current
  algebraic-coherence slice.
- That next physics-first cycle is now landed:
  one stronger recovered-dynamics theorem above the current complete-local
  regime slice,
  one stronger algebraic-consistency theorem above the current
  algebraic-bundle/stability slice,
  one geometry-facing downstream consumer on the widened canonical ladder,
  and one richer moonshine comparison bundle on the prototype track.
- Current next physics-first cycle is now landed:
  one stronger recovered-wave-geometry theorem above the current
  recovered-wavefront slice,
  one stronger algebraic regime-invariance theorem above the current
  transport-invariance slice,
  one wave-geometry-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave family summary on the prototype track.
- Current newest physics-first cycle is now landed:
  one stronger recovered-wave-regime theorem above the current
  recovered-wave-geometry slice,
  one stronger algebraic regime-persistence theorem above the current
  regime-invariance slice,
  one wave-regime-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave-regime summary on the prototype track.
- Current latest physics-first cycle is now landed:
  one stronger recovered-wave-observables theorem above the current
  recovered-wave-regime slice,
  one stronger algebraic regime-coherence theorem above the current
  regime-persistence slice,
  one wave-observable-facing downstream consumer on the widened canonical
  ladder,
  and one richer moonshine twined-wave-observable summary on the prototype track.
- Current algebraic milestone:
  use the already-landed finite orbit-shell generating-series layer for the
  current shift profile, then use it for standalone `B₄` comparison and a
  prototype wave lift.
- Safe symmetry-interpretation order:
  treat the current orbit profile as living first in a
  Weyl/root-system/theta-like neighborhood;
  only ask Niemeier/umbral-style questions if a genuine root-lattice shell
  realization appears;
  reserve Monster/Moonshine language for a future graded-module / trace bridge.
- Current moonshine-facing prototype:
  finite graded shell series and twined fixed-point traces are now present for
  the shift signed action and the standalone `B₄` Weyl action; canonical
  closure now carries a theorem-backed `Quadratic⇒Clifford → WaveLift⇒Even`
  factorization bridge, while the moonshine trace adapter remains prototype.
  Richer twiner libraries and a first graded/twined comparison report surface
  are now landed.
  A richer comparison bundle now sits over the existing detailed report and
  wave summary while staying pre-moonshine and non-modular.
  Safe interpretation policy:
  if a Monster-labeled anomaly report only shows a small rigid substructure
  without clear baseline/control separation, treat it as a non-unique
  structural regularity, not a Monster-specific fingerprint.
  Current measurement discipline:
  the DA51 / exponent-vector embedding is presently a representation-level
  structural probe, not a reliable semantic classifier for Monster-labeled
  proofs.
  Use JMD-side regime metadata (`eigenspace`, `bott`, `Hecke`, `orbifold`,
  `DA51`, `j-fixed`) for occupancy/divergence questions, and use DASHI-side
  delta/cone/Fejér/trace tests for dynamical questions.
  In particular, `p47` / `j-fixed` is currently best read as a baseline gauge
  constraint or normalization, not as a Monster-specific invariant.
  A local CSV-driven analysis harness now lives at
  `scripts/regime_test.py` for matched JMD regime tests, DASHI-side
  transition-table comparisons, and stepwise cone / Fejér checks from trace
  CSVs.
  For existing `dashifine` step embeddings, the direct entrypoint is:
  `python scripts/regime_test.py cone ../dashifine/hepdata_lyapunov_test_out/dashi_idk_out.csv/closure_embedding_per_step.csv --preset dashifine-closure-embedding`.
  That preset now reports the split explicitly:
  learned structural-cone pass,
  separate arrow-monotonicity pass,
  and the joint pass rate.
  Current direct result on the sibling-repo trace is:
  `structural_cone_pass_rate=1.0`,
  `arrow_pass_rate=0.9333`,
  `joint_pass_rate=0.9333`,
  with residual failures localized to `phistar_50_76` on `v_arrow`.
  The next cone-mode refinement is ultrametric/ternary boundary reporting:
  structural sign patterns, magnitude buckets, and nearest admissible pattern
  distance for localized violations.
  That ultrametric/ternary boundary report is now available in the same
  command output and confirms the current `phistar_50_76` failures are
  arrow-only boundary cases rather than structural-signature escapes.
  The same command now also performs an arrow-guard sweep, which on the
  current `dashifine` trace shows:
  `eps=1e-4 -> joint_pass_rate=0.95`,
  `eps=1e-3 -> 0.9667`,
  `eps=1e-2 -> 0.9833`,
  `eps=1e-1 -> 1.0`.
  The next refinement is an explicit boundary-class export so arrow-only cases
  are reported separately from true structural-cone failures.
  That boundary-class export is now present:
  the checked sibling-repo trace splits into `56` `interior` steps and `4`
  `arrow_boundary` steps, and the boundary cases can be written to CSV for
  downstream witness or review flows.
  That same harness now also carries canonical arrow profiles:
  `strict` (`arrow_eps=0`),
  `boundary` (`arrow_eps=1e-2`),
  and `lenient` (`arrow_eps=1e-1`).
  On the checked sibling-repo trace those give:
  `56/4`, `59/1`, and `60/0` for
  `interior/arrow_boundary` counts respectively.
  The current stable exported boundary artifact is
  `artifacts/regime_test/arrow_boundary_latest.csv`.
  The execution-admissibility bridge is now also landed:
  `scripts/regime_test.py cone` can export
  `artifacts/regime_test/execution_admissibility_latest.json`,
  `artifacts/regime_test/eigen_overlap_latest.csv`,
  and a concrete Agda witness module at
  `DASHI/Physics/Closure/ExecutionAdmissibilityCurrentTraceWitness.agda`.
  The same bridge now also exports a family-level Agda witness module at
  `DASHI/Physics/Closure/ExecutionAdmissibilityCurrentFamilyWitness.agda`,
  threaded through `PhysicsClosureCoreWitness` and surfaced from
  `MinimalCrediblePhysicsClosure`.
  The current strict-profile export still classifies the checked trace family
  as `56` `Interior` and `4` `ArrowBoundary`, with no structural-boundary or
  outside-class cases.
  The JMD-side scaffold is now seeded rather than empty:
  `scripts/build_jmd_regime_table.py` merges
  `data/regime_test/jmd_regime_seed.csv` into the Agda-tree scan and rebuilds
  `artifacts/regime_test/jmd_regime_table.csv`.
  Current first seeded occupancy read on the matched `7` Monster and `6`
  control rows is:
  `eigenspace JS=0.5569`,
  `bott JS=0.0608`,
  `joint(eigenspace,bott,hecke) JS=0.6176`,
  with the categorical comparison now running on the actual `M/O` subset
  rather than leaking unlabeled rows into the permutation/classification pass.
  The current seeded regime columns are still graph/seed proxies rather than a
  theorem-grade semantic ground truth, so they are suitable for local
  comparison scaffolding but not yet for strong symmetry claims.
  Source-side clarification:
  the explicit DASL / Monster address grammar now identified for this bridge
  lives in the sibling repo `../kant-zk-pastebin`.
  There, `src/dasl.rs` fixes the `0xDA51` address format, Monster primes,
  attack triple `(47,59,71)`, and orbifold coordinates;
  `src/sheaf.rs` fixes `EigenSpace`, encoding→prime assignment, and Bott/Hecke
  address fields;
  `src/ipfs.rs` wraps content in a DASL/CBOR envelope carrying those fields.
  So the repo now treats `kant-zk-pastebin` as the source-side `Σ_src` anchor
  for `Basin` / `Eigen` questions, while this repo remains the execution-side
  admissibility layer.
  A separate Lean-side check of `../dashi_lean4` does not change that.
  That repo is useful as a Lean witness for DA51/moonshine numerics and schema
  transport, but it does not provide the missing JMD-side class/projection
  layer:
  no DASL address grammar, no `EigenSpace` / `Earth|Spoke|Hub|Clock`, and no
  Bott/Hecke/orbifold class table for the HEPData family projection problem.
  Immediate implementation consequence:
  the next harness pass should load that DASL source model directly so
  `basin_ok` and source-backed eigen overlap are computed against an explicit
  source lattice grammar rather than only trace heuristics or seeded JMD rows.
  Current semantics note:
  `basin_ok` in the local artifacts presently means support under the parsed
  DASL eigenspace prior, not a full class-level source projection theorem.
  The runtime exports now carry the more explicit `source_support_ok` alias as
  well, and `basin_ok` should be read as that proxy until the source projector
  is richer.
  That first-pass source integration is now landed in `scripts/regime_test.py`:
  `cone` mode can parse the DASL source grammar from `../kant-zk-pastebin`,
  emit `artifacts/regime_test/dasl_source_lattice_latest.json`,
  and report a DASL-backed eigen prior plus a first-pass source-support
  `basin_ok`.
  On the checked `dashifine` trace family, that source-backed pass leaves the
  structural/arrow split unchanged (`56` `Interior`, `4` `ArrowBoundary`) but
  now also reports a narrower source mismatch:
  `48/60` steps are source-supported while `12/60` steps from `pTll_76_106`
  currently miss the parsed DASL eigenspace support because the trace-side
  heuristic lands them in `Hub` while the parsed DASL encoding prior is
  `Earth/Spoke`-only.
  Safe reading:
  this source anchor is enough to make first-pass source predicates
  computable, but it is not yet a proof that DASHI projection preserves the
  shared `p47`/gauge constraint automatically.
  Immediate next refinement:
  replace the current trace-side `Hub` heuristic with a profile-based
  eigenspace classifier and export both legacy and refined trace labels in the
  eigen/execution artifacts, since the present `pTll_76_106` mismatch is
  concentrated in that heuristic boundary.
  That refinement is now landed.
  The current artifacts export both `legacy_trace_eigenspace` and refined
  `trace_eigenspace`, and the direct `dashifine` rerun shows:
  `legacy_vs_refined_trace_agreement=4/5`, with the only changed family
  `pTll_76_106` moving from legacy `Hub` to refined `Spoke`.
  Under that refined classifier, the source-support proxy now clears the whole
  checked five-trace family: `60/60 source_support_ok`.
  Immediate next source-side refinement:
  the DASL loader should stop treating the source model as only the small
  encoding prior and instead lift the full `15`-prime Monster catalog already
  fixed in `../kant-zk-pastebin/src/dasl.rs`.
  That would make the exported source model explicitly carry `Earth/Spoke/Hub/Clock`
  support from the whole prime basis rather than only the encoding subset.
  That source-catalog promotion is now landed.
  The default DASL source mode is now `monster-primes`, and the emitted source
  JSON records all `15` primes plus the current eigenspace distribution
  `Earth=0.4667`, `Spoke=0.4`, `Hub=0.0667`, `Clock=0.0667`.
  On the checked `dashifine` trace this richer source model still preserves the
  same execution picture:
  `56 Interior`, `4 ArrowBoundary`, `60/60 source_support_ok`.
  The harness now also exposes an explicit source-projection proxy on top of
  that richer catalog.
  For the current checked traces, the canonical class-to-prime projection is:
  Earth-family traces → `p2 / T_2 / exponent 46`,
  and the refined `Spoke` trace family `pTll_76_106` → `p17 / T_17 / exponent 1`.
  This is a canonical source-projection surface, not yet a geometric
  nearest-neighbor theorem.
  Immediate next refinement:
  enrich that proxy into a scored source-prime ranking over the current source
  catalog, so the artifacts expose more than class membership and a single
  exponent tie-break while still staying short of a geometric nearest-neighbor
  claim.
  That scored ranking is now landed too.
  The artifacts now export a top-ranked source-prime shortlist per trace family.
  On the checked traces:
  Earth-family traces still rank `p2` first,
  while the refined `Spoke` family `pTll_76_106` shows a meaningful split:
  the canonical proxy remains `p17`, but the scored shortlist ranks
  `p59` and `p71` above it because they combine the same `Spoke` class with the
  attack-triple bonus.
  Treat that as a ranking heuristic signal, not yet as a promoted projection
  theorem.
  Immediate next refinement:
  expose an explicit primary source-projection mode so the repo can keep the
  conservative canonical proxy as default while also supporting a scored-primary
  projection mode for experiments.
  That explicit primary mode is now landed.
  `scripts/regime_test.py cone` keeps the canonical
  `source_projection_*` fields as the repo-default bridge surface, and also
  exports `primary_source_projection_*` fields driven by
  `--source-projection-primary canonical|scored`.
  Default remains `canonical`; `scored` is for experimental ranking-led runs.
  The artifacts now also export `projection_conflict` so rows like
  `pTll_76_106` can be marked explicitly when the canonical representative and
  the primary-selected experimental representative diverge.
  The scored ranking is now also canonical-anchored rather than
  attack-triple-led in isolation, and the exported shortlist is labeled
  explicitly as a diagnostic shortlist rather than a promoted primary
  projection surface.
  The artifacts now also expose score-component breakdowns for the ranked and
  primary source projections, so later source-side refinements can target the
  metric weights explicitly instead of treating the ranking as opaque.
  Canonical export cleanup also removed the legacy assumption-first closure
  instance from the public `PhysicsClosureSummary` and `Everything` surfaces;
  the compatibility module remains on disk, but it is no longer publicly
  re-exported on the canonical path, and the umbrella import no longer pulls
  in the empirical-to-full adapter either. The external full-closure
  constructor and the provider-based constructor are now named as legacy
  adapters, so the canonical naming no longer implies that the outside-wired
  routes are authoritative.
  The canonical `physicsClosureFullFromCoreWitness` path now assembles the
  full closure directly from the core witness, instead of bouncing through the
  legacy external adapter.
  The canonical contraction→quadratic theorem constructor now also delegates
  through the strong package’s canonical identity witness, so the uniqueness
  transport seam is less duplicated.
  The current score now includes source-side `Hecke` proximity and a weak
  `Bott` cycle prior in addition to trace support, exponent, canonical
  alignment, and attack-triple bonus.
  A three-batch `dashifine` rerun is now recorded in
  `artifacts/regime_test/dashifine_trace_batch_latest.json`.
  Across the current `out`, `out_new`, and `out_all` trace sets, source support
  stays fully intact and the refined `Spoke` family stays canonically at `p17`;
  the main new movement is on the execution side, where larger batches add
  `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` to the arrow-boundary family list.
  The harness now also exports a per-family boundary summary at
  `artifacts/regime_test/arrow_boundary_family_latest.json` for the default
  checked run, and the larger-batch read is now sharper:
  `phistar_50_76` is a small arrow-only tolerance ladder,
  `z_pt_7tev_atlas` is a single moderate arrow break,
  and `ttbar_mtt_8tev_cms` is the strongest current outlier because it couples
  large arrow violations with `v_dnorm` failures.
  Focused family drilldowns are now exportable too.
  The current `ttbar_mtt_8tev_cms` read is especially specific:
  it stays interior until a late onset at `t=10->11`, where a sign flip in the
  arrow coordinate coincides with the first mixed `v_arrow`/`v_dnorm` failure
  without an immediate structural-signature change.
  A terminal-step autopsy now also records raw axis values, per-axis deltas,
  and alternate `v_dnorm` normalizations for that family.
  On the current larger-batch run, those alternate `v_dnorm` views do not
  remove the two terminal positive `v_dnorm` deltas; they remain positive under
  raw, log-absolute, robust-z, winsorized, and family-minmax transforms.
  The important scale caveat is that those `v_dnorm` reversals are tiny
  (`~9.4e-13` and `~1.6e-13`) and sit at a near-zero floor, so the current best
  reading is late terminal-phase stiffness or tail-edge sensitivity in the
  representation, not a broad failure of the learned structural cone.
  The focused export now also carries observable-side context:
  `ttbar_mtt_8tev_cms` is a `7`-bin spectrum whose last bin (`x≈1350`) has the
  largest fractional uncertainty (`~8.19%`), and the first failing step occurs
  at the late `alpha=1e4 -> 1e5` jump.
  The same local provenance pass also shows that this family still has
  `closestpoint_frac=1.0` and `fejer_set_frac=1.0` in the sibling-repo reports,
  while the explicit failure sits on the MDL-exact surface
  (`MDL_monotone=False`, `2` violations, worst increase `0.694577`).
  So the current disciplined reading is:
  localized late MDL/tail-bin stiffness inside an otherwise closest-point /
  Fejér-admissible family, not a general collapse of the closure geometry.
  The local harness now reflects that directly at the family-summary layer:
  `ttbar_mtt_8tev_cms` is promoted from the generic
  `mixed_hard_axis_outlier` bucket to the narrower `mdl_tail_boundary` class,
  while the per-step witness remains unchanged as `ArrowBoundary`.
  That interpretation is now also encoded in
  `DASHI/Physics/Closure/TailBoundaryLemma.agda`:
  on the current family witness there exists an
  `MDLTailBoundaryFamily` whose family-level witness still satisfies
  cone / Fejér / closest-point admissibility while failing only at the
  stricter MDL-exact layer.
  The current empirical count artifact is
  `artifacts/regime_test/tail_boundary_lemma_latest.json`, which on the
  checked larger `dashifine` family set reports `1` `mdl_tail_boundary`
  family out of `9`, and that current case is both tail-localized and
  terminal-boundary by the local summary rule.
  The widened three-batch aggregate is now recorded in
  `artifacts/regime_test/tail_boundary_batch_latest.json`, produced by
  `scripts/tail_boundary_batch.py`.
  On the currently compatible `dashifine` batches it reports
  `2` `mdl_tail_boundary` instances across `3` datasets, with only one unique
  family (`ttbar_mtt_8tev_cms`), and both observed instances remain
  tail-localized, terminal-boundary, cone/Fejér/closest-point admissible, and
  MDL-exact-failing.
  The same aggregate now also makes the control split explicit:
  repeated `pTll` families plus `dijet_chi_7tev_cms` and `hgg_pt_8tev_atlas`
  remain interior controls, `phistar_50_76` repeats only as
  `arrow_ladder`, `z_pt_7tev_atlas` repeats only as `single_arrow_break`,
  and only `ttbar_mtt_8tev_cms` repeats as `mdl_tail_boundary`.
  The aggregate now also records the current expansion inventory directly:
  there are `3` compatible step files in `dashifine`,
  `7` current tail-candidate families,
  and among those only `ttbar_mtt_8tev_cms` and `z_pt_7tev_atlas` currently
  leave the interior.
  The next-priority tail candidates after `ttbar` are therefore
  `z_pt_7tev_atlas`, then the still-interior heavy-spectrum candidates
  `atlas_4l_m4l_8tev`, `atlas_4l_pt4l_8tev`,
  `dijet_chi_13tev_cms_mgt6`, `dijet_chi_7tev_cms`, and
  `hgg_pt_8tev_atlas`.
  The current focused `z_pt_7tev_atlas` drilldown now sharpens that next step:
  it is not another `mdl_tail_boundary`.
  It remains a milder `single_arrow_break`: one late tail-localized boundary
  step at `t=9->10`, `arrow_delta≈0.0305551`, no non-arrow failure, all tested
  `v_dnorm` variants remain nonincreasing there, and the family clears under
  the `lenient` arrow profile.
  The first still-interior heavy-spectrum candidate is now checked too:
  `atlas_4l_m4l_8tev` stays fully interior on the same all-batch run.
  Current focused read:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is not the maximum-fractional-uncertainty tail bin.
  The next heavy-spectrum control `atlas_4l_pt4l_8tev` is now checked as well
  and stays fully interior too:
  `12` steps, `0` boundary steps, `closestpoint_frac=1.0`,
  `fejer_set_frac=1.0`, `MDL_monotone=True`, no onset event, and its last bin
  is likewise not the maximum-fractional-uncertainty tail bin.
- Next theorem milestone:
  the bounded one-minus shell family is now the base layer and the parametric
  shell-1 theorem is now in place; the next theorem milestone is a second
  Lorentz-family realization and stronger shell-2 / orientation follow-through.
- Current closure hardening target:
  keep the canonical Stage C path, the empirical full adapter, and the legacy
  assumed closure surface on the same concrete constraint-closure witness, and
  keep the canonical Stage C entrypoint explicit in code rather than only in
  summary prose.
- Next runnable benchmark:
  Fejér-over-χ² monotonicity, starting from a typed shift reference harness
  with theorem-backed Fejér / closest-point / MDL witnesses and an explicit
  χ² falsifier-status boundary.
- Newly landed benchmark surface:
  observable-space collapse is now exposed as a typed shift benchmark backed
  by the observable fixed-point and uniqueness witnesses in the real closure
  kit.
- Current Fejér benchmark snapshot:
  positive side established and carried directly by the benchmark harness,
  χ² side now has a concrete shift-side boundary witness,
  that witness now sits inside a small explicit shift-side boundary library,
  and the standalone snap-threshold benchmark now includes secondary and
  tertiary shift-side boundary cases beyond the reference witness.
- Non-shift snap-threshold coverage now includes:
  a synthetic one-minus harness with a non-shift policy derived from its
  witness state type, a Bool inversion-specific harness with its own witness
  selection, and a standalone `B₄` harness.
- Lemma A/B constructive eliminators are now in place inside
  `CausalForcesLorentz31`; prioritized next steps (condensed):
  1) keep closure-pipeline labels and repo-facing citation order synchronized
     as modules are promoted,
  2) re-run direct `PhysicsClosureValidationSummary.agda` timing/validation when
     a longer runtime budget is available.

The repo does **not** currently claim full physics closure or “solved
physics”.

Note on `DASHI/Unifier.agda`:
it is a stub-style unification sketch that exposes axiomatized/placeholder
interfaces (not theorem-backed), and it is not part of the canonical Stage C
closure pipeline.

For the current forward-claim shortlist and falsifiability criteria, see
`Docs/MinimalCrediblePhysicsClosure.md`.
For the math-prof outreach framing and archive crosswalk, see
`Docs/MathProfOutreachSummary.md`.

Cleanup note:
- the current maintenance turn freezes new local wave-regime rungs,
  treats the grouped ladder modules as the authoritative internal API,
  and keeps the old per-rung modules only as compatibility surfaces.
- widening resumes only after canonical Stage C and the repo-facing summaries
  depend on the grouped surfaces rather than direct per-rung imports.
For the current milestone order, see `Docs/PhysicsClosurePriorities.md`.
For the current orbit-shell / Lorentz-signature framing, see
`Docs/OrbitShellProfilesAndLorentzSignature.md`.
For the authoritative Stage C theorem chain and module labels, see
`Docs/ClosurePipeline.md`.

## Typecheck Performance Policy (Current)

- Keep theorem certainty unchanged: performance work must not replace proven
  theorems with postulates.
- Use `abstract` for heavy theorem terms when downstream modules only need the
  theorem type, not internal definitional unfolding.
- First rollout target: repo-facing closure summary aliases in
  `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`.
- Second rollout target: aggregate theorem/summary record values in
  `DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda` and
  `DASHI/Physics/Closure/CanonicalStageCSummaryBundle.agda`.
- Third rollout target: remaining moonshine/regime summary aliases in
  `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`.
- Keep computational kernels transparent where reduction is part of behavior.
- For cyclic Base369 operators, prefer closed-form index arithmetic companions
  and explicit correctness bridges from recursive `spin` forms.

# I. State Space 

### 1. Carrier

Let

[
T = {-1, 0, +1}
]

Interpretation:

* (+1) = constructive / help
* (0) = neutral / indeterminate
* (-1) = destructive / harm

---

### 2. 3×3 Reasoning Tensor

[
S \in T^{L \times \tau}
]

Where:

**Lenses**
[
L = {3,6,9}
]

* 3 = Self
* 6 = Norm
* 9 = Mirror

**Temporal gates**
[
\tau = {p,0,f}
]

* p = past
* 0 = present
* f = future

Cardinality:

[
|T^{9}| = 3^9 = 19,683
]

This is the full virtual state sheet.

---

# II. Extracted Invariants

The supervisor does **not** reason over all 19,683 states directly.

It extracts an invariant tuple:

[
I(S) = (b_0, \sigma, \Delta_m, T, Z)
]

---

## 1. Present Backbone

[
b_0 = (S_{3,0}, S_{6,0}, S_{9,0}) \in T^3
]

This is the “spine”.

---

## 2. Temporal Instability per lens

[
\sigma_\ell = #{t_i \neq t_{i+1}}
]

Total instability:

[
\sigma = \sigma_3 + \sigma_6 + \sigma_9
]

---

## 3. Mirror Asymmetry

[
\Delta_m = \sum_{t \in \tau}
\mathbf{1}[S_{9,t} \neq \text{mirror_check}(S_{*,t})]
]

Measures conjugation failure.

---

## 4. Tension Mass

[
T = #(+) \cdot #(-)
]

High when help/harm coexist strongly.

---

## 5. Neutral Load

[
Z = #(0)
]

Tracks indeterminacy.

---

# III. Deterministic Motif Classifier

Define

[
\mathcal{M} : T^9 \to {M_1,\dots,M_9}
]

Ordered by priority rules.

---

## M1 – Robust Allow

Condition:

* (b_0 = (+,+,+))
* (\sigma = 0)
* (\Delta_m = 0)

Interpretation:
Full constructive interference.

Action:
Allow.

---

## M2 – Time-Gated Allow

Condition:

* (S_{3,0}=+)
* (S_{6,0}=+)
* (S_{9,0}=+)
* (S_{9,f} = -)

Interpretation:
Future instability only.

Action:
Add timing fence.

---

## M3 – Role-Gated

Condition:

* (S_{3,0}=+)
* (S_{9,0}=+)
* (S_{6,0}=-)

Interpretation:
Norm conflict only.

Action:
Restrict by role.

---

## M4 – Substrate Fail

Condition:

* (S_{6,0} \ge 0)
* (S_{9,0} \ge 0)
* (S_{3,0} \le 0)

Interpretation:
Externally coherent but locally harmful.

Action:
Redesign substrate.

---

## M5 – Mirror-Unstable

Condition:

* (S_{3,0}=+)
* (S_{6,0}=+)
* (S_{9,0}=-)

Interpretation:
Present looks fine but fails reflection.

Action:
Buffer. Do not generalize.

---

## M6 – Redesign Lane

Condition:

* (b_0 = (-,-,-)) OR strongly negative present
* but ∃ t ∈ {p,f} s.t. (S_{9,t} = +)

Interpretation:
Non-local constructive path exists.

Action:
Reframe (dose/time/product).

---

## M7 – Tolerance Rim

Condition:

* (S_{3,0}=+)
* but (\sigma) large
* flips toward negative over time

Interpretation:
Dynamical fatigue.

Action:
Frequency control.

---

## M8 – Programmatic Only

Condition:

* Sparse positive occupancy
* Most entries negative

Interpretation:
Filamentary viability only.

Action:
Structured program only.

---

## M9 – Retire / Prohibit

Condition:

[
b_0 = (-,-,-)
]

Interpretation:
All-red spine.

Action:
Disallow.

---

# IV. Topological Interpretation (Optional Layer)

You can interpret motifs as equivalence classes under symmetry:

[
G = S_3^{time} \times C_2^{mirror}
]

Motifs are orbits in quotient:

[
T^9 / G
]

Examples:

| Motif | Geometry        |
| ----- | --------------- |
| M1    | Stable sink     |
| M5    | Saddle          |
| M7    | Spiral          |
| M9    | Absorbing basin |

This is explanatory, not required for classification.

---

# V. M10 – Voxel Overflow

M10 is not a motif in the same equivalence class.

It is a **resolution jump**.

Define capacity:

[
C = 9
]

Overflow trigger:

[
Z + T > C
]

Interpretation:
Local invariant compression insufficient.

Operation:
Lift

[
T^9 \to T^{9} \times T
]

i.e., introduce new coordinate axis.

This is a carry operation (p-adic style).

Result:
New voxel.

---

# VI. Structural Summary

You now have:

* Finite state space (3^9)
* Deterministic invariant extraction
* Deterministic classification
* Explicit overflow rule
* No metaphors required
Current refactor status:
- the local Stage C wave-regime ladder is frozen for now
- grouped ladder modules are the authoritative internal import path
- widening resumes only after canonical code is routed through those grouped surfaces

## Local Nix / Zkperf Merge Surface

The repo now carries a local merge-prep Nix surface intended to harden an
upstream `nix`/`zkperf` merge without overstating what it validates.

- `nix build .#check` is the authoritative Nix check and mirrors the current
  GitHub workflow by typechecking `DASHI/Everything.agda`.
- `nix build .#merge-smoke` is the recursive merge-prep smoke check and walks
  the merge-relevant standalone roots plus recursive `Kernel/`, `Monster/`,
  and `Verification/` modules.
- The merge-prep target list is centralized in
  `scripts/list_merge_agda_targets.sh`, and the actual recursive compiler pass
  is wrapped by `scripts/run_agda_merge_smoke.sh`.
- `agda-record-all` is expected to recurse over that same merge-prep target
  surface rather than only top-level files.
- `dashi-agda.agda-lib` is now present as the local library surface used by
  this tooling layer.
- Any tracked DA51 / zkperf JSONL examples should be read as sample witness
  outputs, not as canonical reproducibility fixtures.

Merge-prep status:
the local Nix / zkperf surface is complete and validated, so active work now
returns to the physics closure spine and the existing tail-boundary follow-up
track.

## RG Toy Next Phase

The RG toy is now past pure shell/plumbing work.
It has operator families, mixed coarse/evolve schedules, endpoint and rich
benchmark layers, and a trace-aware mixed benchmark surface.

The next RG implementation work is split deliberately:

- Phase 2: enrich the operator/state hierarchy.
  Add multiple coarse schemes, multiple evolve modes, and a less trivial
  fixed-point/family structure so universality is not being tested against one
  stylized route.
- Phase 3: restate the current comparison and benchmark theorems against that
  richer hierarchy.
  The target is endpoint agreement with room for path/scale disagreement,
  rather than more collapse lemmas on the current toy encoding.

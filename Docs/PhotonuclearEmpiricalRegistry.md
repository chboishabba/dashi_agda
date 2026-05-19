# Photonuclear Empirical Registry

This note is the canonical owner map for the photonuclear / LHC empirical lane.
It exists to keep the lane durable and bounded:

- where constants come from,
- where measured observables are packaged,
- which scripts currently instantiate the lane,
- which docs explain the external physics, and
- which parts are explicitly not claims of Dashi closure.

## Repo-native code owners

### Constants registry

- `DASHI/Physics/Closure/PhotonuclearEmpiricalConstantsRegistry.agda`

Role:

- registers surrogate defaults,
- records example-derived inputs,
- attaches provenance to each entry,
- marks each entry with a claim-boundary tag.

Primary script/doc mirrors:

- `scripts/prototype_runner.py`
- `scripts/prototype_gbw.py`
- `scripts/prototype_ipsat.py`
- `Docs/GBWResponse.md`
- `Docs/SaturationLayer.md`

### Measurement surface

- `DASHI/Physics/Closure/PhotonuclearEmpiricalMeasurementSurface.agda`

Role:

- packages measured observables,
- packages per-sample payloads,
- packages per-measurement provenance hooks,
- carries explicit in-scope and out-of-scope claim bookkeeping.

Primary script/doc mirrors:

- `scripts/prototype_schema.py`
- `scripts/emit_shift_prototype_examples.py`
- `Docs/NumericObservableInterface.md`
- `Docs/CMSPhotonuclearBridge.md`

### Evidence summary

- `DASHI/Physics/Closure/PhotonuclearEmpiricalEvidenceSummary.agda`

Role:

- combines the constants registry and measurement surface,
- exposes repo-facing counts,
- records empirical-only status,
- gives one canonical summary owner for the current photonuclear lane.

### Validation summary

- `DASHI/Physics/Closure/PhotonuclearEmpiricalValidationSummary.agda`

Role:

- wraps the evidence summary in the thinnest repo-facing validation owner,
- exposes simple validation counts and status tags,
- keeps the lane explicitly empirical-only and non-claiming.

### Empirical adequacy carrier diagnostic

- `DASHI/Physics/Closure/EmpiricalAdequacyCarrierDiagnostic.agda`

Role:

- instantiates the narrow typed `EmpiricalAdequacy` equality available today:
  the packaged `Nat` defect-channel observable is observed at the held
  shift-pressure fixed point;
- records that this equality is only over one packaged `Nat` observable, not
  the stronger full-profile origin/chi2/B4 empirical adequacy bridge;
- uses the repo-local term `mismatch diagnostic` in the strict typed sense:
  each diagnostic records the first mismatch depth, the model/empirical trits
  at that depth, the trit-level mismatch kind, and the responsible pipeline
  component from `F_extract`, `F_promote`, `F_graph`, `F_explain`, or
  `F_action`;
- carries the current blocker statuses as typed evidence:
  `poolCarrierMismatch`, `noSameSurfaceRecovered`, `standaloneOnly`, and the
  full photonuclear profile's `Set₁`/`Set` mismatch against the current P0
  obligation; it also consumes the W8b origin-observation receipt and records
  that its empirical status remains `empiricalBlocked`;
- imports `Chi2FixedPointCarrierTransportObstruction`, which names the positive
  `Chi2FixedPointCarrierTransportReceipt` needed to transport the chi2 pool to
  the fixed-point carrier, and records the current obstruction as
  `blockedByPoolMismatchAndNoSameSurface`; the receipt is now inhabited, but
  only by a `carrierForgettingConstantReceiptOnly` boundary, so it does not
  discharge the non-forgetting same-surface theorem;
- imports `Chi2NonForgettingSameSurfaceObstruction`, which proves that the
  current same `Nat` defect target cannot also distinguish the primary and
  secondary chi2 cases. The next admissible W3 repair is therefore not another
  constant fixed-point receipt; it needs a boundary-case discriminator, an
  injective/nonconstant observation target, and a same-surface transport law
  over `Chi2BoundaryCase`;
- imports `Chi2CanonicalPoolObservationCandidate`, which supplies a local
  nonconstant `0/1/2` discriminator for the canonical chi2 pool cases. This
  reduces the discriminator gap, but remains explicitly local-only,
  non-empirical, non-promoting, and not an `obs(fixedPoint) = empirical`
  bridge;
- imports `Chi2ToShiftPressureTransportCandidate`, which maps the local chi2
  pool cases onto `shiftStartPoint`, `shiftNextPoint`, and
  `shiftHeldExitPoint` with pairwise distinction. This is a local
  same-carrier transport candidate, not fixed-point landing, not empirical
  transport, and not an adequacy bridge;
- imports `Chi2TransportDynamicsToFixedPointBridge`, which composes that local
  transport with the existing `shiftConvergesToHeldWithin2` dynamics theorem.
  This isolates the remaining local W3 gap to empirical observation target and
  promotion bridge work; it still does not assert `obs(fixedPoint) =
  empirical`;
- `W3EmpiricalTargetPromotionBridgeObligation` packages the remaining positive
  W3 work as obligations: nonconstant empirical observation target over the
  transported chi2 pool, promotion from the local chi2 path to
  `P0.EmpiricalAdequacy`, empirical B4 promotion beyond `standaloneOnly`, and
  origin receipt promotion beyond `empiricalBlocked`;
- `W3SurrogateEmpiricalTargetBoundary` proves the W3 target/promotion record
  shape is structurally inhabitible with a synthetic `Nat` target, but marks
  that inhabitant as surrogate-only. It does not replace accepted empirical
  evidence, does not promote empirical B4 validation, and does not promote the
  origin observation receipt;
- `W3AcceptedEmpiricalAuthorityGate` separates the accepted-authority gate from
  the surrogate target shape. The current gate status records photonuclear
  evidence and validation as empirical-only, B4 shell comparison as
  `standaloneOnly`, and the origin observation receipt as `empiricalBlocked`;
- `W3AcceptedEvidenceAuthorityToken` has no constructors in the current repo.
  This hardens the gate: the synthetic surrogate target can inhabit the target
  shape, but it cannot be reused as accepted empirical authority without a new
  upstream receipt;
- `W3AcceptedAuthorityExternalReceiptObligation` names that upstream receipt
  shape explicitly: it must carry the authority token, an evidence-backed
  empirical target, B4 empirical promotion, origin receipt promotion, and the
  matching bridge obligations. The current status remains
  obligations-needed/blocked;
- exposes structured W3 diagnostics for the current complement of the narrow
  equality: chi2 pool carrier mismatch and chi2 tail lift are `F_graph`
  under-promotion diagnostics, chi2 fixed-point carrier transport is now a
  separate `F_graph` obstruction diagnostic, the carrier-forgetting receipt
  boundary and the non-forgetting same-surface contradiction are `F_explain`
  diagnostics, B4 `standaloneOnly` is an `F_promote` under-promotion
  diagnostic, the B4 closure-promotion bridge is recorded as a separate
  `F_promote` diagnostic rather than a discharge of empirical B4 validation,
  and the full-profile universe mismatch plus W8b
  `empiricalBlocked` receipt are `F_explain` under-promotion diagnostics;
- consumes the W1 narrow equality retarget policy decision as typed evidence
  rather than treating retarget policy selection as a remaining W3 blocker;
- records `B4EmpiricalDependencyReceipt`: the closure/observable
  `RootSystemB4PromotionBridge` is `admissiblePromotionReady`, but the
  empirical `RootSystemB4ShellComparison.report` remains `standaloneOnly`, so
  closure-side B4 promotion does not satisfy the empirical adequacy dependency;
- names the next type needed for promotion:
  a `StrongEmpiricalAdequacyBridgeNextType` with chi2-pool transport onto the
  fixed-point carrier, B4 promotion beyond `standaloneOnly`, and promotion of
  the consumed W8b origin-observation receipt beyond `empiricalBlocked`.

### Canonical normalized artifact schema

- `scripts/hepdata_artifact_schema.json`
- `scripts/hepdata_adapter.py`
- `scripts/hepdata_consumer.py`
- `scripts/hepdata_family_crosswalk.json`
- `scripts/hepdata_surface_report.py`
- `scripts/hepdata_program_surface.py`
- `scripts/hepdata_projection_contract.py`

Role:

- defines the canonical JSON normalization boundary for legacy HEPData and
  `dashitest` empirical artifacts,
- prefers the NPZ-backed `x/y/cov` measurement surface when it exists and
  downgrades covariance-free lens tables to an explicit fallback,
- resolves family names through an explicit crosswalk rather than stem-only
  inference so stage-specific naming drift stays visible,
- keeps measurement, evidence, and validation payloads on one repo-native
  surface,
- allows the old dataset/timeseries/certification outputs to be ingested
  without re-running the legacy fitting pipeline,
- preserves explicit claim-boundary bookkeeping so the normalized artifact
  stays empirical-only.

Thin consumer role:

- loads one canonical artifact,
- selects one validated family payload,
- extracts only the `MeasurementSurface` carrier required by the current
  prototype schema layer,
- refuses artifacts whose measurement fields or validation status are
  incomplete,
- does not invoke runner, scorecard, fitting, or theorem-side code.

Surface-report role:

- consumes one already-validated measurement surface,
- computes health-only diagnostics such as point count, covariance rank,
  condition number, symmetry, and value ranges,
- exposes `projection_eligible` as the current explicit gate for any future
  projection lane,
- stays measurement-side and report-only,
- does not construct a `DashiStateSchema` or a `Δ` interpretation.

Program-surface role:

- promotes one already-validated measurement/report path into a single named
  repo-facing empirical program surface,
- packages the measurement summary, surface health report, and projection
  contract in one artifact,
- keeps the empirical lane explicit and reusable without pretending that a
  `MeasurementSurface -> DashiStateSchema` interpretation already exists,
- stays packaging-side only and makes no theorem claims.

Projection-contract role:

- fixes the future `MeasurementSurface -> ΔState` interpretation boundary as
  a contract rather than an implementation,
- records admissibility conditions, hard failures, transform declaration
  requirements, and claim-boundary rules,
- prevents future projection code from silently dropping covariance or
  inventing `Δ` semantics.

Canonical payload blocks:

- top-level:
  `artifact_schema`,
  `schema_version`,
  `generated_utc`,
  `source`,
  `assumptions`,
  and either one `family` payload or a `families` map
- per-family:
  `measurement`,
  `metrics`,
  `timeseries`,
  `certification`,
  `evidence_summary`,
  `validation_summary`

Primary invariants:

- counts are nonnegative integers,
- packaging status is explicit as `ok`, `missing`, or `error`,
- measurement-field status is explicit per family for `x`, `y`, and `cov`,
- family-name resolution is explicit per family rather than implied by file
  stem coincidence,
- all claim-boundary strings remain explicit rather than implicit,
- normalization may carry provenance and completeness summaries, but it does
  not add live fetches, re-fit the old pipeline, or make theorem claims.
- projection eligibility is explicit and currently narrower than measurement
  admission.

## Current script owners

### State and observable schema

- `scripts/prototype_schema.py`

Current payload owners:

- `trace_id`
- `delta`
- `coarse_head`
- `mdl_level`
- `photon_energy`
- derived numeric observables such as promoted and saturation-facing proxies

### Runner defaults and packaging

- `scripts/prototype_runner.py`

Current runner/default owners:

- GBW-style defaults
- shared surrogate defaults
- base output packaging for predicted yield, flags, and observables

### Reduced response families

- `scripts/prototype_gbw.py`
- `scripts/prototype_ipsat.py`

Current response-family owners:

- surrogate parameter families
- predicted-yield packaging
- residual and confidence fields

### Comparison and scorecard surfaces

- `scripts/prototype_matrix.py`
- `scripts/compare_surrogate_models.py`
- `scripts/prototype_scorecard.py`

Role:

- compare reduced model families,
- compute explanation-side residual/penalty summaries,
- keep the lane explanatory rather than fit-claiming.

## Historical precedent in `../dashitest`

The older HEPData/LHC lane in the sibling repo follows the same three-stage
shape as this photonuclear registry, but on a different empirical subject:

- dataset package:
  - `hepdata_to_dashi/<observable>/lenses_continuous.csv`
  - `dashifine/hepdata_npz_all/*.npz`
- metrics package:
  - `hepdata_dashi_native/*_dashi_native_metrics.csv`
  - `hepdata_beta_dashboard_out/summary.csv`
- certification package:
  - `hepdata_lyapunov_test_out/overall_certification.json`
  - `dashifine/hepdata_proof_dossier/report.md`

That lane is a useful empirical precedent for packaging, metrics, and
certification structure. It is not a dependency of the photonuclear sidecars.

## External-physics docs

- `Docs/PhotonBridge.md`
- `Docs/CMSPhotonuclearBridge.md`
- `Docs/CharmPhotoproduction.md`
- `Docs/SaturationLayer.md`
- `Docs/CMSCapstone.md`

These docs explain the external QED/QCD interpretation layer. They are not
replaced by the Agda sidecars.

## Boundary conditions

The photonuclear empirical lane currently claims only:

- empirical input registration,
- empirical payload packaging,
- provenance tracking,
- measurement-side control surfaces.

It does not claim:

- equivalent-photon derivation,
- QCD charm-production derivation,
- CMS fit reproduction,
- closure of the `Δ -> Q̂core` bridge,
- internalization of the external collider theory stack.

Projection boundary:

- `MeasurementSurface -> DashiStateSchema` remains intentionally deferred,
- any future projection must first declare:
  explicit semantic meaning for `delta/coarse_head`,
  covariance propagation or metric law,
  and invariant-preservation/failure conditions,
- until then the normalized HEPData bridge terminates at
  `MeasurementSurface` only.

## Validation policy

Use leaf validation on the photonuclear empirical modules directly.

Do not treat this lane as a reason to run:

- `DASHI/Everything.agda`
- `DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda`

unless the task is explicitly about those aggregate targets.

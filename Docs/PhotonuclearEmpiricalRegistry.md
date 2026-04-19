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

### Canonical normalized artifact schema

- `scripts/hepdata_artifact_schema.json`
- `scripts/hepdata_adapter.py`
- `scripts/hepdata_consumer.py`
- `scripts/hepdata_family_crosswalk.json`
- `scripts/hepdata_surface_report.py`
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

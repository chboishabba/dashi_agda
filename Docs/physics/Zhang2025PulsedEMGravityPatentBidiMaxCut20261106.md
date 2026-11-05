# Zhang 2025 pulsed-EM "gravity-like" patent × DASHI exotic-gravity max-cut

Date: 2026-11-06. **Status: implemented source/bounded-comparator adapter; physical production and measurement OPEN.** This is not a patent validity opinion, proof of infringement or proof of unusual gravity.

## 0. Primary sources and identity

| object | source identity / statement | authority ceiling |
|---|---|---|
| Chinese publication | CN119943525A, published 2025-05-06, priority 2025-01-21 | Original invention claim, not experimental replication |
| US counterpart | US12417870B1, 2025-09-16 grant; inventors Xiangqian Zhang, Zhongqiang Xiao, Xiang Li; assignee Zhang Xiang Qian Technologies Inc. | Same patent family, not evidence of an independent second device |
| International counterpart | WO2026157422A1, published 2026-07-30 | Same priority family, not a third replication |
| Previous US Navy patent | Salvatore Pais US10322827B2, granted 2019-06-18 | Different proposed high-frequency gravitational-wave source; patent alone does not validate it |
| Social-media source | User supplied `transcript-2026-11-05.srt` (11 clauses, 0:00–0:39.680) | Claims "stealing" and "exact same deal"; no technical measurement or patent-claim crosswalk |

Primary locators:
- https://patents.google.com/patent/US12417870B1/en
- https://patents.google.com/patent/CN119943525A/en
- https://patents.google.com/patent/WO2026157422A1/en
- https://patents.google.com/patent/US10322827B2/en
- Existing source-first Pais audit: https://github.com/chboishabba/dashi_agda/pull/1256

Patent US claim 1 covers a controlled time-varying EM source and motion of a target along a prescribed trajectory. Claims 2–3 mention HV DC, frequency conversion, coils and pulsing. Claim 9 describes the suspended ball/two-coil vacuum tank. The description discusses plastics and polarization and itself mentions classical EM induction/polarization mechanisms. Do **not** rephrase those claims as a measured spacetime metric or a demonstrated mass reduction.

The prose embodiment reports approximately 50,000 V and 1/100000 A, a 10 cm *tank diameter*, a thin cotton suspension and an upper energized/lower grounded coil. VI = 0.5 W is the **nominal product** of those illustrative source values, not measured total wall power, phase-resolved pulse energy, stored electromagnetic energy, sphere force or a 10 cm electrode gap. Geometry, charge, dielectric properties, field derivatives, gas pressure, frequency waveform, force/torque readout, sample size, uncertainty and independent replication remain unavailable as calibrated matched data.

Patent granting, registered assignee nationality, or same superficial component list cannot establish a specific act of technology theft or the "Pais effect."

## 1. Claim decomposition and accepted observation channels

**Do not treat the coarse phrase "gravity-like effect" as a measurement.** A rotating sphere can demonstrate target motion while leaving the mechanism undecided. The first bounded consumer is a signed local force (or a separately calibrated torque) in the original apparatus.

| target | claim type | existing DASHI owner | missing physical receipt |
|---|---|---|---|
| Sphere movement | patent/source assertion, no antigravity claim type | `Zhang2025EMGravitySourceClaimExact` | recorded force/torque, original waveform, calibration, raw data |
| Local residual signed force | conditional physics comparison | `AntigravityLaboratoryBackgroundClosureExact`, `AntigravityClaimTheoryComparisonExact` | same-identity ON/OFF and all nuisance closures |
| Remote test mass response | `Anti.remoteRepulsiveField` | `Anti.requiredDiscriminator`, `AntigravityStrongestConditionalTheoremExact` | independently instrumented test mass, source/geometry/stress, scaling and replication |
| Free-fall response | `Anti.changedFreeFallResponse` | `Anti.requiredDiscriminator` | free-fall accelerometer isolating nongravitational forces |
| Metric-clock/optical response | `Anti.engineeredMetricResponse` | stress-to-metric and four-channel physical owner #1120 (unmerged) | conserved source stress, same metric, clock/optical signals |
| Propagating gravitational wave | *different source channel*, not automatically an Anti claim | Pais #1256, EM-GW #1099 (both unmerged) | transverse-traceless far-field radiation and independent detector |

Existing in-master owners: #828, #852, #1045. Open sibling donors: #1256, #1120, #1099, #1241, #1284, #1460. Unmerged sources remain references only and are not silently imported.

## 2. Classical null: explicit controls, units and scope

Weak, quasistatic, linear and locally isotropic selected formulae in SI:

```
F_e (N) = q (C) * E (V/m)
F_DEP (N) = 1/2 * alpha (C m^2/V) * grad[E^2] (V^2/m^3)
F_m (N) = chi * volume (m^3) / (2 mu0) * grad[B^2] (T^2/m)
```

They are **comparison kernels**, not an adequate full pulsed HV/coil Maxwell–matter–mechanics simulation. In particular applied voltage DOES NOT determine local E, tank diameter DOES NOT determine gap, and alpha/chi must be material- and frequency-appropriate. A dielectric insulator can be polarised, so "nonconducting" does not imply "no electromagnetic force."

The script `scripts/check_zhang2025_em_gravity_bidi.py` implements a signed-force interval handoff. It requires paired **ON/OFF** source states sharing apparatus, target, axis, configuration, calibration and instrument, distinct run IDs, explicit raw-hash metadata, and eleven separately bounded families:

```
charge_force, dielectrophoresis, magnetic_gradient,
time_varying_induction, suspension_and_support,
mechanical_vibration, thermal_drift, residual_gas_and_ionic_wind,
rf_instrumentation, radiative_momentum, unmodelled_cross_couplings
```

Every bound (including any explicitly justified zero) requires an evidence-receipt locator; the program cannot authenticate that locator. Omission is recorded as `incomplete_ordinary_force_comparator`, NEVER silently set to zero. Each bound is a conservative deterministic interval, not a sigma/significance claim. An entirely bounded model can yield `ordinary_force_interval_compatible` or `candidate_unexplained_signed_force_residual`; the latter is **not** a discovered gravitational field. Explicit synthetic fixtures are always `synthetic_fixture_only`. Raw SHA metadata is not verified against bytes by this script, so source provenance is a separate real-world gate.

For paired interval observations, `M_on`, `M_off`, and classical model `C_on`, `C_off`:

```
R = (M_on - M_off) - (C_on - C_off)
```

All four intervals propagate through subtraction by extrema. A nonzero residual interval requires further ordinary-physics model checks and blinded validation. It does **not** imply tensorial gravitational geometry, negative Newton coupling, unique propulsion or propagating GW. No generated fixture is labeled empirical evidence. An explicit catch-all bound for unmodelled and cross-coupling forces is required, but even it does not mathematically prove model completeness.

**Execution:**

```sh
python3 -m unittest discover -s tests -p 'test_zhang2025_em_gravity_bidi.py' -v
python3 scripts/check_zhang2025_em_gravity_bidi.py --input path/to/calibrated_case.json
```

Runnable synthetic case: `python3 scripts/check_zhang2025_em_gravity_bidi.py --input tests/fixtures/zhang2025_synthetic_pair.json`. This fixture has **no** real measurement entitlement.\n\nInput must declare `data_kind` as `synthetic` or `real_unverified`. Each `on` and `off` is a JSON object with identity metadata, `source_mode`, `channel: signed_force_N`, `measurement: {nominal_N, bound_N, evidence_receipt}`, and a `force_classes` map containing bounded entries for each required mechanism. Rotational-angle videos cannot be fed in as N without an independently measured force/torque calibration.

## 3. Agda integration and no-promotion

- `Zhang2025EMGravitySourceClaimExact.agda`: exactly one patent family; source assertion vs measurements; classical insulator-polarization finite witness; no automatic mass/GW/metric entitlement; separate original motion and gravity-consumer types.
- `Zhang2025EMGravityPhysicalPromotionExact.agda`: **only** consumes the already-existing `ProvenancedComparativeAnomalyReceipt` indexed by the requested canonical `AntigravityClaim`. The compiler cannot create that physical receipt from patent text. External-field and metric consumers stay disjoint and require their own typed receipts.
- `Zhang2025EMGravityValidation.agda`: dependency-free regression of the new finite source/scope terms. Any exact-head kernel success must be separately recorded.
- `Everything.agda`: import discovery for these three owners; no change to the conditional negative-G theorem or to core GR semantics.

## 4. Exact max-cut / Pareto frontier

| Gate | Deliverable in this branch | Remaining real source payment |
|---|---|---|
| Z0 — source identity | exact original patent-family map, attribution, source claim type, transcript ceiling | primary proof of copying/infringement (not present; must NOT be inferred) |
| Z1 — classical signed-force comparator | 3 sourced weak kernels, 10-class interval ledger, explicit missing input and paired-identity checks, synthetic unit tests | measured local fields/gradients and material coefficients; frequency-dependent full Maxwell/mechanical model |
| Z2 — source-matched anomaly | typed projection to established DASHI provenance and comparative-anomaly receipts; no shortcut | original matched apparatus/source/target/raw dataset, all confounder bounds, blinded ON/OFF, measurement calibrations |
| Z3 — gravitational discrimination | separate external-test-mass / free-fall / metric channels with exact consumer identity | independently observed test-mass/free-fall/clock/optical outcomes and ordinary-GR predicted values from SAME physical stress and metric |
| Z4 — replication/mechanism | no-promotion boundary and strongest conditional negative-G route preserved | independent replication, scaling, physical action/stress and comparison to alternative models |
| Z5 — Pais/GW bridge, **optional** | separate source-specific GW lane, no direct motion-to-TT coercion | conserved total EM/matter/elastic source, radiative TT waveform and independent far-field detector |
| Z6 — formal verification | Agda source and test cases committed | exact-head Agda `--safe` receipt and CI pass must be observed; none manufactured here |

**Steelman:** a time-modulated coil apparatus induces measurable motion of dielectric matter. This can be valuable as a material-control effect without new gravitational physics. The substantially stronger gravitational hypothesis predicts a sourced metric or an external inertial/free-fall response surviving all known force couplings; it must be tested on the same source and geometry. This is a clean BIDI fork, not an assumption of negative G.

**Hard terminal:** from the provided patent/transcript, Z0 can close as documentation and Z1 can close as a *method/model*; Z2–Z5 cannot be marked physically complete absent original calibrated measurements. Formal exactness never substitutes for experimental identity.

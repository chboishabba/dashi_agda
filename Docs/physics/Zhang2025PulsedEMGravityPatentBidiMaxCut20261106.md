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

## 5. 2026-11-06 WEB SOURCE UPDATE: first-party claims and independent negative comparator

**Source custody correction: not all experimental descriptions are absent, but there is no identified complete calibrated SAME-APPARATUS receipt.** Original research by Xiangqian Zhang and Yuchuan Xu supplies the following, with evidence ceilings:

- Original English 6+ page preprint, `An experiment in which a varying electromagnetic field generates a gravitational field that causes all objects to move`: https://zhangxiangqian.me/files/An%20experiment%20in%20which%20a%20varying%20electromagnetic%20field%20generates%20a%20gravitational%20field%20that%20causes%20all%20objects%20to%20move.pdf . Reports one 400-turn amorphous iron toroid, 130/190/30 mm, 18 mm GAP, 50–100 V, 10–50 A, 50 Hz, alleged gap field ~0.2–0.5 T, six *differently sized and weighted* samples (epoxy, paper, ceramic, leaves, aluminium, pork skin), and visual motion in AMBIENT AIR; says DC 20–60 V motion is similar. Source does not show calibrated force traces / measured accelerations / measured source B(x,t) maps / independent gravimeter traces. It asserts air and vibration controls without published quantitative nuisance budgets.
- Chinese original `Gravitational Field and Object Motion Generated by Electromagnetic Changes`, Xinjiang Steel (新疆钢铁), 2025 issue 1 pp45–47, DOI 10.20146/j.cnki.1672-4224.2025.01.016: https://www.ahdvlp.cn/upload/file/2025/07/276879f4533b6c125.pdf . **Same authors, same geometry**, thus not independent replication. Document text confirms motion in ambient pressure and proposes `curl A = B / k` without source-fitted, uncertainty-qualified `k`. PDF page screenshots could not be loaded during the web audit (502); assessment uses retrieved text, and does not claim visual chart inspection.
- `Material-Independent Acceleration in Time-Varying Magnetic Fields`, Zhang/Xu SSRN abstract posted 2025-08-19, revised 2025-08-27: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=5389995 . Same authors and same toroidal study. Claims material-independent motion, reports approximate 0.1–0.5 T and 50 Hz / DC switching, describes vibration/airflow controls, but its abstract explicitly places precision measurements, vacuum, Faraday shielding and quantitative scaling in **future work**. Proposes **different** law `curl G = -alpha * time_derivative(B)`. This is not automatically identical to `curl A = B/k`; a steady DC field has `dB/dt=0` after transient while `B` can remain nonzero, so the two curl sources make distinct predictions. An experimentally observable gravitational field itself is NOT proved absent by curl=0: only that curl source vanishes under the second ansatz.
- `An Experiment Based on The Generation of Positive and Negative Gravitational Fields by the Accelerated Motion of Positive Charges`, same authors SSRN posted 2025-09-17, https://papers.ssrn.com/sol3/papers.cfm?abstract_id=5420875 . A **further first-party claim**, not an independent confirmation. Its assertion of positive/negative gravitational fields does not inhabit DASHI's constitutive signed-G receipt.
- First-party experimental guide: https://www.unifiedfield.info/experiment, updated accessible 2026-11-06. Offers 18±1mm gap build, 400 turns, 60Hz 0.1–0.3T *target*, suggested simple electrostatic/airflow/vibration controls and recommended video/log fields. Crucial distinction: a replication **guide** is not a published raw replication result; a target field is not necessarily a calibrated measured field. No source-specific original time-series dataset or blinded residual was found in the material reviewed.
- Independent experimental baseline: M. Tajmar, M. Kößling and O. Neunzig, *Scientific Reports* 14:19427 (2024), DOI https://doi.org/10.1038/s41598-024-70286-w . Under specified **steady-field** regimes, shielded/vacuum torsion/force balances including solenoids/toroids found no anomalous forces/torques to their nano-Newton/nano-Newton-meter limits. Not a direct replication of either Zhang's 50Hz 10–50A toroid or the patent's HV vacuum sphere.
- Independent **2026** comparator: M. Tajmar, M. Olek and O. Neunzig, *International Journal of Modern Physics A* 41(27), 2650147 (2026-07-25), DOI https://doi.org/10.1142/S0217751X26501472, AGH institutional abstract https://badap.agh.edu.pl/publikacja/170712 . No anomalous force/weight change above ~0.1mg balance resolution under ambient/water **DC up to 3A** for selected toroidal solenoids. Theory-specific Mbelek/modified KK bounds improve 6–10 orders of magnitude. NOT a Zhang apparatus replication, NOT a test of arbitrary high-voltage transients, but a strong material/geometry/nuisance baseline.

**Three DIFFERENT source objects**, not interchangeable:
```text
A patent HV 10-cm-vessel suspended plastic sphere, up to ~50kV; mode/geometry described
B Zhang/Xu 18-mm toroid gap, 400 turns, 50Hz 10–50A, ambient-pressure samples
C Pais HFGWG charged rotating/acoustic cavity proposal
```
A and B may be from overlapping inventors/programme but their run IDs, original geometry, electric waveform and sample response are not automatically identical. Likewise B is not an independent replication of A. The source-safe Agda owner explicitly separates these three apparatus records.

### Re-evaluated first five max-cut gates after web acquisition

| Gate | Source now located | Still *not* paid |
|---|---|---|
| Original calibrated field, material, motion | First-party 2025 specified dimensions/materials/nominal field and qualitative clips; guide metadata schema | ORIGINAL measured B/E waveform+gradient maps, specimen charge/susceptibility/polarizability, measured trajectory/acceleration/torque/force with error bars and instrument trace. Source geometry must match A or B explicitly |
| Complete Maxwell–matter–mechanics | Concrete toroid geometry sufficient for a bounded new numerical/symbolic model; selected known EM force families already coded | selected nonlinear hysteretic magnetic circuit, coil transient, dielectric charge, sample dynamics, thread torque, buoyancy and phase-resolved conservation/uncertainty on the actual apparatus |
| Residual with all controls | Authors report attempted vibration/air suppression; guide proposes electrostatic/magnetic dummies | calibrated source-specific nuisance budget, blinded matched runs, raw data and nonzero bound after subtraction; **no positive residual established** |
| Independent gravity-sensitive channels | Independent gravity literature/gravimetry methods exist | for these A or B devices: external shielded test mass, independent free fall, clock/optical metric channel, source/stress/geometry identity |
| Replication / mechanism | Same-author republications, plus independent steady-field and weaker DC comparator **negative studies** | registered, independent same-object replication at measured matched parameters, discriminating steady-vs-transient `B` vs `dB/dt`, mass/composition dependence and polarity tests |

**Prioritised Pareto acquisition**: obtain ORIGINAL complete on/off video with frame-time data, synchronous measured B(t), dB/dt and field gradients, exact target/thread properties, vacuum/air-pressure log, input real power and coil-temperature record from *either* identified A or B rig; do not combine measurements from the two. Next ask for apparatus-specific response-vs-frequency, response-vs-polarity and response-vs-current/ramp-rate with open negative controls. Then independent test mass/free fall readout. No observational/gravitational promotion until empirical receipts actually exist.

**Cross-domain note**: A scalar, electrodynamic or KK proposed action must deliver its own conserved source and selected stress/metric prediction under the same apparatus; an alternative action's numerical fit cannot promote a local force to universal negative-G or to a Pais-type propagating TT gravitational wave.

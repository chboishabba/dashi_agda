# PR #1242 max-cut: S1 field/force metrology, S6 observability, and complete 20-fibre donor audit

**Input contract update:** submission-to-review now also demands `polarity_factorial_verified` and `ambient_field_reference_verified` metadata booleans. Like all declared control flags, these are **not proof** of control execution. The S1 script's local self-test separately calls the original `psychotronics_field_loom_coils.loop_b` for a 1 mm centered finite-difference independent consistency comparison with the analytic axial gradient. The illustrative JSON below deliberately omits the new flags, so it remains `unverified` rather than silently implying actual measurements.



**24 October 2026 · source-typed, implementation-backed revision.** Engineering analysis and synthetic tests, **no hardware**, no new gravity result, no independent scientific replication, no Agda/CI. Entry points: [force/metrology analyser](../../scripts/psychotronics_field_loom_metrology.py), [two-coil observability analyser](../../scripts/psychotronics_field_loom_observability.py), existing [coil Biot–Savart simulator](../../scripts/psychotronics_field_loom_coils.py) and [existing exact-rank owner](../../scripts/psychotronics_design_rank_audit.py).

## Hard S1 gain: field is not force; motion is not antigravity

For the **previous PR's illustrative** two separated circular coils (radius and separation `a=d=0.1 m`, `N=100` turns each, `I=1 A`), a direct axial thin-wire calculation gives

```text
Helmholtz midpoint Bz                     = +8.99176285573e-4 T
anti-Helmholtz midpoint Bz                 = 0 T (ideal symmetry)
anti-Helmholtz midpoint ∂Bz/∂z             = -1.07901154269e-2 T/m
permanent point-dipole m_z = 0.01 A m²    -> Fz = -1.07901154269e-4 N
mass m_test=1.0 g, local standard g0       -> weight 9.80665e-3 N
|F_dipole| / weight                       = 0.01100285564 (~1.10%)
|m_z| required to match that weight      = 0.90885496698 A m² (ideal gradient)
```

These are **not experimentally grounded magnetic moment, field, weight or levitation measurements**. They are a force budget conditional on a fixed point dipole. An induced moment/linearly susceptible material needs its **own** constitutive model: `F ≈ χ V/(2 μ0) ∇(B²)` for weak isotropic linear susceptibility with negligible demagnetizing corrections, not `m_fixed ∇B` arbitrarily. With an ideal anti-Helmholtz centre `B=0` an induced linear moment and first-order gradient of `B²` vanish. Permanent-dipole static **stability and Earnshaw-type constraints** also need an independent support/feedback design. A moment that can match weight at one point does not imply stable free levitation.

**Independent local cross-check:** Numerical 800-segment Biot–Savart ring integration produced `Bz(0)=8.991762855732019e-4 T` and finite-difference anti-coil gradient `-0.010788964500568298 T/m` (1 mm derivative step), differing by ~0.0107% from the closed-form derivative. This is a *numerical model consistency test*, not external measurement.

## S1 experimental contract: a same-object, blinded force comparison

1. **Original model and instrument identity:** register apparatus ID, exact magnet/coil moment and orientation, sensor serials, revisions, coil winding and location, support/force-balance geometry, measurement frame, source article, signed force/field axes, calibration objects and dates. Changes create new revisions.
2. **Acquisition:** preserve original time-stamped current/voltage/power, Hall/fluxgate three-axis field map, field gradients, force/torque readings, camera tracking, vibration, acoustic, air temperature/flow, heating, magnet temperature, sample position and uncertainty. Raw data and calibration files each get independently recomputable SHA-256. Software hash alone is *not* authenticated instrument provenance.
3. **Factorial and paired discriminators:** use independently controlled coil-current reversal, test-dipole polarity reversal, coil-off/sham, dummy nonmagnetic sample, blinded sensory/noise control, reordering, and at least two independently acquired sessions. A `2 × 2` sign factorial can separate coil-only and dipole-only patterns from the `coil×dipole` ordinary magnetic term; correlated switching can be rank-deficient. Field and visual/thermal/sound cues require separate control (reuse `psychotronics_design_rank_audit.rank_exact`).
4. **Ordinary physical prediction:** for a sufficiently small *permanent* magnetic dipole of independently calibrated moment `m_z`, `ΔF_model = m_z [gradient_active - gradient_sham]` (valid with known fixed orientation and appropriate field geometry). Never apply this to a ferrofluid body, gradient-induced/superconducting moment, nonlinear saturated sample or rotor without rederiving its constitutive force and geometry.
5. **Uncertainty and evaluation:** pair `ΔF_meas - ΔF_model`; include independent readout and moment/gradient uncertainties, correlated calibration uncertainties, systematic force-balance floor and drift. The current script computes a **simple weighted residual with undiluted maximum supplied common systematic floor** and is **not** a complete correlated-error/generalised least squares or statistical-discovery engine. Apparent `residual/σ` is diagnostic only, without look-elsewhere, model discrepancy, registration or independent review.
6. **G-claim firewall:** magnetic `F`, acoustic radiation pressure, EHD ion drift, vibration and thermal effects are not modified `g`, negative effective gravitational coupling or reactionless thrust. Gravity promotion would need an **independent direct gravity observation channel**, source-to-execution same-object weld, independently controlled ordinary-model closure, uncertainty, replication and inspected lab-origin result under the *already owned* `AmyEskridgeAntigravityMeasurementObservationWeldExact`, `AntigravityClaimScopedExperimentalCutExact`, and `AntigravityCalibratedExecutionBridgeExact`. The S1 script NEVER outputs a gravity-validated status.

**Illustrative input for `--record-json` (all quantities in SI):** retain one such pair per block under `pairs` and real file/hash metadata in `metadata`. Metadata booleans are *self-declarations to be independently audited*, not authenticated calibration evidence:

```json
{
  "metadata": {
    "origin": "synthetic",
    "apparatus_id": "DESIGN_ONLY",
    "configuration_revision": "ideal_coils_v1",
    "instrument_serial": "",
    "calibration_revision": "",
    "attributed_original_source": "",
    "model_revision": "dipole_v1",
    "independent_operator": "",
    "preregistered_model_id": "",
    "independent_field_map": false,
    "force_calibration": false,
    "thermal_and_vibration_controls": false,
    "current_power_log": false,
    "blinded_sham": false,
    "independent_replication": false
  },
  "pairs": [{
    "pair_id": "synthetic_pair_1",
    "session_id": "synthetic_session_1",
    "moment_am2": 0.01,
    "moment_std_am2": 0.0001,
    "common_systematic_std_n": 0.000002,
    "active": {
      "force_n": -0.0001079011542688,
      "force_std_n": 0.000001,
      "gradient_t_m": -0.0107901154269,
      "gradient_std_t_m": 0.0001
    },
    "sham": {
      "force_n": 0,
      "force_std_n": 0.000001,
      "gradient_t_m": 0,
      "gradient_std_t_m": 0.0001
    }
  }]
}
```

For non-synthetic `origin = "instrument"`, provide valid, accessible `raw_data_file`, `raw_data_sha256`, `calibration_file`, `calibration_sha256`, filled identity/protocol fields and independent checks. The script checks byte hashes and completeness, *not* authenticity of underlying measurements. Four pairs/two session labels are merely an illustrative minimum gate, **not a justified statistical power calculation**. The output `submission_ready_for_independent_metrology_review` is only a dossier intake flag: never a confirmed experiment, source authorisation, calibration, independent replication or force discovery.

### S6 pre-build observability and control debt

The new `psychotronics_field_loom_observability.py` reuses the *actual existing two-coil* `loop_b` producer, sampling the ideal 3×3×3 site cube `x,y,z ∈ {-0.015,0,0.015} m`. The linear sensor matrix maps **two independently controlled coil currents** to measured field components. Local numeric outputs:

| Sensor layout | Measurement rows | Model response rank | Condition number (nonzero singular values) | Consequence |
|---|---:|---:|---:|---|
| Nine sensors on centre z=0 plane, Bz only | 9 | **1** | Singular/infinite | Two independent coil currents indistinguishable by symmetry at this plane |
| 27 spatial sensors, Bz only | 27 | **2** | ≈6.65 | Both currents theoretically identifiable under ideal calibration, not 27 freely programmed Bz values |
| 27 spatial three-axis sensors | 81 | **2** | ≈5.50 | More independent observations and better numerical conditioning, still only two actuation DOFs |

No material permeability, ferromagnetism, sensing noise, thermal drift, winding error, saturation or nearby steel is included; conditioning is units- and noise-model dependent. The response rank is numerical with an explicit tolerance, not a proof of field-equation controllability or real hardware identifiability. **Actual rank can deteriorate.**

**Decisive cross-pollination:** W. N. McCasland, *Fault-tolerant sensor and actuator selection for control of flexible structures*, 1989 American Control Conference, vol.2, pp.1111–1116, NASA bibliographic abstract [A89-54007](https://ntrs.nasa.gov/api/citations/19900016740/downloads/19900016740.pdf), originally studies controllability/observability Gramians and failure-tolerant placement. **His original contribution remains his**; our finite static-response audit is a bounded analogous design problem, **not his theorem applied unchanged**. Next S6 donor: fault-aware design of coils/sensors over documented field response matrix, noisy calibration and failures. E.g. optimise smallest singular value under one failed sensor/coil, rather than counting site symbols. Second donor: Zhiwen Ren, Hao-Wen Dong, Mingji Chen, Haiou Yang, Yue-Sheng Wang, Li Cheng, **Daining Fang** (original [2025 Journal of the Mechanics and Physics of Solids 200 106144](https://doi.org/10.1016/j.jmps.2025.106144)) for **elastic-wave mode inverse design**; it does not establish an arbitrary Maxwell B field or supersede acoustics experiments.

### Four-sensor fault-tolerant S6 placement (implemented follow-on)

`psychotronics_field_loom_observability.py` now additionally evaluates all **27 choose 4 = 17,550** distinct four-site Bz sensor subsets, and for each simulates loss of **any one** of those sensors. It maximises the **minimum surviving two-coil response singular value** under a common, idealised equal-noise assumption (a bounded implementation *inspired by*, but distinct from, McCasland's 1989 dynamic Gramian approach).

The chosen tied/symmetric maximin layout puts two sensors on the lower plane `z=−0.015 m` at `(x,y)=(-.015,-.015),(-.015,+.015)`, and two on upper `z=+.015 m` at the same `(x,y)` values. Every single-sensor failure leaves an ideal **rank-two** three-row response; worst surviving smallest singular value ≈`1.95463×10⁻⁴ T/A`, worst condition number ≈`5.66`. This **does not** show four sensors universally sufficient: independent failures, actual magnetometer noise/correlation, ambient fields, sensor placement tolerance, electronics, shielding, currents and material responses remain missing, and the selection is only optimal *on the 27 listed grid points under the chosen maximin objective*. This is a concrete prebuild/sensor-placement deliverable, **not a constructed 27-site field fabric**.

## Full 20-fibre source-owned scientific-capability audit

**Denominator:** exactly the 20 `ScientistTechnologyFibre` entries in pre-existing `DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda`, **not** every person in news reports, not twenty common-programme collaborators, not twenty independently validated experimental methods. Technical-to-instrument transfers are *new original DASHI design hypotheses*, not historical source facts.

| Science fibre, original-owner domain | Application/experimental donor for Field Loom | Prioritisation / scope ceiling |
|---|---|---|
| **Nuno F. G. Loureiro** — KREHM/KRMHD Fourier–Hermite reconnection and kinetic plasma numerics | Model diagnostics **only if regime is within physical closure**; optional future magnetised plasma simulation | Medium conditional; room-air PAW plasma is not automatically a reduced fusion-kinetic system |
| **Joshua LeBlanc** — NASA fission I&C qualification | Sensors → estimation → protection → fault injection/interlocks, high-reliability workflow | **High S1/S3** as engineering pattern, not flight qualification |
| **Frank Maiwald** — cryogenic tagged-ion action spectroscopy | Precise instrument/spectrum calibration and false-positive methodology | Medium analytic donor; no claim this apparatus measures PAW nitrate/peroxide |
| **Monica Jacinto/Reza** — oxygen-service nickel superalloys | Source-derived corrosion/high-temperature qualification requirements | Medium S3 after reactor material requirements specified |
| **Carl Grillmair** — stellar stream matched filters | Detector noise, selection effects, weak-signal false-discovery controls | Medium metrology/inference, not magnetic actuation |
| **Michael Hicks** — asteroid photometry/spectrophotometry | Observation geometry and exposure/illumination calibration | Lower direct utility; optics methodology only |
| **William Neil McCasland** — original 1989 sensor/actuator selection and Gramians | **S1/S6 sensor layout, failure-tolerant identifiability** | **High immediate**; confirmed 1989 bibliographic receipt; implementation uses rank and not original Gramian theorem |
| **Anthony Chavez** — DARHT/Scorpius | Generic measured-system forward/inverse and detector calibration approach | Medium; no acceleration/radiographic hazardous hardware proposed |
| **Jason Thomas** — signalling and chemical biology | Orthogonal objective assay controls if future qualified chemistry study is justified | Later/low; no human efficacy promotion |
| **Amy Eskridge** — historical antigravity programme and original presentation | Attribution-aware mechanism classification and hypothesis-specific negative-control design | **High G/H**, no attribution of Li/Torr/Podkletnov/POAMS to Amy |
| **Ning Li** — superconductor gravito-EM theory/experimental claims | Ordinary magnetic/GR predictions, cryogenic controls, source-vs-constitutive hypotheses | **High G** only with qualified gravity metrology, not first hardware build |
| **Chen Shuming** — graph-based processor/hardware verification | Future readout-board fault and design verification | Medium downstream; no assumed chip provenance |
| **Feng Yanghe** — Bayesian/noisy-label decision methods | Contaminated or partial sensor-label analysis only | Lower, no wargame content imported into civilian apparatus |
| **Zhou Guangyuan** — low-shrinkage polyimide aerogels | Insulation/mount vibration and thermal management when specs support it | Medium future S3; reported material ≠ qualified part |
| **Liu Donghao** — DSMM data-lifecycle management | Run/raw/calibration file provenance, retention and access controls | **High cross-cutting** data audit pattern, not certified DSMM implementation |
| **Zhang Xiaoxin** — space weather and geomagnetic disturbance analysis | Field baseline/drift/environmental magnetometer reference; match local noise scales | Medium S1 calibration; distinguish space-weather source from lab coil signal |
| **Zhang Daibing** — UAV localisation/path following | Multi-sensor tracking/actuation reliability donor | Medium S6 analogy; not aircraft autonomy or safety approval |
| **Li Minyong** — fluorescence probes/photopharmacology | Optical assay design donor only if relevant chemical target is selected | Later, no drug/human experiments |
| **Daining Fang** — source-owned elastic-metamaterial inverse-mode design | Acoustic/elastic mounting modal optimisation for S2 and active vibration rejection | **High S2**, specific original coauthored paper; not arbitrary EM/gravity design |
| **Yan Hong** — high-speed inlet thermal excitation | Thermal-flow disturbance diagnosis under regime-appropriate lab conditions | Low near-term; high-speed aerodynamic mechanisms do not automatically transfer to water |

**Human-event firewall:** selection of a useful contribution is never evidence of covert collaboration, cause of death/disappearance, shared laboratory/contractor, experimental suppression, motive, or criminal act. Preserve original person, source, author, DOI, publication date and original-vs-summary level. Institutional record, reported statements and source-written Agda do not imply kernel verification or the observed claimed physical result.

## Reassigned Pareto/phase gates

| Gate | Already paid at PR #1242 | **Actual next payment** |
|---|---|---|
| H0 | Contemporary Soviet/Czech primary source genealogy and first-person Kitaygorodsky 1974 | Exact original Pavlita/Jana 1973 apparatus text/1975 experimental body only via legally accessible source; archive/copy restriction is an access wall, not a proof obligation discharged by web searching |
| G0 | Amy main historical mechanics and source-specific physics consumers | Same-apparatus, same-exact-observable experimental source and calibrated comparison, NOT another generic theorem |
| **S1a** | Ideal field, force budget and source-hashed paired analysis protocol **implemented, synthetic tests run locally** | Real Hall/current-force-sensor calibrated time series and uncertainty, stable apparatus identity, controls; no existing instrument supplied |
| **S1b** | Equal/anti coil geometric consistency and paired residual | Independent qualified force-balance/ambient-control and repeatability; avoid induced-permanent moment conflation |
| **S2** | Published PMUT/EWOD component demonstrations, Fang elastic-mode design inspiration | Qualified acoustic chip, characterized pressure fields/particle trajectories, engineering safety, cross-talk tests |
| **S3** | Source-specific PAW isotope/chemistry/energy donors and safety mode gates | Enclosed qualified reactor, calibrated chemistry assay and gas/power measurements; no human ingestion or exposure |
| **S6 preflight** | Explicit response-matrix rank **implemented and synthetic local checked** | Noise-weighted sensor/coil placement optimisation with fault scenarios and actual calibrated winding map, **before** 27-actuator hardware design |
| I source/evidence | Full 20-fibre survey reusing existing source-owned science and negative controls | No new work-linked event attribution; only exact source-limited empirical investigations with matched controls if separately justified |

**Verification receipts**: two new repo Python files were composed and local equivalents executed in this session; metrology self-test passed; separate 800-segment ring numerical cross-check agreed with analytic `dB/dz` to ~0.0107%; ideal two-coil observability rank 1→2→2 at 9/27/81 measurement rows with reported ideal condition numbers. Repository paths must be read back after commit. **No checkout of the actual GitHub blob was executed locally** (restricted container network), no Agda/CI, no hardware or externally authenticated raw dataset.

## Source-role anchors, not independent experiment counts

- [Amy original HAL5 presentation/programme (2018)](https://www.hal5.org/program-2018-12.shtml), historical author and conference-carrier. Her deck is not the original Li/Torr experiment or R. H. Eskridge NASA TM.
- [NASA 2021 POAMS TM 20205010911](https://ntrs.nasa.gov/citations/20205010911), authors R. H. Eskridge, M. A. Nelson and M. P. Schoenfeld; explicitly preliminary.
- [Li & Torr 1991](https://doi.org/10.1103/PhysRevD.43.457) and [1992](https://doi.org/10.1103/PhysRevB.46.5489): original theoretical authors and distinct theory objects.
- [Podkletnov & Nieminen 1992](https://doi.org/10.1016/0921-4534(92)90055-H): author-reported 0.05–0.3% apparent weight reduction, not accepted independent gravity screening.
- [Graham et al. 2008](https://doi.org/10.1016/j.physc.2007.11.011): specific null frame dragging and quantitative predicted-effect bound in lead; no universal no-go.
- [Tajmar, Kößling & Neunzig 2024](https://doi.org/10.1038/s41598-024-70286-w): steady-field high-sensitivity nulls including coils; not an exhaustively dynamic experiment.
- [Ianconescu, Sohar & Mudrik 2011](https://doi.org/10.1016/j.elstat.2011.07.004): measured ion-wind comparator for asymmetric capacitors.
- [Berry & Geim 1997](https://doi.org/10.1088/0143-0807/18/4/012): conventional diamagnetism; **counterforce** not shielding.
- [Vuille-dit-Bille et al. 2025](https://doi.org/10.1039/D5LC00747J): experimental acoustofluidic particle control, not macro levitation.
- [McCasland 1989 ACC paper NASA bibliographic index](https://ntrs.nasa.gov/api/citations/19900016740/downloads/19900016740.pdf): source-authored actuator/sensor fault-tolerant placement.
- [Ren, Dong, Chen, Yang, Wang, Cheng & Fang 2025](https://doi.org/10.1016/j.jmps.2025.106144): original elastic-metamaterial inverse design, a different field from Maxwell gravity.
- [Geoscience Australia geomagnetic observatories](https://www.ga.gov.au/education/natural-hazards/space-weather): independent reference on baseline drift and 3-axis magnetic calibration; not a Zhang-Xiaoxin coauthored result.

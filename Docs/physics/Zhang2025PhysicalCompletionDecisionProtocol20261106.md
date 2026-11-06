# Zhang/Pais exotic-gravity programme: experimental completion and physical implications

**Scope:** implementation-ready research protocol linked to PR #1468 source/measurement consumers. Date: 2026-11-06. **NOT** a claim that a device or an experiment has been performed. No high-voltage/cryogenic/vacuum build guidance; a qualified laboratory must approve apparatus and electrical/vacuum safety before operation.

## Objective and mutually independent outcomes

- **O1 Reproduced motion**: exact source identity + calibrated motion/force/torque, reproducible controls. Does not establish gravitation.
- **O2 New force law**: ON/OFF residual that survives predeclared Maxwell+matter+mechanical/thermal/measurement controls, independent replication, context-specific scaling. Does not by itself establish modified gravity.
- **O3 Gravitational/metric response**: independently sensed external test mass, free fall, clock or optical response, same source geometry and derived physical stress, conventional GR comparator and new theory with physically falsifiable divergence.
- **O4 Engineering utility**: independent performance target (force, force density, torque, efficiency, power, heat, repeatability, safety, cost), irrespective of O2/O3.
- **O5 Theory-wide claim**: gauge/diffeomorphism-consistent action, energy-momentum conservation, causal propagation, correct units, reduction/regularity/known-gravity tests and successfully predicted held-out data. Do not infer from O1/O2 alone.

Pursue O1/O4 and O2/O3 as **parallel outcomes**. Negative results can pay a specified *regime-indexed* bound and scientific publication, not universal impossibility.

## Select one real device object, never silently combine

- A: Zhang/Xiao/Li patent US12417870B1 / CN119943525A high-voltage vacuum-vessel suspended sphere.
- B: Zhang/Xu 2025 toroid with reported 18 mm gap, 50 Hz nominal source and six differently sized materials.
- C: Pais US10322827B2 proposed acoustic/charged-cavity high-frequency gravitational-wave source.

**First scientific selection: B** as the published toroidal geometry with six material tests and the most direct external steady-toroid controls. Do not directly construct A's high-voltage device from a patent. A and C receive different prediction and observation channels and require distinct safety reviews and apparatus receipts.

Author-provided source report: https://papers.ssrn.com/sol3/papers.cfm?abstract_id=5389995
Independent 2024 steady-field paper: https://doi.org/10.1038/s41598-024-70286-w
Independent 2026 toroidal DC paper: https://doi.org/10.1142/S0217751X26501472

## Gate G0: legally/technically acquire actual source data

For B, request: original continuous source-frame videos with calibrated scale/clock; run timestamps; blinded ON/OFF labels; exact sample masses, shapes, dimensions, charge/dielectric susceptibility; support/thread length, stiffness/damping, initial displacement; measured B(x,t), E(x,t), source waveforms, input current/voltage and real power; coil/core magnetic B-H and hysteresis, temperature and excitation duty; gas pressure, air-flow, humidity; vibration on multiple axes; sensor and calibration metadata; independent original raw file hashes and device ID.

A published image or transcript can be a documentary claim but is not its raw sensor receipt. An account by the same authors is not independent replication.

**Gate passes** only with sample-by-sample raw run identifiers, calibration, metadata and fit-for-purpose uncertainty or a separate ground-truth lab measurement. If the above cannot be obtained, preregister an independent experiment rather than impute missing values.

## Gate G1: source-conserved physics and prediction

For a selected physical configuration and a fixed convention, solve/approximate the following jointly, with measured time-dependent constitutive laws:

1. Maxwell: \(\nabla\cdot B=0,\quad \nabla\times E=-\partial_t B,\quad\nabla\times H=J_f+\partial_t D\).
2. Material: nonlinear/hysteretic \(B(H,\mathbf x,t,T)\), measured or uncertainty-bounded \(\epsilon,\chi,\sigma\), surface/triboelectric charge and polarisation of each material, induced currents.
3. Matter/mechanics: sample translation/rotation, suspension restoring forces, mechanical vibration, magnetic forces, dielectric forces, air/buoyancy, outgassing, temperature, optical tracking and RF pickup.
4. Poynting/mechanical stress and power/impulse: chosen complete apparatus boundary, measured input real/reactive/stored energy; account for source coupling, shield, support and room. Test the divergence/flux accounting for total stress. Finite-element/ODE simulation is an auditable hypothesis, not an assertion of physical closure.
5. Emit\(\widehat F_{\rm ordinary}(t,\mathbf x,m,\text{material},\text{waveform})\) and bounded model discrepancy with no nuisance silently set to zero.

The *assumed sinusoid* 50 Hz, 0.1–0.5 T input supports an illustrative \(\max|\partial_t B|\approx31\text{–}157\,{\rm T/s}\); this is NOT measured B(t). The reported gap alone cannot supply field gradients.

**Key mathematical discriminator:** the Zhang/Xu 2025 equation
\[
\nabla\times\mathbf G=-\alpha\,\partial_t\mathbf B
\]
and Faraday's law imply
\[
\nabla\times(\mathbf G-\alpha\mathbf E)=0 .
\]
On a simply connected domain, \(\mathbf G=\alpha\mathbf E+\nabla\phi\), with \(\phi\) left unspecified. Therefore this *curl equation alone* does not fix an acceleration field or predict an independently measurable gravitational metric. \(\alpha\)'s dimensions must be supplied before numerical comparison. This **does not prove** that \(\mathbf G\) is electric or that no extension exists; it identifies an underdetermined model and a close ordinary-EM discriminator. A complete gravitational producer must add source/constraint/boundary equations and give a new external test-mass, free-fall or metric readout unlike electric-force coupling. Merely observing rate dependence is insufficient: standard induction also depends on \(\partial_t B\).

## Gate G2: blinded predeclared physical experiment

A qualified independent laboratory designs the device; this document intentionally does not provide high-voltage construction steps.

- Predeclare H0 (ordinary Maxwell+mechanics), H1 (additional source-specific force), H2 (gravitational metric / free-fall effect); their non-overlapping predictions, discovery endpoint, detector bandwidth and minimum physically interesting \(\delta_{\min}\).
- Randomise independent paired ON/OFF blocks, sham source-drive controls matched for heat and vibration, blinded video analysis, hold-out sessions, power/temperature logging, reverse drive polarity, source frequency/ramp-rate sweep, sample position/rotation and mass/material contrasts.
- Maintain real E and B near the target. Electric shielding does not automatically eliminate low-frequency magnetic gradients. Monitor material magnetism, dipoles and hidden residual charge.
- Include a source-off residual decay experiment, but post-switch rotation alone can be mechanical inertia; decompose impulse, continuous force and damping.
- Each statistical unit is an **independent experimental block**, not each video frame; handle time dependence and autocorrelation.
- Use an explicit measurement function for \(x(t),\theta(t)\) and their calibrated derivative uncertainties; do not treat visual motion as a Newtonian force without a calibrated dynamical model.

**Preregistered estimand:**
\[
\Delta_F=\mathbb E[F_{\rm ON}-F_{\rm OFF}
 -(F^{\rm ordinary}_{\rm ON}-F^{\rm ordinary}_{\rm OFF})] .
\]
Use intervals or hierarchical uncertainty propagated from both measurement and ordinary model. If bounded IID paired observations \(d_i\in[a,b]\) are justified, the existing Python Hoeffding compiler gives a conditional CI for the mean; otherwise use an identified dependent-data / block-bootstrap or design-based model and explicit systematic bounds. Pilot \(\sigma_d\) determines the number of independent blocks for a target power: a normal approximation for two-sided \(\alpha\), power \(1-\beta\) gives \(n\gtrsim(z_{1-\alpha/2}+z_{1-\beta})^2\sigma_d^2/\delta_{\min}^2\), subject to empirical design calibration. An illustrative high-significance threshold is **not** a proof of correct physics if systematics, model selection or multiplicity are unresolved.

**Decision if H0 remains compatible:** report the specific frequency/current/material force-interval upper bounds and evaluate conventional engineering performance. Do NOT declare universal gravity impossible.

**Decision if reproducible residual:** publish raw/blinded records, hold-out analysis and independent laboratory reproduction, then move to G3. This is an unexplained force, not yet a gravitational observation.

## Gate G3: multi-consumer physical and model discrimination

A candidate real gravitational source must predict a joint consequence of one selected total stress tensor and geometry:
\[
T_{\mu\nu}^{\rm full}\longrightarrow g_{\mu\nu}\longrightarrow
\left(\Delta a_{\rm ext},\Delta a_{\rm ff},\Delta\nu/\nu,\Delta\theta_{\rm opt}\right).
\]

- External test mass: independent, electrically/magnetically isolated sensing with measured leakage bounds. Electric shielding alone is not decisive for 50 Hz B.
- Free fall: distinguish changes in natural free fall from material-specific Lorentz, dielectric, buoyancy or magnetic forces. Measure mass/charge/composition dependence on the same source.
- Metric/clock/optical: for weak static conservative metric assumptions, check redshift \(\Delta\nu/\nu\simeq\Delta\Phi/c^2\), and jointly predicted acceleration \(\mathbf a\simeq-\nabla\Phi\). A vector/scalar alternative must present its own distinct source-consistent predictions; redshift cannot be inferred from force alone.
- Propagating TT gravitational waves: only for Pais/GW hypotheses, independently test quadrupolar TT far-field waveform, propagation, polarisation and conservation; never from local object motion.
- Change source location/geometry; test spatial decay and exterior response. Identify and subtract ordinary current loops, apparatus mass displacement and moving cables/optics.
- Repeat at second independent facility with new source hardware and independent instruments; keep identical protocol/version and crosswalk hashes.

**G3 pass** requires physically distinct external measurement channels consistent with one model, explicit ordinary-GR and alternative-model predictions, uncertainty-qualified held-out tests, and independent replication. A new force that violates weak equivalence is possible in physics, but it should be classified as an additional interaction unless evidence specifically supports a changed metric.

## Gate G4: downstream existing DASHI proof consumers

| Exact owner | Admissible input now | Remaining constructor to inhabit |
|---|---|---|
| `Zhang2025EMGravityQuantitativeSourceExact` | original nominal source, external 2024 3σ screens and 2026 DC resolution | no first-party acceleration outcome yet |
| `check_zhang2025_quantitative_consumers.py` | models, sample masses, conditional CI and material-acceleration interval screen | real calibrated repeat-level outcome files |
| `AntigravityLaboratoryBackgroundClosureExact` | nuisance schema for EM, vibration, thermal, RF | matched real background receipts |
| `AntigravityClaimTheoryComparisonExact` | typed ordinary-vs-modified comparator | exact *same-observation* predictions and residuals |
| `AntigravityExperimentalCutProvenanceExact` | original per-run hashes, calibration/identity requirements | actual source/phase/model/scaling/replication bundle receipts |
| `Zhang2025EMGravityPhysicalPromotionExact` | canonical external screens; physical compiler from existing provenance receipt | `ProvenancedComparativeAnomalyReceipt claim` for this selected device |
| `AntigravityStrongestConditionalTheoremExact` | frozen sign/scope theorem | *additional* measured constitutive-negative-G receipt and remote comparative anomaly |
| open local-C / CMP119 #1120 | typed stress-to-metric and multi-channel conditional compiler | real same-source stress, calibrated physical scale, matching metric and channels |
| open KK #1241, Lorentz/observer #1460 | alternative 5D/4D source/action consumers | selected full stable action and measured geometry weld |
| Pais #1256, controlled EM/GW #1099 | source-first TT/HFGW and energy exchange | conserved apparatus stress and independent GW detection |

**Do not** use external Dresden null measurements as if they were Zhang apparatus runs. Those results calibrate an *external-regime comparator*, not a first-party anomaly. No current source supplies \(\omega_{\rm obs}(A^*B)\) or selected YM/OS metric identities merely by observing a force.

## G5: consequential real-world implications and their thresholds

**Case A — conventional electromagnetism accounts for reproducible motion.** The result is a calibrated EM/material actuator. Evaluate useful force/mass/power/bandwidth, wear, device complexity and comparison with existing electrostatic/magnetic actuators. No antigravity or spacetime-modification claims.

**Case B — no controlled motion survives.** Publish source-specific upper limits, ruled-out model parameters in that regime, validated calibration hardware and software; negative results can be valuable to precision metrology and replication methodology.

**Case C — reproduced force residual, no external gravitational/metric effect.** A potential additional force/constitutive mechanism merits physics follow-up; prove energy and momentum conservation and check known force laws, but **do not call it antigravity**.

**Case D — reproducible, independently observed gravitational/metric response with a coherent theory.** This would motivate substantial fundamental-physics tests against GR, equivalence-principle bounds, conservation, weak-field astrophysical tests, energy sourcing and stability; claims of practical gravity engineering require a separate technology demonstration.

**Engineering performance gates regardless of mechanism:** measured thrust/force/torque per input real watt; source duty/range/mass/volume; field outside device; thrust after blank/shield tests; thermal and acoustic costs; safety; repeatability; sensitivity to ambient conditions; quantitative error-budget and cross-facility reliability. A force signal that is real need not have useful net propulsive impulse or lift.

## Exact next actions

1. Publish a source request for original per-run videos and field/current/temperature/mass calibration for **one** B-type Zhang toroid. Use original paper author channel and cite exact date/apparatus ID; no inference from nonresponse.
2. Freeze this protocol, select the metric and force targets and plausible detection limits *before* acquiring new outcome data.
3. Audit the existing 2024/2026 reference-data provenance; resolve which ± values are per-run σ versus estimator SE; keep their current 3σ **screening** and resolution labels until paid.
4. Implement and unit-check measured-geometry Maxwell/material + suspension simulation and an observable dictionary **before** declaring any new interaction.
5. Secure an independent calibrated laboratory with an electrical safety review; complete a blinded small pilot; estimate \(\sigma_d\), systematic uncertainty and reachable minimum detectable effect.
6. Run preregistered independent blocks and release the bounded source-specific residual with raw hashes and model uncertainty.
7. Only if a reproducible residual is present, fund physical gravitational-source tests and a second independent hardware replication; then instantiate terminal DASHI physical receipts rather than assigning arbitrary values.
8. In parallel, maintain an engineering-performance ledger so a reproducible conventional actuator can become an immediately useful result.

**Acceptance:** no physical-promotion flag may be true unless its exact sample/run identity, measured observable, uncertainty, ordinary-model closure, independent evidence and source-to-prediction mapping are supplied. Kernel checking validates implication structure, not truth of empirical premises.

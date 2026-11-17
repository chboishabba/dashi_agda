# Smith/Filsinger — five-gate original evidence acceptance (17 November 2026)

## Scope and result

The user requests closure of **F10 physical Maxwell→original terminal**, **original raw metering and uncertainty certificates**, **F15 sustained independent natural work**, **F16 atmospheric causality**, and **D1 genuine Agda kernel acceptance**.

**Current result: 0/24 original evidence roles provided by the locally available source-first archive. No physical or kernel gate can responsibly be marked CLOSED.** This is NOT a statement that the device is impossible; it is a strict absence-of-confirming-evidence result. All prior conditional exact energy algebra and model checks remain useful but must not be substituted for the original device's source, control, or weather observations.

The new `scripts/check_smith_filsinger_original_gate_evidence.py` checks byte integrity, common original ID, role, clock and traceability; `scripts/test_smith_filsinger_original_gate_evidence.py` supplies 10 adversarial regressions. The tool is **fail-closed and can only issue READY_FOR_INDEPENDENT_REVIEW_NOT_CLOSED**, even for a syntactically complete manifest. Hash-matched files are not authenticated instruments or independent causal proofs.

### F10 — Maxwell → actual original terminal calibration (6 roles, all absent)

`original_pins`, `geometry_material`, `source_current`, `field_flux`, `ground_return`, `signed_terminal_vi`.

Required scientific weld: the chosen original source/receiver/ground boundary, calibrated E and H field/geometry/normals and material current, time-aligned measurement, Poynting flux with outgoing radiation and internal stored field energy, and the same source's separately measured signed electrical work `∫V(t)I(t)dt` in SI joules. A symbolic full-vector pointwise identity or an elliptic Green function alone is NOT an original Maxwell field solution, physically integrated surface flux, source-current observation or calibrated terminal equality.

### METER — real original readings and rigorous error (3 roles, all absent)

`instrument_calibration`, `synchronous_port_work`, `signed_error_bounds`.

Require original traces with known instrument/clock/source provenance, bandwidth, phase delay, probe loading, signed current orientation, sampling and integration window; actual calibration and *two-sided* propagated uncertainty with appropriate coverage and covariance. Existing formal certified signed rational residual and finite-sum bounds cannot produce numerical error bounds without independent original calibration. A measured audio spectrogram cannot stand in for electrical V/I phase or watts.

### F15 — sustained independent natural energy (5 roles, all absent)

`natural_source_independence`, `controller_work`, `load_work`, `all_storage_return`, `full_loss_and_return`.

Require repeatable identical source-controlled cycles, all controller/modulator input, natural incident **and outgoing** work, useful load, thermal/chemical/ionization/near-field radiation, all batteries, capacitors, inductors, ferromagnetic, thermal and charged medium storage, and independent environmental-source replenishment. The signed ledger must allow net environmental **sink** (outgoing > incoming), as already proved in the same PR. A useful load > zero, coherent response, unexplained current or reactive circulation is insufficient. In particular require a lower confidence bound for naturally supplied NET real work strictly > 0 under full-storage return with independent source identity.

### F16 — weather/cloud/rain/cooling causality (6 roles, all absent)

`preregistered_intervention`, `random_assignment`, `sham_control`, `cloud_rain_outcome`, `meteorological_covariates`, `replicated_site`.

Require the proposed actuator's delivered atmospheric electric-field perturbation, preregistered randomized intervention and sham/control design, blinded or instrumented outcome, local meteorology/upwind/downwind confounder measurements, negative controls and independent replication. A source→cloud correlation, rain occurring after operation or a statement about natural global electric circuit coupling cannot determine a causal treatment effect. Even passing these inventory roles establishes only review readiness; causal identification, effect-size uncertainty and independent replication must be evaluated.

### D1 — compiler and kernel acceptance (4 roles, all absent as of audit)

`agda_source_commit`, `pinned_toolchain`, `kernel_exit_receipt`, `complete_kernel_log`.

A new `.github/workflows/filsinger-agda29-acceptance.yml` uses the repository's Nix-locked Agda 2.9 compiler target and calls the existing focused Agda formal checker on PRs. It preserves logs and tests the source-evidence fail-closed harness first. The OLD `.github/workflows/ci.yml` is manual-only and selects Agda 2.6.4.3; it cannot validate these new sources as Agda 2.9. No run status was present when this document was authored. **The stdlib experimental branch in the existing runner is not a fixed commit: freeze it for reproducible exact D1 acceptance.** Likewise exact-head compiler/stdlib hashes and successful complete target logs are mandatory. A PR's mergeability is not an Agda result.

## Executable audit

Run from the repository root:

```sh
python3 scripts/test_smith_filsinger_original_gate_evidence.py
python3 scripts/check_smith_filsinger_original_gate_evidence.py PATH/TO/original_manifest.json --root PATH/TO/raw_evidence --out PATH/TO/gates.json
bash scripts/check_smith_filsinger_formal_weld_agda29.sh
```

`original_manifest.json` is a source-specific object with `original_id` and `records`. Each record supplies one unique `role`, identical `original_id`, `kind` (raw_measurement / independent_certificate / pinned_kernel_receipt / instrument_document), `producer`, `clock_id`, relative `file` within the data root and SHA-256 of the actual bytes. The Python checker rejects model/proxy/conditional theorem receipts, absent raw files, wrong original or mismatched hashes. A complete manifest is **not proof** of correctness. Do not use fabricated values to make the CLI pass.

## Source-first reuse and next proof cut

Reuse the existing KSW668 pointwise full-vector Poynting theorem, indexed signed face incidence/Stokes, finite rational spacetime telescope, signed source/receiver work, signed controller-paid environmental sink, and canonical proof-carrying finite-sum error bounds; **no simulated model is promoted to physical admission**. The remaining work is obtaining actual original physical evidence and a real Agda kernel receipt, not adding empty Set-shaped evidence labels. No ESD modifications or unsupported TOE promotion.

Sources: original programme's [PR #1524](https://github.com/chboishabba/dashi_agda/pull/1524), `Docs/research/SmithFilsingerMaxwellValueAndSourceFirstCut20261117.md` and canonical `Docs/research/SmithFilsingerFormalWeldMaxCut20261117.md`.


## Continuation — independent-role evidence and exact signed V/I integrator

Implemented `scripts/check_smith_filsinger_signed_vi_intervals.py` and `scripts/test_smith_filsinger_signed_vi_intervals.py` (13 exact arithmetic / adversarial fixtures). This is a **data reader**, not simulated physics: five separately hashed raw port CSV channels (`natural_incident`, `natural_outgoing`, `controller_incident`, `controller_outgoing`, `load_output`) must share the exact physical original ID, sampling clock and all exact rational sample times, using explicit `positive_in_port_direction` convention and a declared `piecewise_linear_power_trapezoid` integration assumption. For each signed V/I sample, exact `Fraction` interval multiplication propagates the supplied voltage/current uncertainty radii, and trapezoidal integration supplies exact rational work intervals. It reports net natural incoming minus outgoing work, net controller incoming minus outgoing work, useful load and the residual **unassigned loss OR storage change**, NOT a fabricated conservation pass. It is explicitly conditional on supplied sample interpolation/aliasing accuracy; true calibration uncertainty and physical provenance are NOT derived from raw CSV.

The original five-gate evidence audit previously had a meaningful weakness: copying one already-hashed artifact into several roles could make all 24 role labels appear present. It now **rejects the same path or identical SHA-256 bytes assigned to different roles**, even if copied under a second filename. Role-specific evidence files or separately hashed extracted channels are required, but that alone is still not proof of scientific independence or calibrated measurement. The corresponding adversarial regression suite is extended from 10 to 12 cases, with role-distinct fixtures for review-readiness tests.

CI `.github/workflows/filsinger-agda29-acceptance.yml` includes both Python test suites before true pinned Agda kernel acceptance. **These are authored CI checks, not an observed successful CI run**. No Agda/Nix binaries are available in this container. F10 original Maxwell port/metric and SI boundary integration, meter sample/bandwidth error validity, F15 all storage returns and independently replenished natural source, F16 controlled atmospheric causality and D1 actual pinned kernel PASS remain OPEN. The port-reader deliberately never sets `physical_claim_closed` or `f15_closed` to true, even when a hypothetical CSV yields a positive conditional source interval.

Run on authentic separately hashed instrument traces only:

```sh
python3 scripts/test_smith_filsinger_original_gate_evidence.py
python3 scripts/test_smith_filsinger_signed_vi_intervals.py
python3 scripts/check_smith_filsinger_signed_vi_intervals.py ORIGINAL_VI_MANIFEST.json --root RAW_ORIGINAL_PORTS --out signed_work_intervals.json
```

The manifest must include `original_id`, `clock_id`, `port_orientation`, `integration_rule` and `ports`. Each port record carries `file`, `sha256`, `clock_id`; each CSV has exactly `time_s,voltage_V,current_A,voltage_error_V,current_error_A`, in SI units. All numerical values are strings parsed as exact decimals or rational fractions. If the original fields lack independent current, time, error radius or source authentication, the input is **not available**; do not fill with guesses or model values.


## Continuation — required independent intersample error certificate

The exact signed V/I interval reader previously propagated instantaneous voltage/current calibration radii but **implicitly set all sub-sample energy error to zero**. This is invalid for original high-frequency/switching/tuned apparatus: a narrow sample-level trapezoidal envelope does not necessarily bound the actual continuous waveform integral.

`scripts/check_smith_filsinger_signed_vi_intervals.py` now requires **three extra per-port evidence fields**: `integration_error_bound_J` (exact nonnegative rational string), `integration_error_certificate` (separate, role-distinct file) and `integration_error_certificate_sha256`. The file's hash and path are checked, and re-use of an earlier port's raw/certificate bytes is rejected. The work interval becomes:

```text
sampled_trapezoidal_work_interval = [L, U]
independently_certified_integral_remainder_radius = ε ≥ 0
admitted_original_integrated_work_interval = [L − ε, U + ε]
```

This is conservative only if the external remainder certificate itself truly bounds the missing integration, inter-channel phase offsets, bandwidth/aliasing and switching transients. A SHA256 match is **not** an assessment of that mathematical/experimental claim. The reader never silently sets the physical remainder to zero: a supplied `0` remains a separately documented, scientifically auditable premise, not a derived physical fact.

Added five new negative-control/exact-radius tests for nonzero remainder propagation, missing certificate, wrong certificate hash, negative remainder and copied certificate. V/I test suite now has **18 authored test cases**, evidence-role suite has **12 authored test cases**. Both are included in the focused GitHub PR workflow. As of this update neither suite nor pinned Agda 2.9 typechecking has an observed accepted CI run; these are **source-authored tests and reviewable code, not kernel receipts**.

F10 physical calibration, actual instrument uncertainty calibration, F15 independent natural replenishment, F16 controlled atmospheric cause, and D1 actual pinned Agda success all remain OPEN. In particular, calling an unverified channel `natural_incident` does not prove its physical source is natural.


## 17 Nov continuation — conditional same-original Maxwell-to-meter bound weld and alias-error admission

**Source-first proof weld (NOT another Maxwell simulation):** `DASHI/Physics/Motors/SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda` directly consumes the EXISTING `SmithFilsingerSelectedSpaceTimePortWeldExact`, `SmithFilsingerCertifiedSignedMeterTwoSidedExact`, the canonical `ProofCarryingFiniteSumEnclosureExact`, original `KSW668FullVectorMaxwellJetExact` and 4D space-time Poynting owners. Its `OriginalMaxwellMeterIntervalWeld jet b f` record demands a two-sided proof-carrying meter certificate indexed by the **same selected Maxwell `physicalTrace.window`**, preventing a separately chosen meter interval from masquerading as this original apparatus. It authors `originalMaxwellReceiverUpperFromSignedMeter`, `originalMaxwellReceiverLowerFromSignedMeter` and `originalCalibratedPortUpperFromSignedMeter` via equality transport, with no independent aggregate conservation assumption.

**Critical numerical acceptance correction:** the earlier exact-Fraction V/I integrator bounded only pointwise sampled meter calibration and set intersample energy error to zero. Switching and pulsed waveforms make that unsafe. `scripts/check_smith_filsinger_signed_vi_intervals.py` now **requires** `integration_error_bound_J` (nonnegative exact rational string), `integration_error_certificate` (different file from all port CSVs and other certificates), and `integration_error_certificate_sha256` for **each** of the five ports; it changes the trapezoid work interval `[L,U]` to `[L−ε,U+ε]`. This is a conditional data check, not a derivation or scientific validation of ε. An asserted ε=0 is admissible to the parser ONLY with an independently archived certificate, and is not automatically physically justified. Five regression test methods now exercise this gap; V/I suite contains 18 authored tests, evidence-inventory suite contains 12 authored tests.

**D1:** new Agda consumer added to both `owners` and `new_owners` of `scripts/check_smith_filsinger_formal_weld_agda29.sh`. No Agda 2.9 kernel check was executed successfully in this session, and the tests are source-authored rather than observed passing runs. The 2.9 pinned CI route exists in the PR, and should be run before this new module is treated as a theorem. Original Maxwell terminal field calibration F10, actually measured and independently bounded SI work, repeated-source replenishment F15, controlled weather intervention F16 and D1 kernel PASS remain OPEN.

**Pareto next cut:** obtain original clock-synchronous, signed, calibrated instrument traces and validated intersample/phase error certificates; apply the new meter-weld to that selected original `jet/b/f` only; do not infer atmospheric output or unmetered natural supply from a symbolic electromagnetic identity. ESD surfaces unchanged.

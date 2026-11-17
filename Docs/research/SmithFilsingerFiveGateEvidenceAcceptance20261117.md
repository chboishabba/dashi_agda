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


## Further continuation — symmetric original calibrated port bounds and signed environmental sink regression

**Source-first formal improvement**: the existing `SmithFilsingerOriginalMaxwellMeterIntervalWeldExact.agda` now provides `originalCalibratedPortLowerFromSignedMeter`, the missing lower analogue of `originalCalibratedPortUpperFromSignedMeter`. Both use `SelectedOriginalSpaceTimePort.loadIsSameOriginal` to transport the already certified physical receiver bounds to the **same selected original calibrated b/f terminal**, not an independently chosen terminal or new field identity. The result is **source-authored and not Agda-kernel accepted** until pinned D1 actually typechecks all modules.

**Numerical/F15 adversarial improvement**: `check_smith_filsinger_signed_vi_intervals.py` now computes `unassigned_loss_or_storage_change` by folding the existing explicit five-port `ROLE_SIGNS` ledger, not maintaining a competing handwritten balance. It exposes `conditional_environmental_sink_interval` when the upper endpoint of natural incident-minus-outgoing is <0; a `natural`-labelled channel that sends more work OUT than IN is not independently replenishing the apparatus. New `test_reverse_natural_port_is_a_sink_not_independent_supply` checks the negative-control case: sample-only hypothetical natural input 5 J, outgoing 7 J, controller net 1 J and load 2 J gives natural −2 J and unassigned −3 J. This is a regression fixture, **not an original measured source**.

**Execution distinction**: actually ran the two older **locally mounted** source-evidence and original Maxwell/replenishment suites in this session: 10/10 `unittest` and 45/45 selected `pytest` tests passed. These are *not* the latest connected GitHub branch tests. The PR branch now contains 12 source-evidence methods and 19 signed V/I interval methods (31 authored total); none of those exact-head 31 can be claimed PASS without execution. No available local Agda/Nix binaries and no successful exact-head Agda workflow receipt. Thus F10 original field-to-port physical admission, authentic meter calibration and error records, F15 independent sustained natural replenishment, F16 atmospheric causal intervention and D1 kernel acceptance remain OPEN.

**Next Pareto cut:** run the 31 source-authored branch tests on the checked-out PR and fix actual failures; then obtain pinned Agda 2.9 compiler acceptance for the same commit; separately require independently authenticated original electrical/waveform records to instantiate F10/F15. No ESD edits or unsupported TOE promotion.


## 17 Nov F15 follow-up — exact-branch, locally executed restored-cycle first-law discriminator

Reused the existing signed V/I port interval receipt rather than inventing a Maxwell source. Added `scripts/check_smith_filsinger_restored_cycle_intervals.py`, which consumes the previous measured/source-labelled work interval output together with an **independently supplied** (not scientifically authenticated by this script) signed total stored-energy change interval and all dissipative/outgoing-loss interval. The programme's exact first-law discriminator is

`R = natural_net + controller_net − useful_load − independently_supplied_losses − (U_final − U_initial)`.

All operations use standard-library `Fraction` with outward conservative interval arithmetic: if `0 ∉ R`, the asserted complete same-window budget is inconsistent; if `0 ∈ R`, the supplied intervals are merely **compatible**, not sufficient proof of a power source. A `[0,0]` storage-change interval is a *claimed exact* restoration, not proof that original device stores were completely enumerated. A signed negative natural interval is retained as an environmental sink. `f15_closed` and `physical_claim_closed` are always false, including on a mathematically compatible example. The code guards same original ID, same clock, previous interpolation remainder admission, valid ordered rational endpoints, and nonnegative aggregate loss lower bound.

Added `scripts/test_smith_filsinger_restored_cycle_intervals.py` with 12 adversarial exact-rational test methods. **This round actually executed 12/12 PASS** on the local exact source files, and verified the local `git hash-object` identifiers equal the GitHub branch blob hashes:
- consumer `0678622bee219188999ecf1b979b43b22f4bec15`;
- test suite `1197828f45641082f9087c0e597b2b142f42243f`.

Tests cover exact zero residual with F15 still false, environmental sink rejection, stored-energy drawdown falsely implying restoration, conservative uncertainty, wrong original ID, wrong clock, absent integration remainder admission, invalid/reversed intervals, negative physical loss, floating-point endpoints, and incomplete interval endpoints. Both new files are wired into `.github/workflows/filsinger-agda29-acceptance.yml`.

**Acceptance boundary:** these 12 local source-matched passing tests are a verified Python audit, not calibrated original experiment data nor Agda 2.9 kernel acceptance. The 31 previously committed GitHub-branch V/I and role-evidence tests remain unexecuted in this container; no pinned Agda 2.9 run is shown for the exact PR head. Physical F10, authentic metering/calibration, F15 independently replenished natural work, F16 atmospheric intervention and D1 remain OPEN. Do not classify an input merely named `natural` as independent source work without a separately established origin certificate. Original ESD material remains import-only.


## 17 Nov next cut — F15 upstream receipt recomputation + original Maxwell restored-source funding

1. **F15 JSON integrity weld actually tested.** `scripts/check_smith_filsinger_restored_cycle_intervals.py` now REFUSES a bare net-source summary. It requires the upstream exact V/I producer's `signed_balance_from_named_port_role_map = true` and all five independently named `conditional_port_work` interval entries, recomputes natural incident−outgoing, controller incident−outgoing, load, and the unassigned work interval, and requires exact equality with **all four** purported producer summary fields before performing the original loss/storage first-law residual test. This closes the previous danger that an independently edited source/load summary could be accepted as an arithmetic premise. It does **not** authenticate a signed input's physical provenance. The suite now has **17/17 actually locally executed PASS**, and local Git blob identities match the connected PR branch exactly: consumer `831b986ee5857236d61b0474604b399d88436995`, tests `c3c6d1a563779c92ea35f67426e21328938ce917`. Five new adversarial controls cover tampered environmental summary, load, unassigned residual, missing physical port role, missing sign map.
2. **Same-original Agda proof joining, source-authored.** Added `DASHI/Physics/Motors/SmithFilsingerOriginalMaxwellRestoredMeterFundingExact.agda`. Its `restoredSourceFundsSameOriginalMaxwellReceiver` consumes the **same b/f original field/port** both as `OriginalMaxwellMeterIntervalWeld jet b f` and the independently admitted `SignedSourceCycleWeld b f`, then transports the existing Nat `Cycle.workPaidAfterStorageReturns` through the existing additive rational `calibratedWork`, original Maxwell `loadIsSameOriginal`, and the source's same-original load/loss identifications. The conclusion is original Maxwell receiver work plus calibrated original internal loss equals calibrated independently admitted natural work plus calibrated controller input. No secondary conservation equation is stipulated. **This is conditional on an original source admission and cannot establish a physical natural-source replenishment claim.** The named imported field and theorem declarations are present, source has no holes or postulates, and the module is listed in both pinned Agda checker arrays. **Agda kernel ACCEPTANCE NOT RUN / NOT CLAIMED.**
3. **Unchanged physics gates:** F10 Maxwell→original terminal material+field calibration OPEN; authentic electrical measurement and certified intersample/phase errors OPEN; F15 independently replenished original natural net work plus all-store return OPEN; F16 controlled/replicated weather intervention OPEN; D1 pinned full Agda 2.9 kernel PASS OPEN. The existing numerically exact F15 result is a source-linked arithmetic consistency checker only, not experimental validation. Do not derive global energy/climate claims, and do not edit ESD.


## 17 Nov F15 acceptance hardening — mandatory original-file replay

**High-alpha fix:** F15 previously recomputed the claimed five-port net from five JSON intervals, which still permitted a malicious or stale upstream `conditional_port_work` and four summary fields to be edited *consistently*. `scripts/check_smith_filsinger_restored_cycle_intervals.py` now has `analyze_from_original_files`, which calls the original `check_smith_filsinger_signed_vi_intervals.calculate(vi_manifest, vi_root)` against the **raw five V/I CSV files, individual SHA256 identities, calibration/intersample-error certificates and the declared common clock**. It compares every original signed producer field (original ID, clock, port intervals, natural/controller/load net, unassigned sum, and both acceptance flags) with the supplied V/I JSON receipt, rejecting any mismatch **before** applying the independent all-loss/storage first-law interval audit.

The F15 CLI is intentionally fail-closed: `--vi-manifest ORIGINAL_VI_MANIFEST.json --vi-root RAW_ORIGINAL_PORTS` are now mandatory. The old invocation accepting two self-described JSON receipts alone is not an accepted F15 check. This binds arithmetic consistency back to the exact source files, though **hashes and copied certificate text cannot establish meter truth or environmental independence**.

New `scripts/test_smith_filsinger_restored_cycle_raw_replay.py` adds seven adversarial raw-file checks: replay-compatible-but-not-physical, self-consistent forgery of signed port data and summaries, stale raw CSV hashes, wrong original acquisition clock, absent integration-error evidence, mismatched original apparatus and load-only tampering. Included in `.github/workflows/filsinger-agda29-acceptance.yml`. These seven tests are source-authored and **not yet executed in this session**. Previous F15 17/17 locally executed matches its earlier exact commit but must be rerun with changes. D1 pinned Agda kernel acceptance continues to require actual compiler execution; GitHub workflow execution must be confirmed at the exact PR head.

The independent `all_dissipative_and_outgoing_loss_J` and `total_stored_energy_final_minus_initial_J` remain *submitted intervals* (not independently authenticated observations). F10 original Maxwell→terminal calibration, physical error provenance, F15 independently replenished source and fully restored original stores, F16 causal atmospheric experiment, and D1 kernel PASS remain **OPEN**. The proof owners and ESD modules are unchanged.

Reproducible invocation after obtaining authentic original files:

```bash
python3 scripts/test_smith_filsinger_restored_cycle_raw_replay.py
python3 scripts/check_smith_filsinger_signed_vi_intervals.py original_vi_manifest.json --root raw_original_ports --out signed_vi_work.json
python3 scripts/check_smith_filsinger_restored_cycle_intervals.py signed_vi_work.json independent_loss_and_storage.json --vi-manifest original_vi_manifest.json --vi-root raw_original_ports --out first_law_audit.json
```


## 17 November — reproducible D1/Python exact-head acceptance runner

**Execution bottleneck fixed in-repo, not misrepresented as a kernel PASS.** The focused acceptance GitHub workflow had `pull_request`/manual triggers but no observed workflow runs. Added an explicit `push` event for `research/sun-earth-coupled-source-20261116` on SmithFilsinger source/test/workflow changes. An event trigger cannot force Actions to run if the repository/runner policy prevents execution; check actual statuses.

New `scripts/run_smith_filsinger_acceptance.sh` is one reproducible local command. From a CLEAN checkout of the exact branch head:

```sh
bash scripts/run_smith_filsinger_acceptance.sh --python-only
bash scripts/run_smith_filsinger_acceptance.sh --full
```

The runner rejects uncommitted relevant source/test changes, records `git rev-parse HEAD`, executes the four current suites (original evidence inventory, signed V/I exact intervals, restored first-law intervals, original raw-V/I replay), and under `--full` also invokes **the real** `scripts/check_smith_filsinger_formal_weld_agda29.sh` compiler checker on all 41 designated Agda owners. Shell `set -euo pipefail` makes any Python or Agda failure fatal; the previous `acceptance-pass.txt` marker is deleted before work and only recreated when ALL selected checks return zero. The success status is **`PYTHON_ONLY_NO_AGDA_ACCEPTANCE`** or **`ACCEPTED_PYTHON_AND_PINNED_AGDA`**, never an unqualified physical-success flag. Logs/marker are stored in `.filsinger-acceptance/`, and CI uploads them even if the task fails. CI's pinned Agda step now calls this runner `--full`; its initial Python checks remain a quicker fail-fast stage.

**Current truth:** workflow authored and source committed, but no GitHub Actions run has been observed for the exact latest head and Agda/Nix are not available in the current assistant container. Do not claim D1 kernel PASS, nor convert valid Python meter arithmetic into physical F10, independent sustained F15 replenishment, or F16 controlled atmospheric causality. Original experiment/source authentication and all-store return are still required.

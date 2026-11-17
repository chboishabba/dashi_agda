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

# Source-original data acquisition request — Zhang/Xu 2025 experiment

Status: **prepared, not sent**. This is for the actual authors or the official public source contact; it is not a claim that any data exist or have been supplied. Official public guide: https://www.unifiedfield.info/experiment and contact address info@unifiedfield.info, consulted 2026-11-06.

## Draft email (for sender approval)

To: info@unifiedfield.info  
Subject: Request for original calibrated measurement records — Zhang/Xu 2025 changing magnetic-field study

Dear research team,

We are examining the original 2025 report on motion of six different materials near the 18 mm gap of a toroidal magnetic-core apparatus, along with the later SSRN manuscript, using a source-specific quantitative comparison against established electromagnetic and mechanical mechanisms.

To assess reproducibility and distinguish motion from gravitational acceleration, could you share or identify the location of the original run-level source data, ideally including:

1. Original continuous video files, including the uncut pre-switch and post-switch periods, time/frame calibration and length/angular scale, with one run ID per file.
2. Matched ON/OFF and sham source-switch trials; the precise chronological order; all unsuccessful/null trials; and the number of independently repeated blocks.
3. Synchronized voltage, current, magnetic field and electric-field measurements; spatial field gradients near each target; measured waveform/frequency and switching transient.
4. Per-target actual mass, dimensions, composition, electrical charge, dielectric and magnetic susceptibility, mounting/thread details and sample-position geometry.
5. Coil-core material characteristics and magnetic hysteresis; gap geometry, temperature, power, ambient pressure/airflow/vibration and shielding/calibration protocols.
6. Sensor specifications, instrumental measurement errors, raw calibration files and analysis code, including any statistical error bars or confidence intervals.
7. Records for any independent replication by another laboratory, if available, with a separate apparatus and raw trace.

We would retain the original apparatus and source identity throughout the analysis and explicitly distinguish observed outcomes from model-dependent extrapolations. The aim is to test the claim on its strongest quantitative terms, not to presuppose an explanation or a result.

Please advise which materials are openly available, whether original raw files can be shared, and any attribution or conditions you wish to apply.

Kind regards,

[Sender to approve and sign]

## Acquisition ownership and verification

- **Do not send automatically**. User approval/identity and a sender are required.
- DOI/paper identity must distinguish the 2025 18mm toroid from the patent 10cm vessel high-voltage sphere and Pais HFGWG.
- If files arrive: retain originals unchanged, assign an apparatus ID, hash bytes against declared manifests, attach each file to its run/calibration identity, and preserve author attribution.
- Do not use author statements that "precise measurements are future work" to infer absence of every raw recording. Conversely, do not infer that videos contain calibrated force measurements without inspecting them.
- Independently transmitted lab data are NOT the same as an independent laboratory replication; source independence must be supported by personnel/rig/protocol chronology and held-out measurements.
- If responses are unavailable, prepare an ethically and electrically safe external experiment through a qualified laboratory. No unverified author's data can be manufactured by simulation.

## Required machine-readable delivery format

Preferred:
- source/run manifest following scripts/check_zhang2025_evidence_packets.py (one ON/OFF block with two distinct original raw hashes);
- time-aligned position and source data matching scripts/check_zhang2025_source_stress_dynamics.py, OR theta/time data matching scripts/check_zhang2025_torsion_consumer.py;
- independent randomized run-level residual file for conditional_hoeffding_ci, after physical systematics and independence assumptions are paid.

This request is an evidence-acquisition artefact, not an experimental, scientific or antigravity result.

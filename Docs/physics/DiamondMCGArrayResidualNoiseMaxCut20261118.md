# Diamond MCG: array residual-noise maximum cut (2026-11-18)

## Scope and prior-art owners

This cut extends the **existing** [diamond MCG PR #1238](https://github.com/chboishabba/dashi_agda/pull/1238) rather than reinventing Maxwell, NV spectroscopy or calibrated sensor readout.

- `DASHI/Physics/QuantumSensors/DiamondMCGFiniteBridgeExact.agda`: finite Fourier magnetic-current-to-axial-sensor map; NOT a physiological torso forward solution.
- `DASHI/Physics/Closure/NSTriadKNMaxwellFluidBiotSavartBridgeExact.agda`: exact rational-mode current/field donor, not a free-space tissue Green function.
- `DASHI/Physics/QuantumSensors/NVSIMetrologyReadoutAdapterExact.agda`: SI/readout-calibration boundary.
- `scripts/psychotronics_field_loom_covariance.py`: independently authored correlated GLS and explicit common-calibration covariance; reuse as prior art, not a newly measured noise spectrum.
- `DASHI/Physics/Measurement/BioEMErrorBudgetExact.agda`: conditional error propagation.
- `DASHI/Physics/Closure/NSTriadKNExactFiniteComplexCauchySchwarzRound65.agda`: finite Cauchy–Schwarz owner; the weighted matched-filter optimality proof should reuse this algebra where compatible.

Original experimental credit: Muhib Omar and coauthors, *Human cardiac measurements with diamond magnetometers*, *Science Advances* 12 (2026), eaeg5281, DOI 10.1126/sciadv.aeg5281. Their measured sensitivity is not a certified all-frequency white-noise floor, nor a measured 1,000-element array.

## New checked algebra

Execute `python3 scripts/check_diamond_mcg_array_detection_exact.py` (requires SymPy).

For `N` identical sensor couplings `a`, independent-channel variance `sigma²` and equicorrelated covariance
`C = sigma²[(1-c)I + c 11ᵀ]` with `0 <= c < 1` (for `N>1`), exact inversion yields

`a² 1ᵀ C⁻¹ 1 = (a²/sigma²) N/[1+(N-1)c]`.

The symbolic checker verifies the inverse and information formula at N=1,2,3,5,10, plus the 2-channel nonuniform-response covariance formula. The closed form itself is valid for all positive integers N, conditional on the stated covariance assumptions; finite symbolic instances are **not an Agda all-N kernel proof**.

Projection against the uniform interference mode gives `P = I - 11ᵀ/2`. For two channels it retains target power `(x-y)²/2`, and erases a perfectly uniform target. Hence gradiometry must never be claimed to reject interference without an accompanying target-transfer budget.

For `A(r)=A₀(r₀/r)³`, coherent ideal matched-filter observation time scales as `r⁶`; fixed-duration independent noncoherent power-block integration yields an illustrative `r¹²` scaling. Constants, phase tracking, bandwidth, threshold search, stationarity, other source multipoles, and non-Gaussian tails are NOT paid by these symbolic identities.

## Actual residual-noise research contract

1. **Forward source:** anatomically constrained finite-size heart with bounded current and tissue return currents, sensor positions/axes, an appropriate Maxwell quasistatic operator, measured coordinates and orientation; include finite-source multipole error bounds, not only a point-dipole law.
2. **Sensor:** measured transfer functions with units, optical/microwave resources, useful photon counts, channel cross-talk and intrinsic noise vs frequency. Distinguish 1,000 sensor heads from 1,000 NV defects or 1,000 subelements sharing one readout.
3. **Noise:** estimate `C_n(f)` from off-target and held-out recordings with uncertainty; model sensor and environmental contributions jointly. Positive definiteness and covariance stationarity are measured/validated obligations, not assumptions silently promoted to empirical fact.
4. **Detector:** for a *specified* signal, weighted linear matched-filter information `∫s† C_n⁻¹ s df`; then a source-family search with unknown heart rate, phase, position, motion, orientation and frequency multiple-testing corrections. Optimize retained cardiac signal against **residual** noise, not noise reduction alone.
5. **Attribution:** compare target-consistent 3D spatial templates with other humans, animal heartbeats, engine/rotor and electric-line harmonics; require held-out false-alarm and detection probabilities and localization criteria.
6. **Envelope:** compare one sensor, compact array and distributed array under *equal aggregate resources*. Report constructive verified achievable ranges separately from model-class no-go upper bounds. Unbounded time is not free: sensor drift and source evolution require independently tested coherence/reset models.

### Acceptance gates

| Gate | This cut | Remaining obligation |
| --- | --- | --- |
| A1: existing finite magnetic forward owner | Located | Physical finite-heart/tissue geometry weld |
| A2: exact equicorrelation information | Symbolic checks PASS | All-N Agda kernel proof |
| A3: spatial-filter signal-loss control | 2-channel exact negative control PASS | General projector and anatomical template |
| A4: general coloured/correlated array noise | 2-channel SPD rational identity PASS | Frequency-resolved empirical cross-spectra and uncertainty |
| A5: integration exponent | Conditional algebra PASS | Physiological phase tracking, noise tails, threshold trials |
| A6: kilometre-scale heartbeat detection | NOT established | Same-device measured residual noise and attributable target signal |

This is an exact mathematical negative/positive-control cut, NOT a demonstration of kilometre-scale sensing. No live array data were accessed. Neither external authors' scientific results nor preexisting owner proofs are claimed as new.

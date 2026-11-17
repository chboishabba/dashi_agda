# PV P7: robust measurement intervals and 369 control — 17 November 2026

**Source:** Existing [DASHI PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523), unchanged goal: **independently certified greater than 50% NET aperture-normalized solar electricity AND an independently testable physically distinct 369 advantage over a conventional same-source control.** Thermal, fuel and chemical outputs are separate. P3 RF, P4 multiplication, P5 thin-film and multijunction, P6 BH4 biological routes remain live.

## Why this exists

Earlier P5 production code `check_pv_g173_same_sample_optics_eqe_iv_weld.py` already computes source-matched R/A/EQE/J–V and 4T electrical MPP with converter and auxiliary costs. It does not by itself establish that input irradiance, voltage, current, converter efficiency or auxiliary costs are accurate enough to support the `>50%` conclusion, or a positive **369 minus conventional** difference. Both can fail even when nominal results pass.

**Primary measurement guidance:** IEC 60904-1:2020, [IEC official](https://webstore.iec.ch/en/publication/32004), defines solar PV current–voltage measurement procedures, plus informative area/capacitance and nonuniformity measurement discussion. IEC 60904-9:2020, [IEC official](https://webstore.iec.ch/en/publication/28973), classifies solar simulator spectral match, spatial nonuniformity and temporal stability. These standards are provenance requirements; merely citing them or declaring a simulator class does **NOT** prove compliance or a complete device uncertainty budget. Expanded measurement uncertainty is NOT a deterministic worst-case error bound unless specifically justified. Independent accreditation/certification and original equipment receipts remain OPEN.

## New executable verifier

`scripts/check_pv_369_worst_case_power_intervals.py` consumes source-hashed, source-declared per-junction MPP and 4T converter efficiencies from the original P5 source, plus one JSON of **externally validated simultaneous absolute error bounds** for each device. All inputs are mandatory; no unmeasured source/cost receives an automatic zero uncertainty. Required fields:

```json
{
  "solar_rel_bound": 0.005,
  "voltage_rel_bound": 0.002,
  "current_rel_bound": 0.002,
  "converter_efficiency_abs_bound": 0.005,
  "auxiliary_nominal_W_m2": 1.0,
  "auxiliary_abs_bound_W_m2": 0.1,
  "drive_nominal_W_m2": 0.0,
  "drive_abs_bound_W_m2": 0.0,
  "recovered_nominal_W_m2": 0.0,
  "recovered_abs_bound_W_m2": 0.0
}
```

These are **example schema numbers only, not measured data**. All normal-device uncertainty values must come from laboratory calibration, instrument and irradiance receipts. `solar_rel_bound` must apply to the whole aperture spectrum integrated over the same time as the source IV measurement. `voltage_rel_bound` and `current_rel_bound` must be source-backed **simultaneous uniform bounds over the complete IV sweep**, including unsampled maxima: *relative errors on finitely sampled points alone do not certify an arbitrarily curved true IV curve between samples*. Converter uncertainty is an absolute efficiency bound, and auxiliary/drive/recovery bounds use W/m². The existing P5 provenance requires specimen, temperature, source document, SHA-256 for each original file. Matched 369 and conventional controls must have distinct DUT identities, same source document and **identical incident spectrum SHA-256**, with overlapping calibrated illumination intervals. These are necessary, NOT sufficient, to establish real same-wafer, same-temperature equivalence.

For each junction nominal positive MPP P_i and converter efficiency eta_i, the calculation conservatively uses

```
P_out_i_lower = P_i (1-uV)(1-uJ) max(0,eta_i-uEta)
P_out_i_upper = P_i (1+uV)(1+uJ) min(1,eta_i+uEta)
P_net_lower = sum(P_out_lower) - (aux+uAux) - (drive+uDrive)
                                     + max(0,recovered-uRecovered)
P_net_upper = sum(P_out_upper) - max(0,aux-uAux) - max(0,drive-uDrive)
                                     + (recovered+uRecovered)
P_solar_lower/upper = P_solar(1∓uSolar)
```

The **robust physical predicate** for the candidate is `2 P_net_lower > P_solar_upper`. The **independent 369-specific margin** requires `P_369_net_lower > P_conventional_net_upper`. No overlapping interval can pass the second. When source-matched, both predicates must hold, on the same physical candidate, before promotion. They remain *conditional* on error-bound authenticity and optical/IV calibration, and do not upgrade the source's `real_world_certified=false` or `IEC_60904_conformant_proven=false`.

Synthetic checks are included in `--selftest`, but a positive synthetic outcome **must always remain uncertified**. Independent locally executed algebraic samples (11/11) confirm that a 510 W/m² nominal source on 1000 W/m² incident passes zero-uncertainty arithmetic, **fails** with 1% simultaneous voltage and current bounds (lower = 499.851 W/m²), and **passes** with 0.5% V and J bounds (lower = 504.91275 W/m²) absent other losses. A 2% incident-solar upper error alone forces the 510 W/m² example to **tie** 50%, and thus fail the strict condition. Matching against a 504 W/m² synthetic conventional control yields positive conditional margin only with nonoverlapping error bounds. This is not a measured 51% device.

## Agda Golden/source status

`DASHI/Physics/Photovoltaic/PV369IntervalRobustAcceptanceExact.agda` reuses `Circuit36927RecoveryEnergyBoundExact`, `PV369NetHalfThresholdExact`, `PV369MatchedDevicePhysicalAdvantageExact` and `PV369FourJunctionOpticsToMeasuredIVExact`. Defines `MeasuredPVPowerInterval` with source-sound lower/upper bounds on observed incident sunlight and observed net electric output; `RobustStrictNetHalf` with `suc solarUpper ≤ lowerNet+lowerNet`; `RobustMatched369Advantage` with `suc conventionalUpperNet ≤ proposed369LowerNet`; and an exact proof that overlapping intervals plus strict gain imply `suc(n)≤n`, absurd. A mistaken attempted doubling-monotonicity proof was REMOVED before acceptance, since successor induction does not directly justify addition monotonicity. **No full actual-source interval witness has been constructed. Native Agda Golden check OPEN.** Imported through the original `DASHI/Unified/PVPrimaryTOESpliceExact.agda`; no ESD files edited.

## Next physical maximum cut

1. Source one *actual* four-/five-junction specimen and a conventional matched control with calibrated ASTM/IEC simulator classification, spectral mismatch, spatial/temporal uniformity, contact V/J measurements and full uncertainty budgets.
2. Run P5 measured optics–EQE–JV receipt on raw per-junction files; run P7 interval bound verifier separately for both, and require **strict** lower >50 and proposed lower > conventional upper. Confirm independent instrument provenance; hashes alone are not certification.
3. Reduce the broad 4T4J/4T5J *model* headroom by actual optical, thermal, converter, recombination and mismatch intervals, preserving common solar denominator.
4. Continue corrected Bahder P1d same-sample GaAs Hamiltonian, P3 external RF accounting, P4 carrier multiplication, P6 photosystems independently. Specify and preregister a changed *physical* 369 operator/transition versus ordinary `Td→C3v`, not just a symbolic phase relabelling.

**Same-ledger hardening (9ca007b):** The P7 uncertainty tool now MUST recover the original P5 nominal 4T net electric output from unchanged per-junction gross MPP and per-channel delivered MPP, plus the signed auxiliary, drive and recovery terms. It rejects changing the nominal metered costs in the uncertainty JSON and rejects a delivered power inconsistent with its gross MPP × converter efficiency. Two adversarial selftests are in the source. These are ledger-integrity conditions, not independent instrument authentication. Exact committed Python selftest remains unexecuted from a fresh checkout; 11 independent envelope arithmetic checks previously executed, without claiming full-script acceptance.

**Source identity hardening (406825e):** The original P5 measured-data producer now exposes `incident_spectrum_sha256` explicitly alongside path-keyed hashes. The conservative P7 checker requires this to be a 64-character lowercase SHA-256 that occurs in the exact original input manifest; it checks equality between conventional and proposed devices, declares distinct specimen IDs, same source reference, exactly same finite-positive specimen temperature and overlapping source irradiance bounds. A control with absent spectrum hash or different temperature must fail before evaluating any 369 advantage. Additional source-integrity and ledger adversarial cases are present in the committed `--selftest` but remain unexecuted at exact GitHub head; the original independent 11/11 arithmetic checks should not be inflated.

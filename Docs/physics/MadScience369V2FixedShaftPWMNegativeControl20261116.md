# Source-bounded V2 steelman: finite-bus averaged-PWM adversarial confirmation

**16 November 2026. Owner:** DASHI V2 motor PR #1519. This is a **second, independent synthetic model**, not measured V2 hardware. It deliberately checks whether the *ideal rectangular-pulse* comparison in `MadScience369V2SourceBoundedEfficiencySteelmanMaxCut20261116.md` survives a more realistic nonlinear winding/current controller. Original @madscience369 reporting remains ~2354 RPM, motor electric display ~285–287 W and loaded output ~45 W; these cannot establish true shaft work, pulse topology or efficiency.

## Reused canonical producer, not a new ad hoc motor law

The source **imports** `scripts/v2_coupled_pulse_machine_maxcut.py` from the original PR #1511. It integrates its existing positive differential-inductance winding matrix with neighbouring mutual coupling, reversible saturation, first-order dissipative magnetic lag, thermal state, signed coil-port drive/regeneration and averaged PWM voltage tracking capped by a synthetic 320 V DC bus. It uses `m=3` only as one illustrative candidate, not a 369 optimality assertion. Pulse timing q changes the target current; controller amplitude is separately calibrated to approximately 45 W mechanical extraction for each q. The electrically and magnetically near-periodic states are measured after five warm-up revolutions.

**IMPORTANT:** the controller integrates 180 motor ODE steps/revolution and commands an *averaged* PWM voltage, while charging 20 kHz switching events as losses. It does NOT resolve every transistor edge or fully certify sampled-to-continuous numerical integration error. Magnetic inventory is near-periodic at a 2% tolerance; the thermal energy inventory changes. Voltage/current/thermal majorants remain conditional on the model, not source-calibrated device bounds.

## Matched shaft resource, converter intervention

All five selected arms produce approximately **45 W synthetic shaft extraction**, independent of original V2. Baseline reverse-flow converter efficiency is 0.95. Enhanced recovery efficiency is 0.99 for **all reverse terminal flow**, not merely turn-off clamp recovery (different from the primary ideal comparator), with an additional 0.4 W controller cost. Selecting a narrower pulse adds 0.2 W logic cost. Phase count, material and bus voltage are held fixed. The reference control amplitudes are recalibrated to maintain shaft work as q changes, rather than assuming equal current produces equal mechanical extraction.

| Arm | q | Model shaft W | Model bus W | Copper W | Gross reversed coil W | Max commanded V |
|---|---:|---:|---:|---:|---:|---:|
| Ordinary averaged-PWM | 0.00 | 45.00 | 19.32 | 8.438 | 181.80 | 207.7 |
| Pulse timing alone | 0.10 | 45.00 | 18.70 | 8.355 | 189.45 | 223.6 |
| Enhanced recovery alone | 0.00 | 45.00 | **26.19** | 8.438 | 181.80 | 207.7 |
| Both strategies | 0.10 | 45.00 | 25.88 | 8.355 | 189.45 | 223.6 |
| Over-narrow pulse, enhanced recovery | 0.45 | 45.00 | 25.10 | 8.065 | 230.98 | 314.4 |

**Adversarial result:** with selected fixed shaft work, extra pulse concentration makes *copper loss decline* but net useful bus output also declines, because gross bidirectional converter processing grows and the timing-controller cost is not free. The pulse-only arm is ~0.62 W worse than ordinary, while enhanced recovery is ~6.87 W better. Even with enhanced recovery, the combined q=0.1 pulse is ~0.32 W worse than recovery alone; q=0.45 is worse again.

This does **not refute** useful pulsed control in other hardware/regimes; it refutes a universal inference from narrow pulses to efficiency. The exact controller and cost models differ from the ideal rectangular benchmark; **do not combine their watts or rank across the two models**. All computations remain source-independent and no additional energy or original V2 magnetic measurement is claimed.

## Exact next cuts / validation

- `v2FixedShaftFiniteBusPulseTimingCanHurtEvenIfCopperFalls` — model-level negative control 6/6 local tests PASS, same shaft ±0.03 W, finite **averaged** voltage, near-matched magnetic storage; no Agda or interval ODE validation.
- `v2EnhancedRecoveryGrossBidirectionalPortCostsPaid` — model-level positive effect with explicit controller overhead, in the limited reverse-efficiency intervention.
- `v2TrueTransistorPWMAndMatchedWholeStateThermal` — OPEN, requires switched converter and gate-driver trajectories, 20 kHz edge discretisation, thermal periodicity, and uncertainty-certified ODE flow.
- `v2V2SourceSelectedPulseLossDisplacement45W` — OPEN, requires actual apparatus winding + switch trace, shaft torque and complete same-window power/storage observations.

No cable geometry is imposed before the mean-electromechanical efficiency gate. The prior nonlinear retarded field/path proof remains available if source timing makes it relevant. **All 16 strong original P0–P4 gates remain OPEN**. The next maximum-cut priority is a *single physically feasible A/B with the same real shaft and every relevant stored-energy state*, not another generic line-delay theorem.

## Reproduce

```sh
bash scripts/check_v2_source_bounded_efficiency_maxcut.sh
bash scripts/check_v2_fixed_shaft_pwm_negative_control.sh
```

**Acceptance:** 57/57 ideal comparator tests + 6/6 finite averaged-PWM negative tests passed locally in separate completed runs. Exact Github checkout, complete historical runner and pinned Agda kernel remain unverified. Numerical receipt lives in `Artifacts/v2_fixed_shaft_pwm_negative_control_receipt.json`.

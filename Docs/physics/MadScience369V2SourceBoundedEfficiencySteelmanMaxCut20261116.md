# V2 steelman: source-bounded, fixed-shaft, four-arm efficiency max-cut

**16 November 2026. Owner:** `chboishabba/dashi_agda`, continuation of motor PR #1519. This is **constructed mathematical/computational work, NOT a physical V2 test, identification or calibrated efficiency result**.

## Source and authorship boundary

The original @madscience369 V2 reel reports about 2353–2354 RPM, motor **electrical** input display about 285–287 W loaded/unloaded, and electrical-load output about 45 W under load. The reel does not provide the generator shaft torque, original winding and switch circuit, source-selected flux linkage, extra power inputs, control timing or matched storage endpoints. No V2 pulse architecture is inferred. Donald Smith/Filsinger pump and recovery mathematics, Slobodian/Infinity SAV MG10, David Holmstrom/Resonate369 and Tesla polyphase are separately attributed donors, not evidence of identical hardware. Conventional reluctance/co-energy/rectifier theory retains its prior-art provenance.

**Our steelman:** current is timed to generate braking work on falling inductance, and recoverable magnetic energy is returned rather than lost in clamp/rectifier/switching paths, potentially changing copper/core/controller losses. The Don Smith analogue is signed transient storage, nonlinear pumping and recovery; it is not an external energy claim.

## Compared boundary and nonlinear winding

The **four arms all assume a common 45.0 W *generator shaft* extraction** at 2,354 RPM. The number 45 W happens also to be the reel's *reported load output*, but that is a **different physical quantity and must not be identified with shaft work**. All arms have the same invented winding and speed, same positive incremental inductance, current limit, and start/end **winding** state. They do **not** match measured motor electrical input or unmodelled capacitor/thermal states. These comparisons are all under electrical load, whereas the reel is a loaded/unloaded comparison.

Define the reversible, saturating magnetic co-energy and associated flux, torque and stored energy:

\[
W'(i,\theta)=\tfrac12 L_0i^2 + A\cos(h\theta)I_s^2\log\cosh(i/I_s),\quad
\lambda=L_0i+A\cos(h\theta)I_s\tanh(i/I_s),
\]
\[
\tau=-AhI_s^2\log\cosh(i/I_s)\sin(h\theta),\quad
U=i\lambda-W',\quad \partial_i\lambda\ge L_0-A>0.
\]

For a constant-current ideal pulse on `sin(hθ)>q`, shaft extraction and resistive loss are:

\[
P_{shaft}=\frac{Ah\omega I_s^2}{\pi}\log\cosh(I/I_s)\sqrt{1-q^2},\qquad
P_{Cu}=\frac{RI^2}{\pi}\arccos(q).
\]

The peak current is independently solved in each arm to hold shaft input fixed. Analytic integration splits *positive* and *negative* running coil-port `vi` while separate onset magnetisation and turn-off flyback events charge or return `U`. The following identity is independently checked:

\[
P_{running,reversed}+P_{flyback}-P_{magnetise}-P_{running,forward}
=P_{shaft}-P_{Cu}.
\]

The converter's actual **net signed bus** power is separately calculated:

\[
P_{bus}=\eta_{running}P_{running,reversed}
+\eta_{clamp}P_{flyback}
-\frac{P_{magnetise}+P_{running,forward}}{\eta_{forward}}
-P_{switch}-P_{controller}-P_{core}
=P_{shaft}-\sum P_{loss}.
\]

This explicitly prevents counting recoverable flyback energy as a second power source. A controller cannot increase useful output by recovering more than what was stored and extracted from the accounted input.

## Assumed model inputs, not actual hardware parameters

`L0=40mH`, `A=12mH`, `h=4`, `Is=5A`, `R=1Ω`, `Ipeak≤8A`; `eta_forward=eta_running=0.98`; ordinary rectifier **already recovers 80% of the flyback**; enhanced recovery returns **95%** with extra 0.4 W control power and reduced switching-event losses; pulse timing costs 0.2 W logic power. Switching events cost 2 mJ fixed plus 0.15 mJ/A² per transition before soft-switching reductions; a separate 0.5 W fixed core loss is charged. **Only the approximate rotor RPM is taken from V2.**

## Four arms: model result

| Control | q threshold | Peak current (A) | Copper (W) | Clamp loss (W) | Total loss (W) | Net bus (W) | Gain (W) |
|---|---:|---:|---:|---:|---:|---:|---:|
| Ordinary loading + rectification | 0.000 | 5.285 | 13.967 | 14.227 | 34.067 | **10.933** | +0.000 |
| Pulse timing only | 0.223 | 5.364 | 12.326 | 14.776 | 33.272 | **11.728** | +0.796 |
| Enhanced recovery only | 0.000 | 5.285 | 13.967 | 3.557 | 23.408 | **21.592** | +10.659 |
| Combined timing + recovery | 0.396 | 5.554 | 11.420 | 4.035 | 21.839 | **23.161** | +12.228 |

**Net gain from combined timing and recovery:** 12.228 W. Timing alone gains 0.796 W, recovery alone gains 10.659 W, and the factorial interaction is 0.773 W. Combined and ordinary net bus powers correspond to **24.3% versus 51.5% of the *hypothetical generator shaft input***, not efficiency of the V2's motor electrical supply.

The loss changes are independently visible: clamp dump 14.23 → 4.03 W and copper 13.97 → 11.42 W. Other converter, switch, controller and core losses remain charged. Gross cycling electrical power can far exceed useful net output; internal circulating energy is **not** an additional source. The best q is a restricted finite numerical grid plus bounded local refinement, **not** a certified global nonlinear/hybrid controller optimum.

**Idealisation boundary:** instantaneous rectangular current edges require impulse voltage and are **not physically feasible** with finite bus voltage/finite inductance. Zero winding stored-energy change follows by returning `i=0` between pulses; DC-bus, capacitor, battery, magnetic hysteresis and thermal endpoints are *not* certified. Thus the numerical gains are **restricted limiting-model hypotheses**, not admissible physical operating points. The next cut must use the existing finite-slew machine dynamics before treating this ranking as a design recommendation.

## The *separate* 45 W loaded/unloaded observational discriminator

For the *whole motor-generator system*, do not double count shaft work delivered from its motor as an independent external input:

\[
\Delta P_{load}=\Delta P_{motor,electric}+\Delta P_{aux}+
\Delta P_{other,input}-\Delta P_{loss}-\Delta\dot E_{stored}-\Delta P_{other,output}.
\]

If displayed ~286 W motor input really equals true motor electric input and remains fixed, and all external/auxiliary input, other output and storage-rate changes vanish, an additional 45 W load output **requires approximately a 45 W reduction in total loss**, or around **15.7%** of displayed input. If motor input differed by ±2 W, the required reduction could be around **43–47 W**, other terms held fixed.

Our **12.23 W** gain is a comparison *between four constructed loaded operating strategies at the same hypothetical shaft power*. It is not the same intervention, and by itself is **not a sufficient explanation of a 45 W loaded/unloaded output difference**. Four exact, energy-closed counterworlds in the JSON receipt produce the same displayed ~286 W input and ~45 W output with different mechanisms: loss reduction, storage depletion, separate auxiliary input, or true power unrepresented by the meter. The reel alone does not select one.

**Decisive missing quantity:** simultaneous signed generator shaft torque×speed, motor terminal `vi`, load `vi`, all other external inputs and capacitor/magnetic/thermal energy changes. Nearly constant RPM is not the same thing as unchanged shaft torque.

## Falsifiers and adversarial controls

- Ordinary generator control is **not** assumed to dump all flyback. Setting baseline clamp efficiency to zero would invent a strawman.
- For recovery controller overhead 0–30 W, converter efficiency 0.9–1, and copper resistance 0.5–1.5 Ω, **18 / 45** sensitivity cases make enhanced recovery worse; no universal efficiency gain.
- The perfect-converter test never produces more electrical bus output than admitted shaft input after copper loss. Excessive timing-logic cost likewise reverses a positive timing gain.
- Taking saturation scale `Is→∞` recovers the existing `check_v2_pulse_nonlinear_recovery.py` donor's linear current and copper formula; the regression imports that actual module.
- Earlier symmetric 3–12 phase results show that phase count alone does not imply more mean electrical export; 3/6/9 must be compared on comparable physical budgets.
- No cable geometry is needed for this *mean energy comparison*. Finite-speed Maxwell/transmission-line treatment remains **conditional**, needed if verified switching edges, HF resonances or field gradients materially alter the result.

## Exact acceptance leaves and next P0–P4 cuts

| Declaration | This round | Strong remaining acceptance |
|---|---|---|
| `v2SameShaftSaturatingPulseCoenergySignedIdentity` | Analytic coil-port positive/negative integrals, SymPy general co-energy identity, source-donor linear limit and regression | Real-calculus Agda proof and finite-slew source-device controls OPEN |
| `v2FourArmCompetentRectifierRecoveryFactorial` | Reproducible four-arm fixed-shaft comparison with independent bus/loss sums | Empirical baseline/advanced recovery, same real apparatus, equal copper mass and full storage OPEN |
| `v2RecoveryCannotDoubleCountMagneticStoredEnergy` | Exact signed winding energy identity and flyback upper bound | Real diode/switch/cache/saturation waveform and switching loss OPEN |
| `v2Original45WLoadedUnloadedLossDisplacement` | Whole-boundary conditional −45 W loss difference and 4 energy-closed counterworlds | Same-source shaft/vi/aux/thermal/metrology identification OPEN |
| `v2FiniteSlewFixedShaftStorageMatchedEfficiencyFrontier` | **OPEN** | Voltage-limited attainable i(t), net bus, torque ripple, thermal and full-cycle storage; certified Pareto |
| `v2OriginalV2ControllerSourceReceipt` | **OPEN** | Source-selected reel netlist, control trace, coil/pole/magnet and actual λ(i,θ,T) |
| `v2V2ExperimentLossSuppression45WIdentifiability` | **OPEN** | Randomised load interventions with calibrated all-port, torque and storage measurements |

All original **16 P0–P4 strict gates** remain OPEN at their strong definitions. We have not executed Agda kernel or a physical V2 experiment here. **The next mathematical maximum-cut is physically feasible finite-slew, same-shaft-and-storage closed A/B control**, followed by source-specific V2 calibration and physical energy accounting. Causal cable geometry is not the primary research goal.

## Reproduce

```sh
bash scripts/check_v2_source_bounded_efficiency_maxcut.sh
python scripts/v2_source_bounded_efficiency_maxcut.py > Artifacts/v2_source_bounded_efficiency_receipt.json
```

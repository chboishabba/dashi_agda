# J19 — Exact zero freewheel resistor loss, restored J18 HF output and locally consistent switching

**23 November 2026 | PR #1537, target master.** User-directed steelman/backsolve. This is a conditional *dimensionless native J18 simulation*, NOT a measured 0%-loss real apparatus, physical superconductor, historical source admission, confirmed original Filsinger pin map, self-running generator or gravity effect.

## Existing owner, not a new circuit

Use canonical J12 seven-state coupled coil/capacitor/diode/open-wave equations, inherited unchanged inside J18's additional *candidate* HF current and nonlinear cap voltage. Original source:
- [J12 native original](../../scripts/check_smith_filsinger_j12_restored_cycles_20261122.py), exact blob `f5f66e343a979dfe2bc70f68e1e98fce75817653`.
- [J18 HF spark-bank dump/secondary coupling](../../scripts/check_smith_filsinger_j18_hf_spark_tank_20261123.py), exact blob `430520c86fc471deada48835c7d048888745d2fa`.
- [J18 physically separated source and work report](SmithFilsingerJ18NativeHFSparkDumpNonlinearTankReverseSolve20261123.md).
- **New J19 consumer:** [source-native zero freewheel loss and switch-history regression](../../scripts/check_smith_filsinger_j19_zero_freewheel_inverse_20261123.py), Git blob `e32e4a7c6433d36e9b188240cb88612d9cc2f0ca`. Independently byte-matched to the exact local executed file. No new component schema or source ontology.

## Precisely which loss is zero

Native J18 defines OFF-state **freewheel** dissipative work:

\[
W_{\mathrm{free}}=R_f\int_{\chi=0}i_h(t)^2\,dt.
\]

For **(R_f=0)** the freewheel contribution is mathematically **exactly zero**, regardless of current and switching times. This is *not* 0% total circuit heat: native winding/copper (R_{\mathrm{coil}}>0), spark (R_{\mathrm{gap}}>0), diode and original-field heat, and the separate (G_Lx^2) load remain paid. Nor does (R_f=0) supply a physical return wire, actual superconducting connection or authentic original reel. It is an **ideal passive lower bound** for one hypothesised return.

For a *distinct, untested physical topology completion*, a passive reactive OFF return can reconnect the existing HF inductor current to the existing capacitor:
\[
\begin{aligned}
L_h\dot i_h&=\chi b-\xi x-[R_c+\chi R_g]i_h-k_hu,\\
\dot Q_h&=\xi i_h-G_Lx,
\quad \xi=\chi+(1-\chi).
\end{aligned}
\]
The exact symbolic tank law is then
\[
\dot U_h=\chi bi_h-k_hu i_h-(R_c+\chi R_g)i_h^2-G_Lx^2.
\]
Local SymPy verified this cancellation **algebraically**; no full nine-state restored simulation or pin evidence for this alternate LC switching completion has been claimed. The actual J19 numerical acceptance stays on **unaltered J18, (R_f=0)**.

## Restored-state source-aware reverse solve

Parameters: original J18 default (L_h=.15,C_h=.12,\alpha=.5,R_g=.09,R_c=.05,G_L=.16,k_h=.12), J12 default original driving, *hypothetical* incoming amplitude (a=1.2), phase (0.3), and changed **(R_f=0)**. Doubling the former low thresholds ((V_{\rm on},V_{\rm off})=(.003,.0009)) to **(.006,.0018)** cuts the restored event count from 134 to **68** per 20π model-time cycle. All quantities synthetic/dimensionless; neither bare tank frequency nor 7.8-kHz **acoustic** measurement identifies electrical mode or Duga/HAARP/SURA frequency.

### Native parameter continuation — all tested with actual J18.advance

| Return resistance | Freewheel dissipated | HF-load work | Net wave work | Events |
|---:|---:|---:|---:|---:|
| .40 (original J18 threshold) | .156052 | .024518 | +.140811 | 38 |
| .20 | .136031 | .032458 | +.139644 | 32 |
| .10 | .102265 | .041846 | +.138387 | 32 |
| .05 | .072891 | .052199 | +.137359 | 60 |
| .01 | .021345 | .071483 | +.139433 | 116 |
| **0 (original low threshold)** | **0** | **.078643** | **+.139420** | 134 |
| **0 (updated thresholds)** | **0** | **.079664** | **+.139489** | **68** |

Every tabulated row underwent native numerical restored-cycle test at the parameter settings indicated, not an analytic global uniqueness proof. J19 acceptance separately repeats the baseline and improved threshold-selected candidate.

### Selected zero-freewheel native signed ledger

At restored (R_f=0,V_{\rm on}=.006,V_{\rm off}=.0018), (a=1.2):

| Component | Integrated synthetic work |
|---|---:|
| Source wave incident | +90.477868 |
| Source wave outgoing | −90.338379 |
| **Net incident wave work** | **+0.139489** |
| Original controller driver | +24.845351 |
| Bank → HF switched internal transfer | +0.017252 |
| Original secondary → HF internal transfer | +0.207406 |
| HF load | −0.079664 |
| HF coil loss | −0.126845 |
| Spark-gap loss | −0.018149 |
| **OFF return resistor loss** | **0.000000** |

HF internal budget: (0.017252+0.207406 = 0.079664+0.126845+0.018149\) within numerical residual. Of this approximately **35.46%** is the designated HF load, **56.46%** winding heat and **8.08%** gap heat. It is inaccurate to call the whole circuit 100%-efficient. Compared with the original J18 baseline, HF load rises by **3.249×**, but spark events change topology/regime, and coil loss increases; no all-parameter monotonicity claimed.

## Source OFF vs source ON — actual separate restored cycles

Holding (R_f=0), doubled thresholds, controller nominal drive, original coupling and all other synthetic parameters:

| Condition | Wave net | HF load | Driver work | Spark events |
|---|---:|---:|---:|---:|
| Incoming wave OFF | −0.120955 | 0.076405 | 24.840766 | 60 |
| Incoming wave ON ((a=1.2)) | +0.139489 | 0.079664 | 24.845351 | 68 |
| **ON − OFF** | **+0.260444** | **+0.003258** | **+0.004586** | different history |

The controller work changes by **+0.004586** as well, and source ON changes switching count 60→68. Therefore +0.003258 is **source-sensitive change in model HF load**, not proven work supplied by a separately replenished environmental source or an equal-branch linear response derivative. Incoming/outgoing waves and driver are independently budgeted.

## J16 event history: locally accepted, not globally smooth

At selected zero-(R_f) 68-switch source-ON branch, separately restored (a=1.195/1.205), (k_h=.1198/.1202), and (phi=.295/.305) retain the exact same **ordered 68 ON/OFF labels** and positive net wave/HF-load work at both sides. Maximum paired physical-model event-time shifts are ~**.00863**, **.00458**, **.00375** respectively. Two consecutive nominal cycles also match ordering/times under the numerical tolerance. This addresses the immediately local J18 ±.005 and ±.002 instability with a more restricted coupling step, NOT the entire J16 global event-grazing/cycle branch ambiguity.

**Full acceptance granularity:** native J19 baseline+centre+source-OFF and three paired perturbations use two-cycle state restoration `max |z_next-z_prior|<2e-5`, native signed residual gate `<3e-5`, integrated storage delta `<1e-5`, same ordered event labels and adjacent-cycle event-time difference `<.02`. An independently tightened **single centre** run at `1.5e-6` achieved state closure **1.89e−7**, storage delta **8.12e−8**, and signed residual **1.13e−8**; the complete paired tight-tolerance suite was **not** certified and is not represented as such.

**Negative controls:** source-OFF is a *different* 60-event restored orbit, not differentiated across as the same smooth branch; near (k_h=.118/.122) the event count differs (66/68), so local 68-event matching is a **small** parameter neighbourhood only. A separate large-threshold scan timed out; no guarantee of valid restoration there. Lossless freewheel is an idealized return assumption and **physical 0%-loss device is OPEN**.

## Next actual cut — source closure and alternative return topology

1. **J19b:** solve a genuinely reactive OFF capacitor/inductor return (separately source-indexed candidate), keeping all energy stores. Numerically test its default/native legacy reduction, event trace and full cycle; do not use a new empirical netlist.
2. **J19c:** select a local 68-event chart, refine bounded derivatives / event chronology with fixed starting switch branch and small interval arithmetic/stress near grazings. Also compare source-off and phase-shuffled interventions without treating different branches as a derivative.
3. **F13/F15:** existing Maxwell/ADE transfers for Duga HF antenna/downconversion, HAARP electrojet/Hall, SURA plasma and Filsinger terminal. Real electrical pin, receiving field/impedance, physically usable load, real controller costs and metered environmental work remain missing.
4. **Physical interpretation:** ideal freewheel superconductivity, zero total loss, a self-powered high-voltage device and antigravity are *not* consequences of this model. Keep Pais/YBCO gravity in independent mechanical force/stress experiment with its existing null evidence.

**Attribution:** original Filsinger spark/capacitor-bank interpretation, prior DASHI J12/J18 models and reports, SymPy/numerical source-consumer work, original radar/HAARP/SURA experimenters and existing exotic-gravity constraint owners retain separate provenance.

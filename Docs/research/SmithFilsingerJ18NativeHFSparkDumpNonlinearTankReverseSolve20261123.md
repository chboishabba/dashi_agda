# J18 — Native Filsinger capacitor-bank spark dump → HF tank → load/coupling: reverse solve

**23 November 2026.** User-requested correction to J17b. This is a source-derived circuit-hypothesis *candidate model*, NOT a pin-verified Filsinger netlist or experimental high-frequency electrical waveform. No CI, no Agda kernel, no claimed excess power or antigravity.

## What was already discovered; why J17's "spark work" needs reinterpretation

The earlier canonical [Smith/Filsinger hybrid-study ledger](SmithFilsingerHybridStudyExactRemainingLemmas20261115.md) explicitly says: **ZVS is the driven pump and the spark gap is a capacitor-bank dump/switch, not a separate source**. The [causal nonlinear source rollup](SmithFilsingerCausalNonlinearSourceRollup20261115.md) and [source-port/shunt source report](SmithFilsingerSourcePortShuntMaxCut20261115.md) similarly distinguish the midpoint/spark narrative from the ZVS and three-Earth-electrode reels.

The original [J12 seven-state circuit](../../scripts/check_smith_filsinger_j12_restored_cycles_20261122.py) retained coupled windings, nonlinear diodes, bank and hysteresic spark events, but its **specific spark implementation** was a switched resistor:
\[
C_b\dot b=j_u+j_v-G_{\rm bleed}b-G_{\rm spark}\,\mathrm{on}\,b,\qquad
W_{\rm J12,spark}=\int G_{\rm spark}\,\mathrm{on}\,b^2\,dt.
\]
That term is **all dissipated by definition**. The [J17 native wave-absorption cut](SmithFilsingerJ17NativeRestoredWaveAbsorptionReverseSolve20261123.md) therefore correctly proved a **J12-implemented absorber** but could not represent the proposed HF spark-bank dump exciting secondary resonances. It was a conservative baseline, not proof that the real spark cannot transfer energy into a tank. A real spark also dissipates and radiates energy; no ideal or lossless spark is inferred.

## New native J18 extension: nine states, no replacement circuit

Actual pre-existing native J12 file at Git blob **`f5f66e343a979dfe2bc70f68e1e98fce75817653`**, unchanged. [J18 HF extension](../../scripts/check_smith_filsinger_j18_hf_spark_tank_20261123.py) at exact executed blob **`430520c86fc471deada48835c7d048888745d2fa`** preserves all seven original state variables \((i,j,u,v,b,q,z)\), same physical branch labels, diode rectification, electromagnetic input/outgoing and hysteretic thresholds. It adds only two explicitly **candidate** HF states:

- \(i_h\): switched HF loop current with finite \(L_h\), coil loss \(R_c\), gap loss \(R_g\) when ON and **assumed** resistive freewheel return \(R_f\) when OFF. This hypothesised return topology remains unverified.
- \(x\): voltage of a passive candidate nonlinear HF capacitance \(Q_h(x)=C_h(x+\alpha x^3)\), \(\alpha\ge0\), with separate ideal load conductance \(G_L\). For this selected constitutive law, \(U_h=C_h(x^2/2+3\alpha x^4/4)\), which local SymPy verifies exactly via \(dU_h=x\,dQ_h\). There is no claimed measured varactor/nonlinear dielectric in the original device.

With \(\chi\in\{0,1\}\) the original spark on/off switch and \(k_h\) a signed reciprocal coupling to original secondary voltage \(u\):

\[
\begin{aligned}
C_b\dot b &= j_u+j_v-G_{\rm bleed}b-\chi i_h,\\
L_h\dot i_h &= \chi(b-x)-[R_c+\chi R_g+(1-\chi)R_f]i_h-k_h u,\\
C_h(1+3\alpha x^2)\dot x &= \chi i_h-G_Lx,\\
\dot{\boldsymbol v}_{uv} &= A^{-1}\!\binom{-j-j_u+kq+k_h i_h}{j-j_v}.
\end{aligned}
\]

The other original J12 state equations and all driver/wave-source terms are retained. The new branch interacts **bidirectionally** with both the bank and existing secondary; it is not a merely downstream postprocessed division of the old spark-heat total.

### Independent signed work: the key result

For \(U_{h,\rm total}=L_h i_h^2/2+U_h(x)\):

\[
\dot U_{h,\rm total}
=\chi b i_h-k_hu i_h-[R_c+\chi R_g+(1-\chi)R_f]i_h^2-G_Lx^2.
\]

Meanwhile the original bank/secondary gains **\(-\chi b i_h+k_hu i_h\)**. These two internal transfers cancel *exactly*. After summing the boundaries, with all native J12 losses and storage kept:

\[
\boxed{W_{\rm drive}+W_{\rm incident}-W_{\rm outgoing}
=W_{\rm original\ losses}+W_{\rm gap}+W_{\rm coil}+W_{\rm freewheel}
+W_{\rm HF\ load}+\Delta U_{\rm nine\ states}.}
\]

**Do not add \(W_{\rm bank\to HF}\) or \(W_{\rm secondary\to HF}\) to the external-source ledger again.** They are internal transfers. Likewise, \(\int G_Lx^2dt\) is dissipated real work in a deliberately designated model **load resistor**, not an independently rectified, measured or demonstrated useful consumer.

The local SymPy tests independently checked the exact nonlinear capacitor derivative, HF energy equation, bank/secondary cancellation, and linear-\(\alpha=0\) limiting law (5 symbolic identities). A **legacy-mode** numerical run independently reproduces unaltered J12 on the same initial state and input with maximum seven-state difference **\(5.455\times10^{-9}\)**, same 12 spark events and native matching work to tolerance. No canonical Agda/TOE/ESD owner rewritten.

## Local nine-state *restored* numerical results

Same original clock period \(20\pi\) model units, \(\phi=0.3\), \(V_{\rm on}=0.003\), \(V_{\rm off}=0.0009\), with **specified synthetic** \(L_h=0.15,C_h=0.12,\alpha=0.5,R_g=0.09,R_c=0.05,R_f=0.4,G_L=0.16,k_h=0.12\). These are dimensionless numerical choices, NOT Filsinger's electrical component values. Bare linear HF eigenfrequency \((L_h C_h)^{-1/2}\approx7.45\) in this artificial time unit is neither the recorded ~7.8-kHz **acoustic** carrier nor the SURA 8–9-kHz or Duga radio carrier.

Each accepted case replays from zero and then checks **two consecutive complete cycles** with matching ON/OFF event labels/times, state closure and exact integrated signed work:

| Incident amplitude | Net received-wave work | HF load branch | Switch events | Restored-state closure |
|---:|---:|---:|---:|---:|
| 0 (original driver only) | −0.119895062 | 0.023056104 | 20 | \(1.20\times10^{-10}\) |
| 0.8 | −0.004272376 | 0.023504848 | 20 | \(1.01\times10^{-10}\) |
| **1.2** | **+0.140810750** | **0.024518153** | **38** | **\(1.32\times10^{-10}\)** |

At 1.2, incident and outgoing wave works are **90.477868423** and **90.337057673**, driver work **24.806882122**, nine-state storage change **\(-4.76\times10^{-11}\)**, total work residual **\(3.96\times10^{-10}\)**. Thus this candidate provides a **numerical restored-cycle operating point** with positive wave absorption and a separately identified HF load. No absolute real power, independent natural-source access, or controller-free useful output is established. In particular driver-only has an HF load: it would be wrong to claim all positive HF-load energy at 1.2 came from the incident wave.

### Inside the HF dump: one coherent two-input energy ledger

On the 1.2 restored model cycle:

| Internal source / destination of HF circuit energy | Signed model work |
|---|---:|
| Bank → HF through spark switching | +0.012085215 |
| Secondary → HF through reciprocal coupling | **+0.189085170** |
| HF load resistor | −0.024518153 |
| Spark-gap loss | −0.000702852 |
| HF-coil copper loss | −0.019897019 |
| Assumed OFF-state freewheel dissipation | −0.156052362 |

The internal HF supply is **0.201170386** and its separately paid losses plus ideal load **0.201170386**, leaving residual ~\(1.68\times10^{-10}\) model work units. The bank dump is only one part of HF excitation; the *existing original secondary supplies most of the HF-branch energy in this fixture*. This is exactly the sort of **nonlinear, coupled capacitors/coil/switching return** steelman the original spark-dump hypothesis called for. It is NOT independent atmospheric work: the original controller and incoming/outgoing model wave pay the upstream circuit.

The incremental HF load between the driver-only and a=1.2 restored cases is only **+0.00146205**, despite the change in net wave work **+0.26070581**; multiple other loss and storage terms change. Neither this arithmetic difference nor a steady restored cycle *causally allocates* that incremental load entirely to the natural wave without matched-source intervention and calibration.

## Negative controls and inverse-branch warning — do not conceal failures

- With both driver and source **OFF** and empty stores, no HF transfer, load or energy appears.
- With **Gload=0**, the load vanishes as required; the alternate topology/cycle failed the restoration certificate within **four tested intervals**. This is a numerical no-certificate, **not** a theorem ruling out a different long-time orbit.
- With \(k_h=0\), the secondary exchange disappears in the instantaneous run. A separate five-interval restoration attempt did not certify a cycle; the last load was ~0.0002024 instead of the baseline ~0.0245182. This underlines the pivotal conditional role of the HF–secondary coupling, but is **not** evidence of original pin linkage.
- With \(\alpha=0\), a **restored** positive absorber and HF load still exist (net +0.14082397; load 0.02444968; 36 switch events): nonlinear capacitance **is not necessary** for these particular effects, since hysteretic spark switching, diodes and other coupling already create nonlinear dynamics.
- **Critical J16 event instability:** restoring at incident amplitudes \(1.195/1.205\) gives **36/38** events while both net wave works and HF load remain positive. Couplings \(k_h=0.118/0.122\) give **36/40** events, again positive works. Different event histories invalidate a smooth finite-difference inverse proof even if both operating points are individually restored. No universal perturbation robustness or proven unique zero crossing.

This corrects the earlier J17 recommendation to treat higher spark heat as higher useful output and simultaneously makes a stronger, defensible **two-objective** test available: \(W_{\rm net}>0\) and separately paid \(W_{\rm HFload}>0\) with \(\Delta U\approx0\). It does NOT establish a physically implemented load, a real HF energy-dump waveform, model-unique parameters or environmentally sourced power.

## Acceptance and remaining max-cut

[Exact local J18 extension](../../scripts/check_smith_filsinger_j18_hf_spark_tank_20261123.py) Git blob `430520c86fc471deada48835c7d048888745d2fa`; [J18b restored and source/branch controls](../../scripts/check_smith_filsinger_j18b_restored_hf_dump_20261123.py) Git blob `69cf86bddff854f7e427f3445acbf9eceb3be66c`; both independently byte-matched and executed locally with SymPy 1.14.0 / NumPy/SciPy. Commands (from clean checkout):

```bash
python scripts/check_smith_filsinger_j18_hf_spark_tank_20261123.py
python scripts/check_smith_filsinger_j18b_restored_hf_dump_20261123.py --stage core
python scripts/check_smith_filsinger_j18b_restored_hf_dump_20261123.py --stage pairs
```

[Machine receipt](../../Artifacts/smith-filsinger/j18_hf_spark_tank_restored_reverse_20261123.json). Each result is a conditional dimensionless model with source/authorship retained and original empirical work gates still OPEN. GitHub Actions and Agda kernel not invoked.

Next max-cut, in existing owner order: **J19** source-conditioned event branch / transverse crossing and phase-return mapping instead of blind finite difference; **F13** source-specific Duga HF, HAARP electrojet and SURA nonlinear propagation + receiver terminals, with independent source/clock measurements still absent; **F10/F15** same-original true electrical input/output/ground/field/loss and independently replenished work; **Q3/OCT369** separate gravimeter/momentum-stress channel for HF superconducting/Pais/YBCO (not added as electric fuel). If actual Filsinger coil, diode and spark terminals are never source-observed, leave topology branches conditional and continue mathematical reverse cuts.

**Attribution:** original narrated Filsinger spark-bank and midpoint concept; existing Circuit36927, J12 and J17 source owners; Maxwell/Lorentz/ADE and HAARP/SURA original experimenters remain their own first sources. J18 is a new independent conditional mathematical consumer, not first invention of an HF spark transmitter or validated historical apparatus.

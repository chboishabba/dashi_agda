# J20 — HF matched-wave orientation × actual capacitive OFF return × the two distinct 100% limits

**23 November 2026 | PR #1537, base master | Local Python 3.13, SymPy 1.14, NumPy 2.3.5, SciPy 1.17.** A new source-conserving *conditional mathematical consumer* of the **existing** J12/J18 nine-state Filsinger candidate; no empirical RF or electrically pin-mapped original device. User-directed steelman of 100% incoming-wave capture and 100% load work, separately and jointly, with strict attribution to original Smith/Filsinger and external Duga/HAARP/SURA/Pais/YBCO owners.

## First source-preserving distinction

There are three **different denominators**:
1. Receiving-wave **capture**: \(\eta_{\rm capture}=1-W_{\rm outgoing}/W_{\rm incident}\). \(100\%\) requires exactly zero output at the selected matched wave port for positive original incident work.
2. Conditional **HF internal routing**: \(\eta_{\rm HFload}=W_{\rm HFload}/[W_{\rm HFload}+W_{\rm gap}+W_{\rm coil}+W_{\rm freewheel}]\), on a restored HF state. \(100\%\) requires zero positive resistive losses **inside this selected branch**; it does **not** mean that all incoming-wave energy reaches that branch.
3. Real **environment-to-load energy conversion**: only definable on a measured, same-apparatus physical boundary with controller work and independent source isolation. Simple \(W_{\rm HFload}/W_{\rm incident}\) is a *model ratio*, **not causal source attribution if the controller is also active**.

The former J19 \(R_{\rm free}=0\) sets only one resistor's dissipation to zero. It does not supply an observed conductor or source. **We now test a genuinely different candidate topology** as an alternate branch, rather than promoting a missing resistor to a lossless wire.

## J12 wave-port rotation: an exact critical-matching result

With native \(h=\sqrt{2\gamma_r}\) and \(\Gamma=\gamma_r+\gamma_i\), define \(w=q+iz\), \(s=s_r+is_i\). J12's unmodified wave equations at *zero electric-secondary coupling* \(k=0\) imply
\[
  \dot w=-(\Gamma+i\omega)w+h s,\quad s_{\rm out}=s-hw.
\]

For **resonance-matched input quadratures** \(s=A e^{-i(\omega t+\phi)}\) (opposite to the **previous fixture's** \(s=Ae^{+i(\omega t+\phi)}\)), the stationary solution is \(w=(h/\Gamma)s\). The reduced linear wave reflection is exactly
\[
 \frac{P_{\rm out}}{P_{\rm incident}}=
 \left(\frac{\gamma_i-\gamma_r}{\gamma_i+\gamma_r}\right)^2.
\]
Thus \(\gamma_r=\gamma_i\) yields **exact 100% capture in this isolated linear port**. With the prior counter-rotating input, the denominator is \(\Gamma+2i\omega\); merely adjusting wave amplitude cannot achieve the same resonant matching. This is a source-orientation/mode-selectivity mathematical test, **not** proof any real Duga or HAARP wave has the required phase, polarization or frequency.

The **full** J18 HF/coupled coil/spark/diode circuit is nonlinear and has \(k>0\), so the reduced-mode result is an admissible *target*, not a proof that its full-state reflected field is zero.

## Native nine-state source owner and reactive OFF topology

Retain original J12/J18 \((i,j,u,v,b,q,z,i_h,x)\), all work integrators, spark on/off hysteresis, source/return identities, and dimensionless clock. J18 original script [is now optionally parameterised](../../scripts/check_smith_filsinger_j18_hf_spark_tank_20261123.py) at exact locally verified Git blob **f4270a475f010874056cfe3cdeff5ee8e43c44eb**:
- \`wave_handedness=-1\` changes only \(s_i\) to \(-A\sin(\omega t+\phi)\). Its DEFAULT +1 matches every previous J18/J19 run.
- \`off_return=capacitive\` replaces the OFF-state dissipative resistance with the **hypothetical closed inductor-capacitor path**. The HF inductor's return current charges the existing nonlinear capacitor even while the spark is OFF; the bank supplies the HF branch only while ON.
- The full HF energy remains
\[
 U_h=\tfrac12 L_h i_h^2+C_h(\tfrac12x^2+\tfrac34\alpha x^4),
\]
\[
 L_h\dot i_h=\chi b-x-(R_{\rm coil}+\chi R_{\rm gap})i_h-k_hu,\quad
 C_h(1+3\alpha x^2)\dot x=i_h-G_Lx,
\]
\[
 \boxed{\dot U_h=\chi b i_h-k_h u i_h-(R_{\rm coil}+\chi R_{\rm gap})i_h^2-G_Lx^2.}
\]
The bank loss \(-\chi b i_h\) and reciprocal secondary \(+k_hu i_h\) exactly cancel the HF internal transfer. This is **not a proven original pin connection** or evidence a real spark-gap can switch losslessly.

Exact default-regression J18 ↔ J12 remains PASS (max original seven-state difference about \(5.45\times10^{-9}\)). J18b's original baseline and J19's zero-\(R_f\) acceptance have merely been **repinned** to the new J18 Git blob; both default physical equations remain unchanged. Local J20 tests use [the actual newly committed J20 executable](../../scripts/check_smith_filsinger_j20_perfect_capture_reactive_return_20261123.py), Git blob **ed09b82287ec1ca0318b4f8e9d355f614d00d894** and J19 blob **cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439**. All three blob hashes were reproduced from the locally executed exact bytes. No GitHub Actions / CI or Agda kernel.

## Restored-cycle Pareto results

All rows are dimensionless mathematical synthetic fixtures with \(\omega=1.1\), input amplitude 1.2, phase 0.3, original other J12 parameters, \(R_{\rm free}=0\), and the newly **capacitive** return unless otherwise stated. \(\gamma_r=\gamma_i=0.04\), matched incident handedness -1. Every row shown passed full nine-state repeated-cycle closure and signed work tolerance.

| Fixture | Wave capture | HF internal load fraction | HF-load work | Spark events | State closure |
|---|---:|---:|---:|---:|---:|
| Original finite \(R_{\rm coil}=0.05,R_{\rm gap}=0.09\) | **98.9123%** | **98.7329%** | **0.237302** | **8** | \(7.19e-7\) |
| Ideal **zero HF coil and gap resistances** (rest unchanged) | 98.9124% | **100%** | **0.242062** | 8 | \(6.85e-7\) |
| Same ideal zero HF losses and **weak k=0.05** | **99.9758%** | **100%** | **0.070972** | **6** | \(1.79e-6\) |
| Finite loss, increased \(k_h=0.18,G_L=0.32\) | **98.9615%** | **97.8777%** | **0.811701** | 12 | \(1.82e-8\) |
| Original finite loss, controller OFF + wave ON | **99.0108%** | 98.8108% | **0.142596** | 22 | \(2.02e-8\) |
| Original finite loss, controller ON + wave OFF | not defined (no incident wave) | 98.8322% | **0.028611** | 20 | \(1.84e-8\) |

Original model J19 had 68 switch events, \(+0.139489\) net wave work and HF load 0.079664 at \(R_f=0\) using **counter-rotating** input and an unverified resistive OFF path. These are **not the same operating-point conditions** as J20; numerical ratios across them are only *model comparison*, not measurements.

Most consequential negative control: the **99.9758%-capture + 100%-HF-subcircuit** fixture has only **0.070972 HF-load units** out of **90.477868 units incident** (about **0.07844% as a model numerical ratio**, with **positive controller work 24.8543**). The field internal loss is **90.319749 units**. This is a mathematically decisive *counterexample* to the inference that near-perfect capture plus perfect downstream HF routing implies perfect **end-to-end** energy transfer. The designated HF resistive sink is also not an independent commercial useful-load meter.

Likewise, the **higher HF load 0.811701** occurs with finite HF loss and 98.96% capture, while internal field damping remains **87.962725** and controller work **24.667513**; the load-to-incident ratio of about **0.897%** is NOT a causal environmental energy efficiency.

**A new stronger source-only result** occurs in this separately hypothesised reactive topology: driver OFF + wave ON reaches a numerically restored cycle with positive load 0.142596, but it requires the full **external prescribed incoming wave of 90.477868** model units per cycle, with ~88.275785 dissipated through field damping. It is neither self-running nor evidence of a natural high-power Filsinger receiver. Driver ON + wave OFF also powers a load (0.028611), with **different switching histories (20 vs 8 / 22 events)**.

## Switching-event negative controls

Near the finite-loss matched 8-event restored point:
- source amplitude \(1.195\) vs \(1.205\): 8/8 ordered events, maximum paired shift **0.0045003**;
- \(k_h=0.1195\) vs \(0.1205\): 8/8 ordered events, paired shift **0.0101876**;
- \(\phi=0.299\) vs \(0.301\): 8/8 ordered events, paired shift **0.0066130**;
- \(G_L=0.155\) vs \(0.165\): still 8/8 events but **0.0364086** time shift, **FAILS** J19's strict 0.02 time-matching gate; don't call the entire load sweep smooth.

The previous **counter-rotating \(k=0.05\)** one-port study had **99.9758%** apparent capture at the last checked interval but *no restored-cycle certificate* in that geometry. It is **not** this newly verified, matched-hand, capacitive-return fixture. Wider native J20 sweeps also observed non-restoring parameter directions. Global rank, uniqueness, and event-transversality proof **OPEN**.

## Cross-owner physics and next work

Duga's MHz HF pulse train and ~10 Hz envelope, HAARP's electrojet and F-region LF mechanisms, and SURA's original 8–9/17–18 kHz plasma waves **remain separate time-stamped sources**. None has a measured propagation/phase/polarization/rectification transfer map to the source-qualified Filsinger terminal of #1524 F10/F13. Matched synthetic \(\omega=1.1\) circular polarization is a **model signal**, not an observed Earth-wave mechanism. Pais HF gravitational-wave patent and YBCO static/rotating superconductor measurements remain a different stress/force/gravimeter channel and are not additional electrical energy supply.

**J21 next Pareto gate:** optimise **environment-to-load throughput**, not wave capture or HF internal delivery alone. First attack the original resonator's \(\gamma_{\rm internal}\) while re-matching \(\gamma_{\rm rad}\) and preserving source-only restored cases; then test controller-off/wave-on and matched load phase at the *same* event branch. Nonlinear spark return/no-return physical topologies remain separate hypotheses, and real absorption/loading/noise/radiation require measured Poynting and signed original V/I. A hypothetical HF superconducting return must additionally satisfy real material, quench, electromagnetic-force and thermal constraints. No exact 100% real power transfer or gravity modification established.

Attribution retained to original Filsinger/Smith circuit/source reports, 2005/2011 HAARP, 2025 SURA/2026 publication, Duga 1985/1991 original investigators, Pais patent and published YBCO null/claimed effects, and existing DASHI native J12/J18 authors.

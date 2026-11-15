# Smith / Filsinger — nonlinear dispersive source-response maximum cut

**15 November 2026 — follow-on after merged DASHI PR #1515**

## Original steelman and source integrity

Filsinger's original reel claims and Kelly/Darrer's compiled Smith figures are different source occasions and not verified equivalent netlists. The strongest testable interpretation remains: a comparatively small timed electric exciter alters phase, nonlinear constitutive response, effective access admittance and feedback, allowing useful work from an independently energised Earth/atmospheric system. Waveform intensity, capacitor voltage and reactive field circulation alone do not prove source work. This round deliberately moves from audio envelopes to an open Maxwell-side constitutive and source-port model. Keep distinct the [ZVS/shunt reel](https://www.instagram.com/reel/DfiqPnkPnP5/), [earth-ground reel](https://www.instagram.com/reel/Dfi1D7CPzyM/), [Smith midpoint/spark-gap commercial proposal](https://www.instagram.com/reel/Dfu9Jseviz9/), [Tesla terrestrial transmission](https://patents.google.com/patent/US787412A/en), [Smith Mexican application](https://patents.google.com/patent/MXNL02000035A/en), and [Lyden source claims](https://patents.google.com/patent/US12136824B2/en).

## New physically meaningful conditional constitutive identity

Take a causal local material state \(P(t)\) (polarisation, a **modelled effective internal degree of freedom**, not necessarily the actual plasma variable):

\[
D=\epsilon_\infty E+P,\qquad
\eta\dot P=E-\frac{P}{\chi(t)}-\beta P^3,
\qquad \eta,\chi,\epsilon_\infty>0,\ \beta\ge0.
\]

Set \(u=\epsilon_\infty E^2/2+P^2/(2\chi(t))+\beta P^4/4\). Then, **exactly**,

\[
\frac{du}{dt}=E\frac{dD}{dt}
-\eta\dot P^2-\frac{P^2\dot\chi}{2\chi^2}.
\]

The last term is an explicit signed **material modulation-work port**. Moving the constitutive parameter can inject **or recover** energy; it cannot disappear into an empirical ``Q factor'' or be called spontaneous natural work. Unlike an instantaneous capacitor model, \(P\) has relaxation/memory. When \(\chi\) is fixed, \(\eta\dot P^2\) is irreversible loss. This is a specified non-linear dielectric/relaxation model; no measured Filsinger \(\chi,\eta,\beta\) or ionospheric plasma identification is claimed.

### Hall/Pedersen crosswalk

In a neutral-frame ionospheric field \(\mathbf E'=\mathbf E+\mathbf v_n\times\mathbf B\), a standard magnetised form has \(\mathbf J=\sigma_P\mathbf E'_\perp+\sigma_H(\mathbf E'_\perp\times\hat{\mathbf b})+\sigma_\parallel\mathbf E'_\parallel\). Exact algebra gives

\[
\mathbf E'\!\cdot\mathbf J=
\sigma_P|\mathbf E'_\perp|^2+\sigma_\parallel|\mathbf E'_\parallel|^2,
\]

**independent of the Hall coefficient** in this frame. Hall currents can carry/redistribute response and contribute to coupled magnetic fields without themselves being a local Joule heating term. The neutral-wind mechanical energy exchange and global EM work must still be accounted for. This is relevant to the F-region → magnetosonic → E-region Hall-current source/receiver cascade [Papadopoulos et al. (2011) theory](https://doi.org/10.1029/2011GL047368), [2011 experimental ICD](https://doi.org/10.1029/2011GL049263), and current [2026 ion–neutral coupling review](https://link.springer.com/article/10.1007/s10712-026-09937-8); the published HF heater coefficients are **not** the tabletop apparatus's values.

## Distributed causal source–receiver ledger

Use nearest-neighbour line states \(V_j,I_{j\to j+1},P_j\), a **finite dynamic source capacitor** \(C_sV_s^2/2\), feed conductance \(g_s\), a small local drive, and a load. With \(I_s=g_s(V_s-V_0)\), \(C_s\dot V_s=I_{\rm recharge}-I_s\), the exact line + reservoir balance is

\[
\frac{d}{dt}(U_{\rm line}+U_s)
=V_sI_{\rm recharge}+V_{\rm drive}I_{\rm drive}
+P_{\rm material\,mod}-P_{\rm load}-P_{\rm line\,loss}-\frac{I_s^2}{g_s}.
\]

The **separate donor** identity is \(\int V_0 I_s dt=U_s(0)+\int V_sI_{\rm recharge}dt-U_s(T)-\int I_s^2/g_s\,dt\). An explicit synchronous local stencil has a strict *numerical* domain of dependence. The continuous semidiscretised ODE should **not** be described as having an exact zero signal outside a physical light cone; only full hyperbolic Maxwell/telegrapher PDEs with appropriate causal constitutive laws establish the physical wavefront. Every coefficient here is normalised, not measured Earth material or a ZVS electrical clock.

## Original numerical results — controlled model, not original apparatus

- **Four exact SymPy identities:** nonlinear time-varying material work; Hall–Pedersen Joule-power split; distributed-line port energy; paired-world source-work difference. **4/4 PASS.**
- **Eleven local pytest tests** including 16 time-resolved source/phase trajectories, no-source and zero-input controls and the fully integrated donor ledger. **11/11 PASS.** Separate discrete causal-cone test **PASS**.
- Baseline model (normalised, 9 receiving nodes, \(g_s=0.75\), \(R_{\rm load}=1.6\), \(\phi=0\)): initial source storage 30.0; final source storage 13.25433; natural source recharge work 0.228823; donor to line transfer 6.725723; feed resistance loss **10.248767**; driver work 0.001911; material parameter work 0.014702; useful load 2.345950; line/material loss 0.916880. All source and receiver work balance residuals are approximately \(10^{-14}\).
- Empty-source control with same small driver yields useful work \(3.83\times10^{-6}\); zero source and zero drive remains zero even if the material parameter varies. This is source-dependent extraction in the specified model, **not** evidence of Earth harvesting.
- Phase sweep at baseline: useful output varies only **2.34551–2.34781**, about **0.098%** across eight phases. The specific physically richer model is **not** a high-gain parametric amplifier; the positive source-work mechanism is real within the equations but the phase advantage is small for these coefficients.
- Joint impedance scan \(g_s\in\{0.1,0.25,0.5,0.75,1.5,3\}\), \(R_L\in\{0.4,0.8,1.6,3.2,6.4\}\) (30 points): best sampled \(g_s=3,R_L=0.8\) gives useful 7.2634, useful fraction of supplied/released work 31.24%, vs baseline 2.34595 and 13.81%. **Not a global optimum.** Extended sweep to \(g_s=24,R_L=0.8\) gives 11.197 useful and 43.69% fraction, still at the largest g boundary. Any claimed finite hardware optimum therefore needs a source-conductance/geometry/control-cost constraint; increasing \(g_s\) is not cost-free access to Earth.

## Exact mathematical gates closed at a specified scope

| ID | Status | Owner / acceptance |
|---|---|---|
| M1 nonlinear dispersive material-work identity | exact SymPy PASS | `check_smith_filsinger_dispersive_port_symbolic.py` |
| M2 Hall and Pedersen signed work separation | exact SymPy PASS | same |
| M3 distributed line + donor source work | symbolic and numerically conserved PASS | symbolic + finite-line solver |
| M4 two-world signed difference balance | exact SymPy PASS | symbolic |
| M5 causal local stencil and memory | local exact cone check PASS | local and committed stencil |
| M6 finite source-depletion, recharge, drive/modulator/load work | 16 model cases PASS | finite-line solver |
| M7 joint source-feed and load-impedance bounded-grid optimisation | 30+20 tested, no hardware optimum | optimization scripts and JSON |
| M8 repeated-cycle vs finite donor depletion | **source-authored Agda**, kernel OPEN | `SmithFilsingerDispersiveMaterialPortExact.agda` |

## Exactly what remains physically open — no artificial gate closure

- **S0 / A1**: source-attributed same-object wiring with actual capacitor banks, shunt terminals, diode polarity, core and Earth/plate connections; different reels cannot be conflated.
- **P1 / A2**: simultaneous actual driver, switch phase, electrical V/I, microphone and capacitor/load work at the same operating point.
- **P2**: environmental source response with changing load/phase, including measured source impedance and any nonlinear retarded source operator (not chosen ad hoc).
- **R1 / A3 / B1–B3-PHYS**: one hardware-selected nonlinear switched model reproducing all sonic regimes and output work with a common parameter set.
- **R2 / C1–C2**: spatial same-object Maxwell/plasma solution with Earth–atmosphere/ionosphere geometry, conductivity, lightning background, Hall/Pedersen, and actual excitation transfer; the current model is a rigorous *selected material and 1D line example*, not this solution.
- **R3 / C3**: positive signed natural-field work over matched, *repeatable state* cycles, above input/controller losses and without simply drawing down the precharged environment.
- **D1**: Agda 2.9 exact-head kernel checking (not available in this runtime), new source ledger remains a **source-written contract**, not kernel-accepted.
- **D2**: source-to-theorem BIDI: real device measurements and original paper/patent vs claim attribution receipts.

### Most important next acceptance boundary

The finite-reservoir case is constructive, **not sustained environmental harvesting**: for the baseline, 0.2288 replenishment work does not compensate 16.7457 donor depletion over the selected interval. The unresolved original endpoint is therefore **same-object source access with sufficient *ongoing* replenishment** and verified real power delivered across the load. That is the frontier, not the existence of nonlinear mode conversion or a large global stored capacitor.

## Additional gate M9: exact repeatable-cycle source requirement

Using the same simulated source, line, material and controller states, the necessary natural replenishment work for a *repeatable whole-system cycle* is

\[
W_{\mathrm{recharge,needed}}=W_{\mathrm{load}}+W_{\mathrm{distributed\ loss}}+W_{\mathrm{feed\ loss}}-W_{\mathrm{driver}}-W_{\mathrm{material\ mod}}.
\]

This equality applies only if the **complete** source, line and material stored-energy state returns to its starting value. More generally the missing recharge is exactly the decrease in total stored energy in the run. In the baseline \(g_s=0.75,R_L=1.6\), required replenishment is **13.49498**, actually provided **0.22882**; the remaining **13.26616** comes from whole-system depletion. At the highest-tested \(g_s=24,R_L=.8\), required replenishment is **17.65259**, actually provided **0.17693**, shortfall **17.47566**—approximately a **100×** replenishment deficit. These are *normalised*, model-specific figures; they must not be read as real Earth watts. The exact differential-source ledger and local source-cycle test now implement this as **M9 source-closure discriminator**, not as a second 'energy conservation discovery'.

For the actual Smith/Filsinger claim, this makes the endpoint precise: demonstrate a causally closed **ongoing** Earth/atmospheric replenishment path supplying the measured complete-cycle load and losses under matched input/driver/phase controls—not merely an initial global Earth capacitor energy reserve or a transient output rise. The 2025–2026 global-circuit literature constrains candidate sources but does not certify local source admittance.
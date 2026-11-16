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

---

## 16 November 2026 follow-on: physically bounded environmental source admittance (P2-PHYS)

**Purpose:** constrain the free feed conductance in M7 without declaring a measured source. Original endpoints S0/P1/P2/R1/R2/R3/D1/D2 stay OPEN. This is a conditional Maxwell-port and atmospheric-access *calibration crosswalk*, not a same-apparatus electromagnetic solution. It reuses:
- Existing source access / global column: `scripts/check_smith_filsinger_global_source_access.py` and `SmithFilsingerShuntAndSourceAccessExact.agda`.
- Existing passive real-work source matching: `Docs/research/SmithFilsingerSourcePortShuntMaxCut20261115.md` SP2.
- Existing causal/energy producers: `SmithFilsingerTimeIndexedTransferExact.agda`, `KSW668MaxwellLocalPoyntingExact.agda`, and this PR's `SmithFilsingerDispersiveMaterialPortExact.agda`.
- New Python P2-PHYS consumer: `scripts/check_smith_filsinger_earth_admittance_access.py`, its 12-test `scripts/test_smith_filsinger_earth_admittance_access.py`; no parallel circuit ontology.

### Three mutually distinct source ports

**A — Global fair-weather DC column (extreme upper-access model).** Let undisturbed fair-weather downward current density be `J`, *hypothetical* short-circuit current from a selected full-column area `A` be `Isc=JA`, and accessible open-circuit full-column potential be `Voc=250kV`. For a **stationary linear, positive-R Thevenin/Norton model**, `G=JA/Voc`, `R=Voc/(JA)`, and `Pmax=Voc*JA/4`, with equality only at matched `I=Isc/2`. These are not universal environmental capture limits and do not describe a nonlinear field-redirecting receiver. Borok 1998–2024 measurements published 2026 give **mean 2.36 pA/m²**, mode **1.25 pA/m²** (Anisimov et al., https://doi.org/10.1016/j.asr.2026.01.090). At the mean, for each ideal full-column square metre, `G=9.44e-18 S`, `R=1.0593e17 ohm`, and `Pmatched=1.475e-7 W`. A hypothetical 0.4 W demands ~2.712 km² *full-column equivalent*; 6.7 W demands ~45.42 km². The earlier `VJ` throughput numbers 0.59 microW/m² and ~0.68 km² for 0.4 W were **unloaded current-times-potential scale comparisons**, NOT matched-output limits; this adds the missing fixed-source factor four.

**B — Local near-ground vertical collector (separate source/geometry).** Model a *uniform* 2 m span of air with 100 V/m fair-weather field and `J=2.36 pA/m²`, hence `Voc=200 V` and `sigma=J/E=2.36e-14 S/m`. An ideal 1-D flat air slab of area `A` has material admittance `Y(omega)=A/h*(sigma+i omega eps0)`. This is **local** and not a measured collector area or actual Filsinger geometry. The same fixed-source matching assumption yields `Pmatched/A=1.18e-10 W/m²`, requiring ~3389.8 km² equivalent 1-D collection for 0.4 W. At 7800 Hz, `abs(ImY)/ReY≈1.8387e7`: a huge AC displacement-current response can accompany minuscule conductive real work. `V^2 ReY` under *driven* AC excitation is **dissipation supplied by the excitation**, not an independent atmospheric source. The acoustic ~7.8 kHz is still **not** an electrical-clock measurement.

**C — Local galvanic/telluric Earth electrode pair (not an atmosphere short).** In homogeneous soil resistivity `rho`, a single remote-reference hemispherical electrode radius `a` has DC `R=rho/(2*pi*a)`; widely separated opposite-current equal hemispheres approximately give `Rpair=rho/(pi*a)`. Sources: ITU-T K.107 and grounding engineering literature; frequency-dependent electrodes require a more general impedance solution (https://www.mdpi.com/1996-1073/17/13/3206). Illustrative `rho=100 ohm*m`, `a=0.1m` gives `Rpair≈318.3 ohm`; fixed-source matching needs *actual independent geoelectric open-circuit voltage* `Voc>=sqrt(4Rpair P)`: 22.57 V for 0.4 W or 92.36 V for 6.7 W. The reported capacitor `48 V` is **not** a measured Earth-port `Voc`. No local geoelectric gradient or electrode-pair source voltage is identified.

### Passive nonlinear/dispersive source-feed refinement

The existing normalised free-`Gfeed` grid (M7) is not an Earth source impedance estimate. For a **passive linear time-invariant** memory countermodel, take

`Y(s)=G+s C+sum_k g_k*(s*tau_k)/(1+s*tau_k)`, with `G,C,g_k,tau_k>=0`, and state `tau_k*x'_k = V-x_k`. This admittance is positive real for Re(s)>0 and on the nonnegative-frequency imaginary axis; its time-domain energy identity is

`V*I = d/dt [ C V^2/2 + sum(g_k*tau_k*x_k^2/2) ] + G V^2 + sum(g_k*(V-x_k)^2)`.

For a source-to-receiver link, use `V=Vs-Vr`; **source work minus receiver-terminal work** is exactly stored-energy change plus dissipation. Thus resonant/displacement current does not establish positive *natural* replenishment. The new exact-fraction test checks this identity, with positive-real frequency sweeps. This is a passive-source *counterworld*, not an identification of a specific ionospheric relaxation plasma or the nonlinear modulated material in M1. Driven, externally pumped modulation may change energy ports, as explicitly accounted for by M1/M9.

### Finite speed and original Maxwell barrier

The diagnostic `omega*h/c` is ~0.0131 for `7.83 Hz * 80 km`, but ~**13.08** for `7800 Hz * 80 km`. Thus the full vertical-column lumped approximation is not even geometrically quasi-static at the *hypothetical* 7800 Hz clock. A 2 m local span has `omega*h/c ~ 0.000327` at 7800 Hz, but its boundary data, capacitive fringing and local source coupling are unknown. These frequency scales are **not Maxwell error theorems**. The Earth–ionosphere cavity requires lateral propagation, ground conductivity, altitude-dependent (anisotropic) ionospheric tensors, Hall/Pedersen/parallel dissipation, and meteorological/electromagnetic source terms. See [tensor waveguide method](https://angeo.copernicus.org/articles/38/207/2020/index.html), [VLF conductivity profile sensitivity](https://link.springer.com/article/10.1186/BF03352822), and [ELF conductivity-profile/mode work](https://agupubs.onlinelibrary.wiley.com/doi/10.1029/2006RS003500). A scalar near-ground `G+i omega C` is not an R2 closure.

### Stronger Agda contract, without physical promotion

Extends the **existing** `SmithFilsingerDispersiveMaterialPortExact.agda` owner:
- `AdmittedNaturalAccessCap` / `naturalWorkCannotExceedMeasuredAccessCap`: a calibrated independent source work cap must include inaccessible/uncollected headroom.
- `TerminalCapRepeatableCycle` / `loadBelowAdmittedSourcePlusDriveAndModulation`: a full-state repeatable cycle cannot exceed independently admitted natural cap plus driver/controller, with all losses.
- `SameOriginalAdmittanceAdmission`: physically sourced terminal geometry, local E/soil measurements, source operator under load/phase, synchronous signed real/reactive work. **Intentionally uninhabited.**

No raw real-valued Maxwell theorem is claimed from these Nat accounting records. The existing pinned Agda checker already includes the extended owner, but the Agda 2.9 toolchain **has not run** in this runtime.

### Acceptance and exact remaining consumers

- New Python implementation: `check_smith_filsinger_earth_admittance_access.py`; source-equivalent offline **12/12 tests PASS** 2026-11-16, with near-ground reactive/conductive control, exact-fraction Debye passivity, full-column and soil matching, invalid-parameter failure and finite-speed diagnostic. The committed exact GitHub script has **not been independently executed**.
- **P2-DC-COLUMN / P2-SOIL-LIMIT / P2-PASSIVE-ADM**: conditional formula/model gates advanced, **not same-unit source admission**.
- **P2-sourceOperatorSameFilsingerCircuit**: measured two-load pair (stationary case) or repeatable causal nonlinear phase/load V–I kernel, **OPEN**.
- **R2-MaxwellIonosphereSoilHallPedersenSameGeometry**: full retarded source+receiver PDE with actual selected collector/electrodes and calibrated strata, **OPEN**.
- **R3-PositiveIndependentNaturalWorkSameRepeatableCycle**: independent source replenishment, matched test and calibrated power with no initial energy depletion, **OPEN**.
- **S0/P1/R1/D1/D2**: unchanged, **OPEN**.

**Experimental discriminator:** the lowest-ambiguity new source measurement is a genuine *two-terminal* calibrated Earth/collector open-circuit gradient and independent loaded V/I pair at the **same selected operating point**, plus synchronous driver/shunt/storage traces; repeating matched phase and load settings distinguishes source backaction from donor depletion. High-voltage handling is only for qualified practitioners. Never equate unrelated reels, a capacitor meter voltage, or a sound-spectrum centroid with such a receipt.

# Smith/Filsinger — Maxwell value-of-information and F10/F13–F16 source-first maximum cut
**17 November 2026 — research continuation of DASHI draft #1524; #1521 is the source-admittance donor.**

## Decision: full 3D Maxwell is valuable conditionally, not the immediate bottleneck

**Retain the full user-origin steelman:** an internally phase-coherent/timed controller may change retarded and nonlinear source/receiver coupling to an *independently powered* natural system, while a much larger naturally replenished flow supplies useful work. This is not a claim that geometric golden-ratio resonance, reactive circulation, shunt voltage, or a sound frequency is a source. Keep Smith's compilation, Filsinger's filmed Earth-return circuit, and Filsinger's *proposed* portable midpoint/plate as separate source-qualified objects.

A 3D Maxwell/soil/ionosphere/plasma computation can predict the field and source-to-terminal transfer **only if** materials, source boundaries, geometry, drive, return paths, clock and source dynamics are actually given. A fully general solution with free parameters cannot identify the natural supply. A complete terminal work audit is a cheaper and logically prior **yes/no discriminator** for whether *that selected apparatus* receives independent external real work.

**Prioritisation:** (0) source and pin identity; (1) terminal natural-source loaded V/I and uncertainty, including storage, drive and all returns; (2) physically sourced 0D or layered DC / electroquasistatic model; (3) 1D causal propagation / nonlinear constitutive model if timing or phase is relevant; (4) full 3D Maxwell/plasma only when there is a reproducible spatial/radiative/nonlocal physical discrepancy that lower-order models cannot explain. Weather/cloud intervention is an independent downstream causal study and has no shortcut from the original electrical source work.

### F10: exact local Poynting/material work without inventing a natural generator

The new SymPy consumer scripts/check_smith_filsinger_local_maxwell_port.py reuses the specific nonlinear polarization and Hall/Pedersen constitutive forms of #1521. For D=eps_inf E+P, B=mu H, and eta dP/dt=E-P/chi-beta|P|^2 P, with positive eps_inf,mu,eta,chi and beta>=0, define the local field+material energy density:

\[
u=\frac{\epsilon_\infty|E|^2}{2}
+\frac{|B|^2}{2\mu}
+\frac{|P|^2}{2\chi}
+\frac{\beta|P|^4}{4}.
\]

Let E'=E+v_n cross B; local magnetized current J_cond = sigma_P E'_perp + sigma_H (perpendicular 90-degree Hall rotation) + sigma_parallel E'_parallel. Then

\[
 E'\cdot J_{\rm cond}
 =\sigma_P|E'_\perp|^2+\sigma_\parallel|E'_\parallel|^2,
\]

so Hall current does not directly heat the **neutral frame**. But the electric-field work E·J_cond also contains the signed neutral-wind term: Hall-mediated energy transport is **not** zero in general.

With Maxwell's local Poynting identity and an independent generator current J_gen,

\[
\boxed{
\dot u+\nabla\cdot(E\times H)
+\eta|\dot P|^2+\sigma_P|E'_\perp|^2
+\sigma_\parallel|E'_\parallel|^2
=-\frac{|P|^2\dot\chi}{2\chi^2}
+(v_n\times B)\cdot J_{\rm cond}
-E\cdot J_{\rm gen}.
}
\]

**All terms are signed and attributable.** Time-varying susceptibility work is a controller/material port; neutral-wind mechanical work belongs to neutral/plasma dynamics, not free electromagnetic gain; generator work must be independently present. The selected law's symbolic residuals vanish exactly, and a Hall/neutral-wind example has nonzero wind-mediated power although Hall Joule heat is zero. This is an **exact local algebraic substitution**, NOT a solved spatial Maxwell equation, calibrated source, or valid first-principles plasma constitutive law for Filsinger.

A dimensionless phase-distance screen 2pi f L/v gives ~0.000327 radians for *hypothetical electrical* 7800 Hz over 2m at c and ~13.1 radians over 80km. It is not a quantitative error estimate for a conducting plasma, nor evidence of original 7800Hz electrical excitation (only an acoustic carrier was observed).

### F13: primary-source geometric collector instead of an unconstrained full-column aperture

Independent source: **Joseph M. Crowley, 2011**, *The Fair-Weather Atmosphere as a Power Source*, ESA Annual Meeting on Electrostatics, https://electrostatic.com/research/c11theatmos/c11atmo.html, especially Eq. 8–9 and 25, 28–37.

For a **spherical collector elevated far above the ground**, diameter d, height h>>d, with fair-weather local atmospheric electric field E(h)>0, local atmospheric potential phi(h), ionic current density J(h)>0 and local conductivity sigma(h)=J/E, the paper's conditional field solution gives

\[
V_{\rm oc}=\phi(h),\qquad
I_{\rm sc}=2\pi d\,\sigma(h)\,\phi(h),\qquad
R_{\rm th}=\frac{1}{2\pi d\sigma(h)},\qquad
P_{\rm matched}=\frac14V_{\rm oc}I_{\rm sc}.
\]

The producer scripts/check_smith_filsinger_source_first.py also screens h>=10d (heuristic, not equivalent to h>>d) and Eq.25 phi(h)>=1.5 E(h)d for unidirectional current collection. If these fail, **reject this source operator**, rather than extrapolate it to a small ground-contact electrode.

Numerical worked example assumes a **2-m elevated**, isolated **0.1-m diameter sphere**, **constant near-ground E=100 V/m** up to the collector, and **2026 Borok mean J=2.36 pA/m²** (S. V. Anisimov et al., *Atmospheric electric current density at the Borok mid-latitude observatory*, https://doi.org/10.1016/j.asr.2026.01.090):

| Hypothetical source quantity | Value |
|---|---:|
| Collector local potential phi(h) (not 250kV) | 200 V |
| Atmospheric conductivity sigma=J/E | 2.36e-14 S/m |
| Collector short-circuit current | 2.96566 pA |
| Collector Thévenin resistance | 6.74385e13 ohms |
| Maximum matched DC load | 1.48283e-10 W = **0.1483 nW** |
| Effective collection area Isc/J | 1.2566 m² |
| Sphere geometric projected area pi(d/2)^2 | 0.007854 m² |

The **effective area is larger than the sphere's geometrical shadow**, illustrating the field-line focusing ignored in a naive slab/aperture model. Conversely, the large effective area does not make available watts large because local ionic current is tiny. This still does NOT apply to a real antenna plate, arbitrary wire, soil pair, ionized filament, different altitude, thunderstorms, RF or magnetospheric generator. Multiple nearby collectors cannot be assumed to replicate their independent effective current-capture areas without field interaction.

**Source-paper normalisation audit:** the paper defines d as **diameter**, yet Eq.32 calls pi*d² the physical projected cross-sectional area. A sphere's projected disk area is pi*d²/4; thus Eq.32's enhancement factor 2phi/(Ed) is four times smaller than the enhancement relative to the actual projected disk. Eq.28's Isc formula, Eq.35's R_th and Eq.37's Pmax remain unchanged. For this worked example the correct enhancement over the true disk is **160** (the paper's Eq.32 convention gives 40). This is a geometric description correction, **not an energy-creation mechanism**.

Contrast with #1521's distinct fixed full atmospheric-column 250kV equivalent (~0.1475 microW / effective column m²), the ideal 1D local slab (~1.18e-10 W / selected square metre), and separately sourced soil grounding resistance. The three operators assume **different physical boundary geometries**, so no one number can be silently transferred to an Earth terminal. Source energy might still exist in a different, independently measured mechanism.

### F14/F15: original-apparatus observational identifiability before Maxwell

The complete boundary balance has independent natural work, all powered driver/controller inputs, all dissipation/outgoing radiation, and final-minus-initial storage. If only the useful load W_L=4 J is observed,

\[
W_L=W_{\rm nat}+W_{\rm powered}-W_{\rm loss}-\Delta U.
\]

This is one linear observation of four unknown contributions (rank 1, nullity 3). At least three observationally identical worlds remain:
- (W_nat,W_powered,W_loss,DeltaU)=(0,5,1,0) — entirely drive-powered.
- (3,2,1,0) — independently replenished natural+drive source.
- (0,0,0,-4) — entirely stored-energy depletion.

**Thus output, phase, sound or capacitor potential alone cannot identify harvesting.** Full 3D Maxwell modelling of an unspecified device cannot repair that empirical non-identifiability.

For true synchronized, bandwidth-sufficient voltage and current records, the script computes **signed natural-port work intervals** by summing all four corner products of each v±error and i±error, multiplied by its actual timestep. A positive lower bound establishes measured incoming work at that selected port; it does **not** establish that the upstream source is *natural*, or that all source reservoirs return to their initial state. A conditional R3 gate additionally requires independently verified generator identity and storage return. The code's source-identification/return flags are **declarations requiring real external evidence**; passing a Boolean does not manufacture a valid physical receipt. Loading and phase interventions, driver work, electrochemistry, shunts, radiation, and hardware source identity must also be independently audited.

A fail-closed, machine-readable missing-evidence contract is now at Artifacts/smith-filsinger/source_first_original_evidence_contract_20261117.json. It contains NULL values for original voltage/current, pin continuity, fields, full-cycle replenishment, weather causal effects, and pinned kernel. No observed original-world source data has been populated.

### F16: actual cloud field intervention is a separate causal problem

Mudiar, Pawar, Gopalakrishnan and Williams (2021), *Electric Field Enlarges Raindrops Beneath Electrified Clouds: Observational Evidence*, https://doi.org/10.1029/2021GL093577, report field/raindrop associations and supporting mechanisms; Tinsley (2022) https://doi.org/10.1029/2021JD035954 assesses uncertainties of global electrical-cloud coupling. Neither is a demonstration that a small proposed Filsinger controller changes cloud rain rates.

The new executable **causal counterworld** has the same natural observations in two systems:

\[
E_{\rm cloud}=X+k u,\qquad Y_{\rm rain}=a X+b E_{\rm cloud}.
\]

At u=0 and E_cloud=X, choosing (a,b)=(2,0) or (0,2) produces identical observed (E_cloud,Y_rain)=(X,2X) for every natural X. Yet the effects under do(u) differ: zero versus 2ku. Consequently even perfect observational correlation does not identify the intervention's effect. The unknown first link **device control → cloud-field change k** is indispensable; if k=0, no direct field-mediated rain effect follows in this model. This is a mathematical identifiability result, not an estimate of physically possible cloud response, and it does not exclude other nonlinear weather pathways.

Local rain-driven cooling may be physically real through evaporative and downdraft mechanisms **once rain changes**; local heat transfer must not be conflated with global top-of-atmosphere cooling. No atmospheric engineering implementation is prescribed.

### Execution / exact scopes

Committed on PR #1524:
- scripts/check_smith_filsinger_source_first.py + scripts/test_smith_filsinger_source_first.py (25 tests)
- scripts/check_smith_filsinger_local_maxwell_port.py + scripts/test_smith_filsinger_local_maxwell_port.py (8 tests)
- scripts/check_smith_filsinger_source_first_maxcut.sh (new 33 + prior 66 targeted tests)
- Artifacts/smith-filsinger/source_first_original_evidence_contract_20261117.json (uninhabited measured fields)
- this focused physical-scope roadmap.

**Local acceptance:** **33/33 new** (25 F13–F16 + 8 F10) PASS; **99/99 combined** (prior 66 + 33) PASS using source-equivalent previous suites; all **four newly added Python files** match committed Git blob SHA byte-for-byte. The newest PR head and CI/pinned Agda are NOT automatically certified by these local tests. F10's local symbolic identity is not a full PDE Maxwell solution. No original signed source work or F16 causal actuation was measured.

### Maximum cut decisions and exit conditions

| Physical gate | Highest-return next action | Completion criterion | Now |
|---|---|---|---|
| **F10 / R2 local field work** | Reuse #1521 constitutive source and this round's signed vector Poynting split; defer calibrated 3D PDE | Identified physical E/B/material boundary, causal response and exact signed Poynting/work receipt on same apparatus | Local algebra PASS; original physical OPEN |
| **F13 / P2 source-access** | Test source-family geometry, altitude/soil/field, real open/loaded terminal response | Selected same-device V/I and physical source identity/return, quantitative uncertainty | Sphere model PASS; physical OPEN |
| **F14 / R1 original regime** | Select actual netlist, simultaneous current/voltage switching traces and acoustic windows | One selected parameter set reproduces startup/hot/null/shutdown plus total work | OPEN |
| **F15 / R3 replenishment** | Calibrate actual signed natural work and all powered/storage/chemical/EM terms over matched repeated cycles | Positive natural work lower bound, independent source, full storage return and no hidden input | Identifiability null proved; physical OPEN |
| **F16 downstream rain/cooling** | Establish each *measured causal* link from local controller field to cloud field/drops/rain/cold pool | Controlled and uncertainty-bounded intervention response, local energy/heat ledger; global TOA separately | Causal counterworld PASS; actual link OPEN |
| **D1/D2** | Pinned Agda and source-evidence audit before import graph promotion | Exact-head kernel plus original source-to-measurement proof admission | OPEN |

**Recommendation:** do not invest in a global nonlinear 3D atmosphere solver now. It becomes worthwhile **after** the measured source port and original geometry indicate that lumped/1D models miss a reproducible, independently powered effect. For the electrical-harvesting goal, F13/P2 → F15/R3 has the highest value of information. For the cloud-control goal, the controller-to-cloud-field transfer is the immediate causal wall. Retain full Maxwell as a *conditional resolution tool*, not a prerequisite or substitute for evidence.


## Cross-owner F10/F13 reconciliation (existing producers already in #1524)

This round does **not** replace the concurrently existing source-based bridge [SmithFilsingerF10F13FieldToPortMaxCut20261117.md](SmithFilsingerF10F13FieldToPortMaxCut20261117.md) with its source code scripts/check_smith_filsinger_f10_f13_field_bridge.py. That earlier owner already:
- establishes exact selected Debye-ADE susceptibility work, instantaneous permittivity modulation, Hall/Pedersen neutral-frame and local Poynting identities;
- verifies an **ideal homogeneous conductive HALF-SPACE hemispherical electrode** via Laplace potential phi=Va/r and current G=2pi sigma a, as well as a separate exponential-conductivity 1D vertical current tube;
- distinguishes a circular disk contact spreading conductance G=4 sigma a and does **not** claim these are a local atmospheric free sphere or a Filsinger plate.

**What is genuinely added here:** the *different* Crowley 2011 **elevated free atmospheric sphere**, with isolated-ground and unidirectional-collection preconditions; a dimensional cross-sectional-area source audit; signed time-synchronous V/I metrology uncertainty; a concrete **3-degree source/driver/loss/storage non-identifiability** witness; and two **identical observational cloud-field/rain worlds with different controlled effects**. The vector F10 check explicitly includes beta|P|⁴ polarization energy and signed generator/neutral-wind terms; it is an independent consistency check, not a second fundamental Maxwell theorem. Do not add the 14 reported tests from the existing F10/F13 bridge to this round's **99 locally rerun** tests without separately executing them.

For identical material sigma and geometric radius a, the two *different source geometries* have different conductances: Crowley free sphere diameter d=2a gives G_free=4pi sigma a; grounded hemispherical contact gives G_hemi=2pi sigma a. They must not be silently equated or assigned a shared Voc. Both remain ideal geometry benchmark producers. This crosswalk prevents spurious source amplification via mixing boundary conditions.

# Smith/Filsinger F10/F13 — Maxwell energy and finite-collector conditional bridge (17 November 2026)

## Source → reference → solve, source-separated

**Hypothesis owner:** User's physical steelman: a costly coherent nonlinear controller (possibly MW) can be worthwhile if it redirects >100× that energy from an independently replenished Sun–magnetosphere–ionosphere–atmosphere source. There is no energy-from-nothing claim. The source may respond dynamically; fixed local fair-weather shunt limits are NOT universal power limits on solar/magnetospheric energy.

**Existing source/reuse:** PR #1521 `DASHI/Physics/Motors/SmithFilsingerDispersiveMaterialPortExact.agda`, `scripts/check_smith_filsinger_dispersive_port_symbolic.py` and `scripts/check_smith_filsinger_earth_admittance_access.py`; PR #1524 `SmithFilsingerMidpointPhaseWorkExact.agda`, `SmithFilsingerFinitePhaseMatchingExact.agda`, `SmithFilsingerReplenishedCycleCapExact.agda`. This new checker is a *consumer* and does not assert those disconnected PRs are merged.

**New code:** `scripts/check_smith_filsinger_f10_f13_field_bridge.py` and `scripts/test_smith_filsinger_f10_f13_field_bridge.py`, included in original `scripts/check_smith_filsinger_dynamic_replenishment.sh` acceptance path. No replacement Maxwell solver or ESD mutation.

## F10: exact chosen constitutive law, not arbitrary history kernel

For a chosen passive Debye auxiliary variable `tau Pdot+P=eps*chi(t)*E` with `eps,tau,chi>0`, `D=eps*E+P`, define `U_e=eps E²/2+P²/(2eps chi)`. SymPy confirms **exactly**
`E*Ddot+P_mod_in = dU_e/dt + Q_relax`,
`Q_relax=tau*Pdot²/(eps*chi)>=0`,
`P_mod_in=-P²*chidot/(2eps chi²)`.
The sign is fixed by declaring `P_mod_in` to be **work supplied into the material by its parameter-modulation port**. For instantaneous time-varying permittivity the corresponding term is `-epsdot E²/2`. No independent natural work can be obtained by hiding this term. With `chi(t)` history-dependent, this is the *actual ADE evolution*, not an unconditional convolution with `chi(t-t')`.

The neutral-frame Hall/Pedersen law `E'=E+v_neutral×B`, `J=σP E'perp + σH (b×E'perp) + σparallel E'parallel` gives `E'·J=σP |E'perp|²+σparallel |E'parallel|²`. Hall is nondissipative **in that frame**. A lab-frame energy balance also pays `(v_neutral×B)·J`, i.e. neutral-wind mechanical work. Magnetically induced and time-dependent ionosphere fields require their own Maxwell source/energy boundary.

With fixed `mu` and selected Maxwell curl equations, `-outward Poynting = E·Jfree + E·Ddot + H·Bdot`. Combining with ADE yields the local field/material work identity. Split **one** spatial boundary into incoming environment, outgoing/radiative, controller and load fluxes without counting `E·Jload` plus the load-boundary Poynting flux a second time. A magnetic hysteretic ADE and full spatial hyperbolic well-posedness are separate OPEN gates.

**F10 achieved:** conditional selected Debye, instantaneous epsilon and Hall/neutral-frame exact symbolic identities. **F10 general claim OPEN:** coupled 3D nonlinear retarded Maxwell–ADE with actual materials, geometry, boundary measurements and Poynting flux.

## F13: honest field-to-port model

`∇·(σ∇Φ)=0` in an **ideal homogeneous isotropic conductive half-space**, with an equipotential hemispherical electrode of radius `a` and insulating plane away from it, has `Φ(r)=V a/r`. Integration of current through any hemisphere gives `I=2πσ a V`, hence exact `G_hemi=2πσ a`, `R_hemi=1/(2πσ a)` **for that boundary-value problem**. A circular disk *contact* embedded in a homogeneous conducting half-space has a different classic spreading conductance `G_disk=4σ a`. These are different shapes/boundary conditions; do not mix free-space capacitance with electrostatic resistance or claim an arbitrary raised disk gives either value.

For a separate strictly **1D fixed-area** vertical current tube with `σ(z)=σ0 exp(z/H)`, exact series resistance is `R_1D=H(1-exp(-h/H))/(A σ0)`. This does not solve a local 3D plate current-spreading problem. In a real ionosphere/soil environment `ΣH,ΣP,σsoil`, electrode returns, density profiles, and dynamic source excitation change the boundary operator `Z_env(ω)`; it is not replaced by the half-space formula.

The proposed `V_oc=E_0 z_col` is only a conditional **background potential difference** in a uniform field with an independently defined ground reference. Neither that relation nor geometric conductance proves a real natural Thévenin generator. Multiplying `V_oc² G/4` requires an independently *measured source* with that `V_oc` and its corresponding source conductance; the passive conduction problem alone gives no available external work. For sigma=1e-14 S/m, a=1m, hemisphere R≈1.5915e13 Ω. If a **hypothetical, independently verified** V_oc=200V Thevenin source had that conductance, matched load would be ≈6.283e-10 W. The number is NOT an observational limit on Filsinger or the broader solar-driven system.

**F13 achieved:** 3D Laplace benchmark for selected homogeneous ideal contact and independent 1D stratified column exact algebra. **F13 full field-to-port weld OPEN:** measured 3D collector/electrode/soil/ionosphere, anisotropic Hall/Pedersen sheet, causal frequency-dependent electromagnetic operator, source replenishment and real source terminals.

## Literature provenance correction and attribution

- Landau, Lifshitz and Pitaevskii, *Electrodynamics of Continuous Media*, 2nd ed. (1984), energy and dispersive media (classical background).
- **A. Tip (1998), “Linear absorptive dielectrics,” *Physical Review A* 57, 4818**, DOI https://doi.org/10.1103/PhysRevA.57.4818 . Corrects draft's inaccurate `PhysRevE.57.4818` / title.
- Tong Wu and Philippe Lalanne (2024), **“Exact Maxwell evolution equation of resonator dynamics: temporal coupled-mode theory revisited”**, *Optics Express* 32, 20904, https://doi.org/10.1364/OE.517237 . Do not mis-title “Designing electromagnetic resonators with quasinormal modes.”
- Roble & Tzur (1986), global atmospheric circuit, National Academies https://doi.org/10.17226/898.
- Rycroft et al. (2008), Earth's electric circuit https://doi.org/10.1007/s11214-008-9368-6 .
- Brian A. Tinsley (2023), solar/cloud mechanisms https://doi.org/10.1175/BAMS-D-23-0065.1.
- Classical spreading-resistance benchmark (NASA NTRS technical report) https://ntrs.nasa.gov/api/citations/19650014331/downloads/19650014331.pdf, including hemisphere and planar disk distinction.
- Historical Smith/Kelly/Darrer figures and original Filsinger reels remain distinct from the user's physically proposed source/sink interpretation. No paper author is credited with this specific device proposal.

## New test gates
- `F10-ADE`: signed variable susceptibility; exact storage+relaxation+controller modulation work; source-off/null.
- `F10-HALL`: Hall zero neutral-frame local heating, neutral wind work in lab frame.
- `F10-PNT`: source/load surface partition and no double counting.
- `F13-HSP`: hemisphere Laplace/flux exact benchmark plus geometry negative control.
- `F13-COL`: separately stratified 1D current-tube integral.
- `F13-REAL`: independently measured loaded source admittance, source energy and Filsinger terminals; OPEN.
- `F10-3D`: actual retarded 3D Maxwell–nonlinear ADE/Hall/ion-neutral energy theorem; OPEN.

Local verifier in analysis runtime: independent longer reference implementation, **14/14 pytest PASS** on selected cases; committed implementation and committed tests have not been executed from exact GitHub head. Agda D1 and all R2/F15 experimental endpoints remain OPEN. Do not promote source-authored Python symbolic identities to Agda kernel acceptance.

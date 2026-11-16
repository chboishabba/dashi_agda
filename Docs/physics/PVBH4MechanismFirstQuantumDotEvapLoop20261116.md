# PV x BH4 methodology: mechanism-first catalogue and quantitative discriminators (16 Nov 2026)

**Status:** source-indexed formal mechanism inventory; Agda kernel check **not run**; the external numerical tests are synthetic and not measured photovoltaic gain. This supplements draft PR #1523. Scientific sources retain original authorship and measurement context.

## Why BH4 is the correct formal precedent

Existing DASHI `DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda` separates identified species, exact finite reactions, unresolved formula/charge entries, measured kinetic parameters, outside exchanges, and the observed phenotype. `DASHI/Biology/BH4Phase4SystemStateRegression.agda` asserts explicitly that database linkage, kinetic parameter availability, stoichiometric balance and source credibility **do not** imply in vivo flux. The new PV lane adopts this methodology: finite mechanism family -> source-aligned state/stoichiometry -> transport and constitutive rates -> complete external ports -> causal interventions -> calibration and held-out discrimination.

**Required state**: wavelength/angle-resolved photon bins; electronic levels and occupations; excited-state populations, spins and charge states; electric/magnetic field history; extracted charge and terminal voltage; gas ion/electron populations, optical complex refractive response; water liquid/vapour mass and pressures; thermal reservoir temperatures. An unknown rate, gain or material interface must not be silently replaced by zero.

### Mechanisms to keep distinct

| ID | Mechanism and input | State transition / competing sinks | Evidentiary physical outcome |
|---|---|---|---|
| M01 | Passive PV: photons -> excited pair | radiative emission, nonradiative recombination, collected carrier | spectral EQE, V-I curve and net terminal work |
| M02 | Thin-film dichroic / luminescent spectral guide | angle/polarisation-dependent reflection, transmission, escape, absorb/reemit | measured passive transfer/scattering matrix, same aperture |
| M03 | 369/C3 Hamiltonian plus optical dipole | character selection of allowed matrix elements; oscillator strengths not fixed by group | SAME-material Bloch + dipole + transition absorption, compared to symmetry-broken control |
| M04 | QD confined Stark/Floquet drive | E-field deforms carrier wavefunctions -> shifted absorption, altered radiative strength, tunnelling | spectral shift, time-resolved absorption & signed drive energy |
| M05 | QD multiple exciton / singlet fission | one high-energy event -> multiple excited pairs, Auger and separation competing | EQE >1 measured along with usable maximum output voltage |
| M06 | Diamond NV two-photon photocurrent | NV- -> excited NV- -> NV0 + free electron; spin dependent intersystem crossing | zero-bias and biased net P-V/EQE, dark/control; do not discard diamond before comparison |
| M07 | Living photosystem / bioelectrode | exciton -> charge separation -> EET/respiration/repair | source-synchronised EET rate, electrode V-I, maintenance, lifetime and illuminated area |
| M08 | RF air **refraction** | density/temperature/acoustic/index gradient -> phase/beam steering | interferometric delta-n, angle-dependent transmitted/scattered light and pump input |
| M09 | RF gas **absorption / opacity** | electron/gas transitions -> absorption / heat / chemical excitation | complex permittivity, optical depth, heat/excitation storage and sustained drive work |
| M10 | Nonlinear HF photovoltaic capacitor | Q(V,t), delayed E(x,t), state-dependent absorption and carrier transport | simultaneous signed high-bandwidth V(t), I(t), E(t), optical EQE, bus work |
| M11 | First-stage water evaporation | PV-thermal Q into latent energy + evaporation mass | chamber pressures, wet-bulb, m_dot, Q_transfer, same panel T |
| M12 | Second-stage condensation / preheat | condensate mass recovered, latent heat transferred internally | Q_cond measured vs Q_preheat + Q_export + Q_loss |
| M13 | Compression/heat-pump thermal upgrade | Q_hot = Q_cold + W plus rejection | work, compression ratio, temperature lift, COP |
| M14 | Heat engine/steam, deferred hardware | upgraded heat -> work + condenser rejection | future closed steam cycle; not implied by the heat pump |

Some mechanisms are established independently (e.g., QC Stark and NV photocurrent), while the cross-coupled photovoltaic architectures are *hypotheses*. The catalogue distinguishes these rather than declaring them tested as one system.

### Exact reusable core

- `DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact`: Fourier/rotation commuting square, already exact in its abstract model.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact`: source-selected interaction-sensitive p² Coulomb term already paid, **not** full material PV gap.
- `DASHI.Physics.Chemistry.AtomicPeriodicTable369SymmetryProjectionCompilerExact`: same-object Hamiltonian/projection commutation.
- `DASHI.Mathematics.Symmetry.DiamondNearestNeighbourBlochExact` plus NV source owners: real crystal geometry donor, not measured NV PV power.
- `DASHI.Environment.PhotosyntheticLightTransportCrossPollinationExact` plus Biology/BH4 state/exchange and hydrology source: matched optical / biological mechanism.
- `DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact`: time delay and signed source/work receipts.

### Quantum-dot physical model and honest discrepancy

The **source experiment** Pein et al. (2017, https://doi.org/10.1021/acs.nanolett.7b01837) observed >0.5 eV strong THz-induced optical-gap shift in CdSe/CdS core-shell quantum dots, with field pulses and optically pumped luminescence. It attributes the effect to quantum-confined Stark deformation, beyond the weak-perturbation regime.

A proper first physical mathematical consumer is:
`H_e(F)=p²/(2m_e*)+V_e(r)-eF·r`;
`H_h(F)=p²/(2m_h*)+V_h(r)+eF·r`;
`H_ex(F)=H_e(F)+H_h(F)-V_Coul+H_exchange+H_disorder`;
`E_opt(F)=E_eh(F)-E_ground(F)`.
A symmetric dot has leading `delta E ≈ - (alpha_exc/2) F²`; at large fields, carrier localization, oscillator strength, tunneling, valence mixing and time dependence require actual calculations.

A 1D hard-wall *independent-particle* fixture (5 nm, m_e*=0.13m0, m_h*=0.45m0, bulk gap 1.8 eV, omitted Coulomb binding) gives 1.040657 meV redshift at 100 kV/cm and 4.120865 meV at 200 kV/cm. These are not the published measurements and certainly **do not reproduce the >500 meV** reported strong-field shift. This disagreement must be retained as an explicit model residual, not tuned away by fiat.

### Diamond: test first, discard only upon physical discrimination

Bourgeois et al. (2015, https://doi.org/10.1038/ncomms9577) show spin-dependent photoelectrical detection through NV two-photon ionization; biased photocurrent is not independent self-powered electric conversion. 2025 all-carbon Schottky NV devices show bias- and RF-sensitive photoelectric signals (https://pmc.ncbi.nlm.nih.gov/articles/PMC12672660/). Compare NV diamond defect density, charge-state lifetimes, 1- vs 2-photon absorption, contact bias input, incident-spectrum response, V-I curves (including V=0), and Pmax, on equal optical aperture to passive silicon and dot controls. Run finite toy and an actual physical experiment BEFORE accepting/rejecting it; cost is a later Pareto dimension.

### Biology: distinguish native and engineered power conversion

Wang et al., 2026 (https://doi.org/10.1038/s41467-026-72407-7) engineer conductive pili for extracellular electron extraction. A May 2026 membrane-exchange study reports an additional photocurrent improvement (https://doi.org/10.1016/j.greenca.2026.03.006). Changes in extracted current do not directly imply proportional electrical power conversion efficiency. Formalize `dN_species/dt = S v(N,light,temperature) + exchange - loss`; source energy, respiratory ATP draw, water splitting, cell maintenance and degradation/repair separate. Test engineered photosystems, isolated complexes, living electrodes and biohybrid films, rather than assume a crop-derived upper bound.

### Two-stage solar PV evaporative / condenser / heat-pump cycle

First-stage PV heat `Q_PV -> evaporation(m_dot h_fg)`. Second-stage vapour is condensed and the latent heat is partitioned `Q_cond = Q_preheat + Q_useful + Q_reject`. Condensate is pumped back, and heat-pump or vapour-compression work elevates the condensing temperature as necessary. Mass: `dM_v/dt=m_evap-m_cond`, `dM_l/dt=m_cond-m_evap`. Energy for chosen heat pump: `Q_hot = Q_cold+W_comp-Q_loss`.

**Illustrative one-square-metre example only:** solar in 1000 W, PV electric out 300 W, all 700 W balance assumed heat, 25 C evaporation, water latent enthalpy 2.44 MJ/kg => evaporate and condense ~1.033 kg/h. Ideal reversible heat pump to 70 C requires minimum `W=700*(343.15-298.15)/298.15=105.65 W` and supplies ~805.65 W high-grade heat before losses. At identical heat-source and environmental sink T=25 C, maximum ideal work from that output equals the compressor input: **no net thermal-to-electric gain**, but useful hot water and PV temperature control remain possible. Actual COP and condensation/evaporation pressures require source-matched measurements. When water is reheated as preheat, **do not send that heat straight back to the cold PV surface and count it as recovered output**. Condenser placement, humidity, noncondensable gas handling, sensible heat and the external sink are physical gates.

### Air optics and cloaking: distinct mechanisms

- Acoustic modulation of ambient-air optical index is experimentally established: Schrödel et al., Nature Photonics (2024), https://doi.org/10.1038/s41566-023-01304-y.
- Plasma/thermal filament-induced air guides and deflection have separate evidence, e.g., https://doi.org/10.1103/PhysRevX.4.011027.
- Scattering control or refractive lensing does not require visible plasma cutoff, nor does beam deflection imply broadband invisibility. For multi-angle optical applications, measure `phase, transmission, reflection, scatter, absorption, power-in` separately, comparing dark/ambient/drive controls. Keep use to basic research/optical diagnostics.

### Formal gates after this tranche

G0: source/version/author and same-object state identity; G1: all mechanism species and directed transitions; G2: mass, photon, charge and energy conservation without fabricated zeros; G3: constitutive/rate laws and positivity; G4: space-time boundary and retarded coupling; G5: optical/photonic density of states, C3 operator and real dipole; G6: test material Bloch/QD/NV/biology same-object export; G7: two-stage evap/condense/sink thermal topology; G8: measured work and independent controls; G9: held-out/same-aperture benchmark and manufacturing Pareto; G10: Agda local Golden acceptance and source/hash certificates.

**Not closed:** G0–G10 as physical end-to-end gates. `BH4StyleMechanismInventoryExact.agda` supplies source-typed finite catalogue and synthetic exact balance identities; it does **not** build the physical rate matrix or establish PV >50%.

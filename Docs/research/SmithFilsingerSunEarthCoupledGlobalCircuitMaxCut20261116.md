# Sun–magnetosphere–ionosphere–atmosphere–ground source/receiver gate (2026-11-16)

**Origin of hypothesis:** user-proposed extension of Smith/Filsinger: use selective THz/IR/laser and active-array field coupling to change a ground/atmosphere receiving interface and test upstream solar, ionospheric, cloud and climate response. **DASHI contribution:** conditional source boundaries, matched-trajectory methodology and type-level finite-work bookkeeping. No measured sun-to-ground harvest, climate intervention, sustained plasma bridge or kernel success asserted.

## Reuse and dependencies
Reuse, rather than replicate: `SmithFilsingerHybridRegimeStudyBidiExact.agda`, `SmithFilsingerTimeIndexedTransferExact.agda`, `Circuit36927RecoveryEnergyBoundExact.agda`, `MaxwellExteriorCalculusAdapter.agda`; `Docs/research/SmithFilsingerHybridStudyExactRemainingLemmas20261115.md`, `SmithFilsingerCausalNonlinearSourceRollup20261115.md`, `SmithFilsingerReverseRadarSourceOptimisation20261112.md`, `TeslaTowerEmitterMaxCut20261103.md`. New isolated owner: `DASHI/Physics/Motors/SmithFilsingerSunEarthCoupledSourceExact.agda`. No edits to ESD or TOE import surface until kernel/provenance gates pass.

## Physically different connected generators
1. **Solar radiation → atmospheric heat engine:** solar heating drives convection, cloud particle charging and thunderstorms; solar EUV/UV also photoionizes the upper atmosphere. Storms and electrified clouds maintain most of the ~250-kV global fair-weather ionosphere-to-ground potential. This is indirect solar work, not a continuous solar DC conductor.
2. **Solar wind → magnetosphere → high-latitude ionosphere:** magnetic reconnection, magnetospheric convection, field-aligned currents, Alfvénic Poynting flux, ionospheric Hall/Pedersen closures, ion-neutral heating and particle precipitation. A different dynamo than the thunderstorm global circuit, but coupled in the *polar branch* via the ionosphere/atmosphere.
3. **Ionosphere ↔ atmosphere ↔ ground:** spatially variable conductivity, aerosols, atmospheric ions, clouds and charge-current paths. Local changes in electrical boundary conditions can in principle redistribute potentials, natural currents, charge, Joule heating, atmospheric chemistry and cloud microphysics. The sign/magnitude of cloud or storm feedback is not presumed.

### Field model and perturbations
- Gauss: `div(epsilon E)=rho`; charge continuity: `d_t rho+div(J)=0`; EM induction `E=-grad(phi)-d_t(A)`.
- Selected medium: `J=Sigma_tensor(E,B,n,T,x,t) E + J_generator + J_advection`, with Hall/Pedersen and field-aligned/vertical current continuity, explicit retarded electromagnetic boundary response and energy flux `S=(E cross B)/mu0`.
- Electron population `d_t n_e=S_ion(E_RF,lambda,...)-L_attach-L_recomb-div(Gamma_e)`. A THz-field-induced response can involve seed-electron acceleration, collisions and nonlinear plasmas, **not** simple single-THz-photon molecular ionisation.
- Treat cloud charge, collision/coalescence, aerosols, phase change, wind/temperature/moisture and radiation as separately attributed constitutive components with observation operators and uncertainty, not assumed gain parameters.
- A prescribed sustained local electrode potential does not uniquely fix the global response. Solve the natural *source backaction* with all returns and boundary impedances, comparing tuned and control trajectories under **same exogenous forcing and initial state**, not identical realized natural power.

### A single, disjoint energy boundary
For the selected receiving volume:
`W_sunPhoton + W_solarWind + W_atmosGenerator + W_pump + W_initialStorageRelease = W_load + W_dissipated + W_radiated + W_finalStorageIncrease`.
Ports are only counted if their flux crosses this boundary without duplication. An outer Sun/Earth control volume has storm electrical generation as an *internal* conversion of solar/atmospheric energy: one must NOT count both absorbed sunlight and downstream thunderstorm electricity as independent external inputs. Under paired tuned/control trajectories:
`delta W_load - delta W_pump = delta W_realized_upstream - delta W_losses - delta U`.
The new Agda owner provides *conditional abstract* natural-number port separation and a finite-source work bound. It does NOT solve Maxwell–plasma, show accessible solar power, or have a pinned kernel receipt.

### Climate: redistribution vs genuine cooling
Latent-heat release by condensation is atmospheric heating paired with evaporation/transport, not direct loss of terrestrial energy. Condensing 1 mm/hour over 100 km² represents ~69 GW of *relocated latent heat*, not 69 GW removed from the Earth system. By comparison, a sustained 1 W/m² top-of-atmosphere imbalance over Earth's ~5.1e14 m² surface corresponds to ~510 TW. The global fair-weather electric circuit's ~250–750 MW throughput is no hard cap on *other* magnetospheric sources or potential nonlinear downstream feedback, but is small compared with the global radiative budget.

A climate-benefit claim must prove `delta(ASR - OLR) < 0` with global annual net top-of-atmosphere absorbed-solar versus outgoing-longwave flux, spatial feedback and hydrologic/environmental impacts. Cloud response has sign ambiguity: changed aerosol/droplet/ice properties can affect both shortwave albedo and longwave greenhouse trapping. Storm formation is not a direct consequence of extracting current; it requires atmospheric thermodynamics.

### Directionality and virtual aperture
Active real phased elements can shape electromagnetic fields by coherent superposition and may help distinguish source coupling, plasma-memory kernels and receiving geometry. SAR creates a *synthetic* aperture using phase histories and improves imaging resolution; it does not create instantaneous collecting area or energy. Compare actual pump watts, physically realized effective aperture, receiver load, conductivity lifetime and atmospheric loss; never equate a virtual focused image with watts delivered.

### 2026 state of art checks
- Lin et al. report strong source-frequency and Pedersen-conductance dependence of solar-wind ULF transfer to ionosphere **in global MHD simulations**, not measured energy harvesting.
- A 2026 Nature analysis argues that regression-to-the-mean explains some apparent polar-cap potential saturation. Do not assume either an unquestioned saturated source or infinite available source power: physically solve loading and validate against data.
- A 2026 ACS Photonics study reports plasma-filament-confined THz surface waves, showing hybrid laser/THz mode interactions at laboratory scale—not a persistent altitude-spanning ion bridge.

## Explicit OPEN acceptance gates
- `S1 solarSourceBidi`: source-separated solar photon/heat-engine vs solar wind/magnetospheric generator and correct field-aligned closure.
- `S2 globalSourceBackaction`: same external forcing, recalculated natural response, current continuity and boundary potential changes.
- `S3 MaxwellPlasmaGreenOperator`: causal retarded operator with physically measured conductivity/ionisation, chemistry and dissipation.
- `S4 THzIRControlComparative`: matched laser/IR/THz/hybrid/control comparisons in safe scaled models, useful conductance integral per joule.
- `S5 realVsSyntheticAperture`: source-target field and received power vs radar-like reconstruction, physically bounded.
- `S6 cloudChemistryDynamics`: identify sign and strength of charge → hydrometeor → cloud/precipitation/wind response.
- `S7 TOARadiativeBenefit`: annual net shortwave-longwave atmospheric feedback and hydrological/ecological externalities.
- `S8 signedEnvironmentalWork`: calibrated whole-cycle pump, source, storage, loss, useful load; distinguish replenishment from depletion.
- `S9 pinnedKernelAndSameOriginalAdmission`: actual Agda 2.9.0 pinned check, source-evidence tier and matched physical apparatus admission.
Original Smith/Filsinger C1/C2/C3 physical gates remain open and own downstream welds.

## Original authors and stable recoverable sources
All results credited to source authors; user-origin proposal and conditional DASHI abstraction are **not** claims of those authors.
- **R. Lukianova, A. Frank-Kamenetsky, J. Victor, A. Kozlovsky (2025)**, *Solar Wind–Ionosphere–Troposphere Coupling Via the Polar Branch of the Global Electric Circuit*, Surveys in Geophysics, https://doi.org/10.1007/s10712-025-09914-7. Polar branch plus Antarctic data; not a harvester.
- **D. Lin et al. (2026)**, *Efficiency of Electromagnetic Energy Transfer From Solar Wind to Ionosphere Through Magnetospheric Ultra-Low Frequency Waves*, GRL, https://doi.org/10.1029/2025GL118532. Global MHD modeled transfer; no receiver.
- **M. Blanc et al. (2026)**, *Physical Links Between Weather in Space and Weather in the Lower Atmosphere*, Surveys in Geophysics, https://doi.org/10.1007/s10712-026-09968-1. Two-way coupling review / observation gaps.
- **B. A. Tinsley (2022)**, *Uncertainties in Evaluating Global Electric Circuit Interactions With Atmospheric Clouds and Aerosols*, JGR Atmospheres, https://doi.org/10.1029/2021JD035954. Cloud associations/uncertainty, not climate control.
- **M. J. Rycroft, A. Odzimek, R. G. Harrison (2024)**, *Determining the time constant of the global atmospheric electric circuit through modelling and observations*, JASTP, https://doi.org/10.1016/j.jastp.2024.106267. Atmospheric RC and clouds.
- **(2026)**, *10 May 2024 Gannon Storm: Connecting Energy Flux With Field Aligned Currents and Cross Polar Cap Potential*, Space Weather, https://doi.org/10.1029/2025SW004776. Source/field-aligned simulations.
- **(2026)**, *Regression to the mean can explain saturation of geomagnetic storms*, Nature, https://www.nature.com/articles/s41586-026-10757-4. Statistical inference caveat.
- **(2026)**, *Laser Plasma Filament-Bounded Terahertz Surface Waves*, ACS Photonics, https://doi.org/10.1021/acsphotonics.5c03014. Experimental local filament, not long-range bridge.
- **NASA NISAR**, *Get to Know SAR*, https://science.nasa.gov/mission/nisar/get-to-know-sar/. Phase-history synthetic aperture.
- **NOAA**, *The Earth-Atmosphere Energy Balance*, https://www.noaa.gov/jetstream/atmosphere/energy. Evaporation/condensation energy directions.
- **IPCC AR6 WGI Chapter 7**, https://www.ipcc.ch/report/ar6/wg1/chapter/chapter-7/. Radiation/cloud feedback.
- HAARP two-stage F/E current, nonlinear delay, Schumann response and original Smith/Filsinger evidence boundaries retain their individual DOIs and distinctions in `SmithFilsingerHybridStudyExactRemainingLemmas20261115.md`.

**Validation state:** source-authored research and conditional proof, not kernel-accepted or physically admitted. No atmospheric manipulation or discharge implementation specified.

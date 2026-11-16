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


## 2026-11-16 addendum: rain-driven **local cooling**, mW control, Filsinger and Infoton attribution

### User-origin correction and hypothesis
The target was **rain cooling of the local lower atmosphere and surface**, not a claim that condensation in clouds makes the Earth's total energy vanish. Keep three consecutive but *not yet joined* links distinct:

(1) a small, controlled change in local electrical potential/conductivity;
(2) a potentially nonlinear, source-powered change in natural cloud droplet charge, collision/coalescence, rain rate, and cold-pool formation;
(3) lower-level air/surface cooling by evaporation, advection of cool downdraft air, surface evaporation, cold rain sensible heat transfer and rainfall-induced wind/circulation.

Natural electric-field effects on cloud particles and rain, and actual rain-induced cold pools, have individual published evidence. **No published source cited here shows mW electrical control producing sustained rain or measurable weather modification.** The difference in energy scales is not a refutation of gain in an open system, but a missing response-transfer function is not proof of it either.

### Local thermodynamic budgets and conditional example

Local atmosphere: evaporation of falling rain absorbs latent heat from subcloud air; downdrafts advect cooler air and create a gust front; evaporation after wetting the ground removes sensible heat from ground and nearby air; rain at lower temperature carries sensible heat from the ground or surface water. Cloud condensation releases latent heat at altitude, and the circulation can transport heat between layers and regions. **Rain can lower near-ground temperature without lowering total global enthalpy**.

For region A=100 km², precipitation equivalent R=1 mm/h: water mass flux rho_w A R = 1e8 kg/h ≈ 27778 kg/s. Using L_v≈2.45 MJ/kg, hypothetical subcloud evaporation of *all* precipitation gives 68.1 GW of latent cooling, BUT in that case the precipitation mass does not reach the ground. If a fraction f=0.1 evaporates before reaching the surface, cooling is ~6.81 GW in the subcloud air, subject to water-vapour saturation, vertical temperature/moisture profiles and transport; cooling is not the power delivered by an electrical controller. 69 GW of **condensation at cloud level** is a separate upper-air heating accounting entry and must never be relabelled as rain's surface cooling. Remaining rain sensible cooling and evaporating wet surfaces are separate terms. These are scaling examples, not achievable interventions.

A basic bulk air-parcel approximation for evaporated mass delta_m is delta_T ≈ - L_v*delta_m /(m_air*c_p) until wet-bulb/saturation constraints intervene. Useful outputs include spatially and temporally indexed:
- delta_T_surface and delta_T_2m, temperature anomaly duration, cold-pool geometry, moisture and sensible/latent heat changes;
- rainfall intensity and accumulated amount, evaporated fraction, precipitation redistribution, cloud and albedo response;
- control/input W and natural atmospheric enthalpy, potential energy and radiative flux changes.

For climatic implications, local cooling alone is a meaningful *local adaptation* response even if global TOA cooling is zero. Separately, any claim of long-run **global-warming reduction** needs net global radiative/heat storage changes, altered GHG emissions or other independently identified sinks. Do not conflate the two acceptance questions.

### Physical and mathematical test for tiny-control/high-gain response
In the shared open forcing, define controller u(t) and state x=(cloud charges, hydrometeors, q, T, wind, E, Sigma, plasma, fields, sources), with a matched unactuated control. Observable cold-pool response:
`G_cool = [∫_region∫_time (T_control - T_tuned)_positive rho_air c_p dVdt] / W_ctrl`
requires dimension correction: the numerator as written has units joule-seconds, hence define a **snapshot** cooling-energy anomaly `Q_cool(t)=∫_V rho_air c_p (T_control - T_tuned) dV`, or a separately specified *heat flux* integral in joules, then `G_snap=Q_cool(t)/W_ctrl`. Report it as a *response ratio*, not COP or an energy-generation efficiency: source-driven atmospheric latent/sensible heat transport is the energy supplier.
Better signed throughflow: `delta Q_surface(t0,t1)=∫_t∫_A (H_control-H_tuned) dA dt` (W/m² sensible/latent flux as chosen), plus explicit air-mass advection and stored-energy terms.
For very small electrical control (mW), first establish the field perturbation at the actual clouds, its charge/microphysics effect and an unforced matched comparison. No automatic scale-up of `d rain / d electric field` follows from naturally occurring electric fields or HAARP.

### Recovered Filsinger source boundary
**Original speaker assertion** (user-supplied reel narrative and repo source ledger) includes: "interacting with the cosmic radiation of the environment", and in a *proposed portable design*, replacing the Earth ground with a common-midpoint connection to a plate/antenna of claimed ~1:1.618 geometry to "harvest cosmic radiation". See existing `Docs/research/FilsingerEarthCosmicGoldenTwoModeOptimisation20261111.md`, `Docs/research/FilsingerLydenEarthPortMaxCut20261110.md`, and primary reel indices in `Docs/research/SmithFilsingerHybridStudyExactRemainingLemmas20261115.md`. Preserve original reel provenance: the narration makes the claim, the experiment has not identified the actual external energy port.

**Candidate interpretation (DASHI cross-paper inference, not speaker-verified):** "cosmic radiation" could mean incident radio waves, solar electromagnetic radiation, solar-wind-coupled geospace fields, atmospheric electric current or actual ionising cosmic-ray particles; these are different source domains. **Do not claim Filsinger explicitly measured solar-wind ionospheric power or that the proposed portable antenna was demonstrated.** To assign the solar coupling hypothesis to his apparatus requires independent, same-object calibrated ports, incident spectral irradiance/field, current and timing. Never deduce an ionospheric source from his ~7.8 kHz acoustic frequency (~7.8 Hz Schumann is different).

### Infoton thermodynamic cross-pollination
Existing `docs/research/InfotonP30WalkerMaxCut20261115.md` and `DASHI/ComputerScience/InfotonP30FiniteAuditExact.agda` explicitly separate reversible state evolution from irreversible erasure and distinguish `m(T)=k_B T ln 2/c²` as an **energy-equivalent mass expression**, not an experimentally observed Infoton particle. See January N. Walker original-source records in that ledger: https://infoton.ai/infoton-p30 and https://zenodo.org/records/18210355 . These are claims, not physical calibrations of weather. Reuse the useful boundary principle: information about control/phase/resonance changes *which path the physical energy takes*, not its source conservation law. If importing Landauer, count physical entropy generation for actual erasures and distinguish it from reversible modulation, heat, and latent energy transfers. Any thermodynamic-control-to-rain link is a **new conditional DASHI inference** and must not be attributed to Walker.

### Literature: direct cloud-electrification → rain evidence (critical additions)
- **Electric Field Enlarges Raindrops Beneath Electrified Clouds: Observational Evidence**, *Geophysical Research Letters* (2021), https://doi.org/10.1029/2021GL093577. Natural electric-field and raindrop-size observation and proposed coalescence mechanism; **NOT** demonstration of an artificially applied mW controller or weather control.
- **Ming Zhang, Zhiwen Yang, Chuan Li, Jiawei Li, Dingchen Li, Qixiong Fu, Kexun Yu** (2025), *Raindrop formation in a thunderstorm mimicking environment under non-uniform electric field*, *Physics of Fluids* 37, 022023, https://doi.org/10.1063/5.0251043. Laboratory storm-like, nonuniform field and charged-droplet regime, not atmospheric-scale intervention.
- **D. N. Gabyshev** (2025), *Condensational growth of spherical water droplets altered under external electric fields*, *Journal of Aerosol Science*, 106554, https://doi.org/10.1016/j.jaerosci.2025.106554. Theory of droplet growth under electric fields, not a real-world rain gain.
- **Brian A. Tinsley** (2022), *Uncertainties in Evaluating Global Electric Circuit Interactions With Atmospheric Clouds and Aerosols, and Consequences for Radiation and Dynamics*, *JGR Atmospheres*, https://doi.org/10.1029/2021JD035954. Reports atmospheric correlations and uncertainties, not a proved large control transfer coefficient.
- **Brian A. Tinsley** (2023), *Solar Activity, Weather and Climate, the Elusive Connection*, *Bulletin of the American Meteorological Society*, https://doi.org/10.1175/BAMS-D-23-0065.1. Review/interpretive source, not mW weather control.
- **R. G. Harrison and M. Lockwood** (2020), *Rapid indirect solar responses observed in the lower atmosphere*, *Proceedings of the Royal Society A*, https://doi.org/10.1098/rspa.2020.0164. Solar/lower atmosphere observation context.

### Literature: rain → real local cooling and cold-pool dynamics (critical additions)
- **Bastian Kirsch, Felix Ament and Cathy Hohenegger** (2021), *Convective Cold Pools in Long-Term Boundary Layer Mast Observations*, *Monthly Weather Review* 149, 811–820, https://doi.org/10.1175/MWR-D-20-0197.1. 489 events over 14 summers; median near-surface cooling **−3.3 K**. Humidity saturation deficit is stronger predictor than rain amount; wet-bulb evaporative cooling accounts for 64% of overall variance in simplified model, 92% subset without strong cold-air import. **Observation, not electrically controlled cooling.**
- **Evaporation and Cold Pools Beneath Trade Cumulus Clouds** (2026), *JGR Atmospheres*, https://doi.org/10.1029/2025JD044917. Isotope/in situ observations support below-cloud rain evaporation and cold-pool formation.
- **Air-Sea Heat Fluxes Associated With Convective Cold Pools** (2023/24), *JGR Atmospheres*, https://doi.org/10.1029/2023JD039708. 276 observational cold-pool events, threshold near-surface drop −1.5 °C in 10 min and altered air-sea heat flux. This is atmosphere-to-ocean/sea-air redistribution.
- **An Investigation of Hydrometeor Latent Cooling upon Convective Cold Pool Formation, Sustainment, and Properties** (2019), *Monthly Weather Review*, https://doi.org/10.1175/MWR-D-18-0382.1. Microphysical model; evaporation of lower-level rain helps explain cold-pool expansion, structure and intensity.
- **Rooney, van Lipzig and Thiery** (2018), *Estimating the effect of rainfall on the surface temperature of a tropical lake*, *Hydrology and Earth System Sciences* 22, 6357–6369, https://doi.org/10.5194/hess-22-6357-2018. Direct heat-flux and near-air cooling; tropical lake rainfall days lowered surface temperature in observational comparison by ~0.3 K at day end.
- **A Parameterization for Cloud Organization and Propagation by Evaporation-Driven Cold Pool Edges** (2024), *JAMES*, https://doi.org/10.1029/2023MS003982. Cold pool edges may organise further convection; modelled interaction and nontrivial feedback.

### Literature: coupled solar/ionosphere / field resonances / optical interfaces (verified)
- **Renata Lukianova, Alexander Frank-Kamenetsky, Jeni Victor and Alexander Kozlovsky** (2025), *Solar Wind–Ionosphere–Troposphere Coupling Via the Polar Branch of the Global Electric Circuit*, https://doi.org/10.1007/s10712-025-09914-7. Polar GEC mixed review and Antarctic analysis.
- **Dong Lin, Michael Hartinger, William Lotko, et al.** (issue 2026; first published Dec 26, 2025), *Efficiency of Electromagnetic Energy Transfer From Solar Wind to Ionosphere Through Magnetospheric Ultra-Low Frequency Waves*, https://doi.org/10.1029/2025GL118532. **Global MHD model**, not source port extraction.
- **Michel Blanc et al.** (published Oct 28, 2026), *Physical Links Between Weather in Space and Weather in the Lower Atmosphere*, https://doi.org/10.1007/s10712-026-09968-1. Whole-atmosphere coupling review, explicit knowledge gaps.
- **Nithin Sivadas, David Sibeck, Varsha Subramanyan, et al.** (2026), *Regression to the mean can explain saturation of geomagnetic storms*, *Nature* 655, 1143–1147, https://doi.org/10.1038/s41586-026-10757-4. Statistical correction disputes historical saturation interpretation, **does not bound available receiver power**.
- **A. V. Streltsov, T. Guido, B. Tulegenov, J. Labenski, C.-L. Chang** (2014), *Artificial excitation of ELF waves with frequency of Schumann resonance*, https://doi.org/10.1016/j.jastp.2014.07.004. HAARP strong resonance peak in **8/46** episodes, facility-scale drive (3.6 MW), **not mW input**.
- **Jiayu Zhao, Linlin Yuan et al.** (2026), *Laser Plasma Filament-Bounded Terahertz Surface Waves*, *ACS Photonics* 13, 1712–1718, https://doi.org/10.1021/acsphotonics.5c03014. Lab plasma/THz surface modes, **not ionosphere-to-ground conducting filament**.
- **NASA NISAR** synthetic aperture background: https://science.nasa.gov/mission/nisar/get-to-know-sar/ . Observational virtual aperture vs physically intercepted energy distinguished.

### Newly refined gates (all ORIGINAL-WORLD OPEN)
- `S4a tinyControlFieldAtCloud`: demonstrate same-original mW-class port creates specified change in actual cloud electric field/charge (or prove an upper bound) under independently recorded natural forcing.
- `S6a fieldToRainMatchedEffect`: separate natural-field correlation from induced counterfactual rain microphysics, with droplet charge/size, rain-rate and background convection confound controls.
- `S6b rainToCoolLocalEnergyExact`: calculate evaporated fraction, humidity, downdraft enthalpy, rain sensible flux, surface evaporation, local temperature response and storm feedback; accept observed real cooling even if TOA global balance unchanged.
- `S6c naturalFeedbackThreshold`: identify nonlinear threshold, sensitivity, saturation, spatial footprint, uncertainty and source-energy payment for any claimed high-gain atmospheric response.
- `S7a localCoolingVsGlobalClimateDistinct`: local heat relief (allowed without global radiative benefit) vs separate annual global radiative-climate effects; track redistribution and possible warming elsewhere.
- `S8a filsingerCosmicSolarPortBidi`: original speaker's cosmic claim, actual plate/antenna status and physically measured solar-wind/solar-photon/RF/cosmic particle source discriminator; do not silently promote interpretation into original fact.
- `S8b infotonThermodynamicBoundary`: energy/entropy/information control port separation, keeping Walker claims/physical validation distinct.


### SOTA bridge: Tinsley actually proposes an electrical amplifier driving cloud transducers
In *Solar Activity, Weather, and Climate: The Elusive Connection* (2023), https://doi.org/10.1175/BAMS-D-23-0065.1, Brian A. Tinsley explicitly characterizes the GEC cloud-microphysics proposal using a **semiconductor-amplifier / cloud-transducer analogy**. The hypothesis: variations in solar-wind-driven ionospheric potential and very weak vertical atmospheric current density change space-charge accumulation at cloud boundaries, modulate charged-particle scavenging, and may influence much larger radiative or latent-heat flows. Tinsley discusses observations, some solar-linked correlations and gaps/alternative explanations. This is **prior art for the physical control-amplification concept**, not a validated mW actuator or direct proof that an engineered receiver can initiate storms. Preserve author credit and distinguish the user's proposed *controlled receiver extension* from Tinsley's earlier naturally forced mechanism.

A useful mechanism graph, with evidence tiers on every arrow:
solar wind → ionosphere potential (physical established) → atmospheric J_z and charge boundaries (physical established) → cloud aerosol scavenging / droplet effects (theory, lab/natural observational support, uncertain extrapolation) → cloud rain/cold-pool response (natural mechanisms observed; electrically induced effect OPEN) → local surface temperature (natural storm observations established). The full **small-controller-to-cooling** concatenation is OPEN.

A local electrical actuator's mW power is a **controller input**, not the energy supplied to evaporation, cloud motion or solar-wind coupling. No 250–750 MW *global GEC throughput ceiling* constrains the latent heating of naturally driven clouds; conversely, it is false to infer useful actuator gain from the mere difference between those budgets.

### Precision issue: no frequency conflation
The 2014 Streltsov et al. HAARP experiment used a megawatt-class HF heater (reported 3.6 MW) whose modulation produced some observed ~7.8 Hz ELF responses. It is NOT evidence of comparable results with mW pumping; nor is Filsinger's acoustic ~7.8 kHz line evidence of the ~7.8 Hz global mode. Use separate Hz/kHz labels throughout.


## 2026-11-16 further user-origin hypothesis: **off-phase source/sink maintained by common midpoint and plate**

**User hypothesis (not a Filsinger quotation):** the common-midpoint and 1:1.618 plate may be intended to sustain a reasonably consistent *off-phase* pair of source/sink branches, instead of merely selecting two frequencies or geometries.

**Recovered original provenance, before cross-paper inference:**
- `Docs/research/FilsingerDonSmithGoldenRectangleLissajousMaxCut20261111.md` says the proposed topology creates a common midpoint, elevated plate, and opposite capacitor-polarity branches; it explicitly distinguishes the actually narrated Earth-ground arrangement from the unbuilt portable arrangement.
- `Docs/research/SmithFilsingerGoldenFibonacciSingleWaveMaxCut20261112.md` gives Smith compiled PDF pp80–82 Figs 53–55 as opposed/out-of-phase secondaries and rectifier arrangements, not a measured 90-degree circular surface current. It also distinguishes Smith 1:4 winding length and Filsinger golden plate as separate original claims.
- `Docs/research/SmithFilsingerNonlinearQuadratureMaxCut20261112.md` provides conditional nonlinear 2-mode exchange/energy ledger, not same-original physical couplings.
- `Docs/research/FilsingerEarthCosmicGoldenTwoModeOptimisation20261111.md` gives physically source-limited two-mode reference, including some phase circularity and loss/extractive damping cases, but has synthetic spectra and no actual Maxwell conductor result.

### Three candidate mechanisms—don't conflate
1. **Push–pull/opposed branches (180° voltage phase):** write terminal potentials `v_plus=v_common+v_diff/2`, `v_minus=v_common-v_diff/2`, so `v_plus-v_minus=v_diff`. For an ideal between-terminal branch with `i_plus=i`, `i_minus=-i`, instantaneous signed terminal work satisfies `p_plus+p_minus = (v_plus-v_minus)*i = v_diff*i`. Opposed *potentials* alone do not prove one port is producing net natural work, and a physical conductive/capacitive displacement return still must be selected.
2. **Orthogonal modes (near 90° quadrature):** a single coherent feed can drive two geometric resonances with modal responses `a_j=H_j(omega)s_j`, `H_j=(gamma_j+i(omega_j-omega))^-1`; the phase difference `arg(a_y)-arg(a_x)` is time stationary at fixed source frequency and parameters, even if the modes have different eigenfrequencies. When resonance splitting and damping are appropriately matched the phase can approach quadrature; this yields a rotating *field vector* or polarization but NOT automatically a closed Maxwell conductor-current loop or harvesting.
3. **Beating / nonlinear phase entrainment:** two independent self-oscillators with `omega_1 != omega_2` have `Delta phi(t)=Delta phi(0)+(omega_2-omega_1)t`, so geometry alone does not maintain a fixed off-phase relation. A common coherent drive or nonlinear injection locking can maintain a stable relative phase within a locking range; the actual coupling coefficient, phase noise and source backaction are OPEN.

The golden ratio may be useful as a geometric detuning or modal density choice, but it does **not by itself encode 90° or 180°**. In prior original-repo synthetic `Q=50`, `f_y/f_x≈1.618` and drive at the x-mode, the y-mode's amplitude is only ~0.03235 of x and the circularity ~0.06463; balanced quadrature requires reactive tuning, changed loading or common-drive design. This synthetic counterexample disallows promoting aspect ratio to a universal phase relation.

### What source/sink should mean physically
- Alternating *instantaneous* local power, capacitive stored energy and inductive reactive exchange are distinct from positive long-run *natural environmental* work.
- Under load, the phases of voltage, current and local E/B need separate definitions: `P_real=Re(V I*)/2` for peak phasors, not simply the sign of voltage.
- The fields may exchange energy internally between modal amplitudes, while both modes are being supplied by the powered ZVS. In a real *receiver*, a source/sink interpretation requires a signed environmental Poynting or electrical port plus sink load, pump and loss.
- For the Sun/atmosphere extension, the useful hypothesis is coherent, appropriately delayed differential **boundary modulation** that reduces pump cost or changes uptake from a naturally supplied field—not a self-generating opposite-phase source.

### Prior art / attribution
- S. K. Lee, A. Sambell, E. Korolkiewicz, S. F. Loh, S. F. Ooi and Y. Qin (2005), *A Design Procedure for a Circular Polarized, Nearly Square Patch Antenna*, Microwave Journal, https://www.microwavejournal.com/articles/935-a-design-procedure-for-a-circular-polarized-nearly-square-patch-antenna . Near-degenerate orthogonal modes with equal amplitude and quadrature phase require feed geometry/perturbation; not Filsinger data.
- *Temporal coupled-mode theory* for two resonators (2021 accepted APS manuscript), https://doi.org/10.1103/PhysRevLett.127.013902 . Detuning, reciprocal mode exchange and dissipation mathematics; this does not claim the Filsinger geometry has specified coefficients.
- Original Smith/Kelly/Darrer figure, Filsinger narrative and user interpretation are separately attributed above. The differential-port identity and proposed source/sink discriminator are **new DASHI extension**.

### New explicit OPEN gates, subordinate to S3/S5/S8 and original C1/C2/C3
- `S5b originalMidpointDifferentialPolarity`: reconstruct exact portable candidate ports from reel, keep source vs conjectured wiring separate; two signed capacitor branches, diodes, plate feed, reference and return.
- `S5c sourceSinkPhaseTransfer`: for the SAME physical configuration, measure/common-driver-reconstruct terminal `v,i`, modal E/B, cross-spectra, relative phase, bandwidth, loading and feedback stability; distinguish 180° differential from 90° polarization and two-tone beating.
- `S5d phaseLockVsGoldenGeometryCounterexample`: prove a stationary common-drive modal phase in a linear specified model; prove absent specified locking the free-running detuned phases drift; verify fixed phi geometry cannot alone guarantee balanced quadrature.
- `S8c sameEnvironmentalSourceSinkWork`: identify actual independently powered external field/work and delivered load work after ZVS input, storage, losses, passive reactive exchange. Use matched tuned/control boundary dynamics, not apparent terminal sign.

**Status:** source-checked conditional interpretation and paper provenance; no new Agda kernel certificate, physical phase measurement or claim of verified natural power transfer.


## 2026-11-16 steelman revision: finite propagation, time, nonlinear environmental coupling

**User-origin physical steelman (preserve in summaries and acceptance tests):**
> Filsinger's proposed common-midpoint, opposed-polarity and golden-aspect plate arrangement may be intended to create two coherently coupled electrical branches with persistent relative phase, producing a controlled differential electromagnetic interaction with the surrounding environment, **where wave propagation and time are critical components**.

The point is NOT a timeless electrostatic divider, a bare rectangle, or two stationary complex voltages. It is a finite-speed, dispersive, open, driven, nonlinear source–receiver system. Its physical roles:
1. The powered ZVS/switching + passive tuned circuit establishes reference timing and optional slow modulation; opposite terminals may provide a differential push-pull excitation. Geometry, dielectric, loading and mutual coupling affect relative phase and mode overlap but the aspect ratio alone fixes none of them.
2. The source to field to material to receiver transfer is **causal**: excitation at point x' and time t' changes observables at x and t only through a causal Green kernel G_ret(x,x',t-t'; media, state). Include ionisation/attachment/recombination memories; any electromagnetic paths respect propagation limits and any slower material delays are separate.
3. At a selected interaction region, phase is *after propagation*: for path transfer H_j(x,omega), arg E_2 - arg E_1 = arg(s_2/s_1) + arg(H_2/H_1), with H_j including the path/delay and material response. In an illustrative pure-delay case arg(H_2/H_1) = -omega(tau_2-tau_1), additional reactive and dispersive phases omitted. The relevant phase is **not** merely the phase measured at the driver.
4. For coherent common-drive modal steady response, near-stationary relative phase can be real even when resonant eigenfrequencies are split; for undriven/free-running detuned modes it generally drifts; nonlinear entrainment, feedback and field memory alter this. Critical timescales: switching period, driver envelope, group delay, pulse width, plasma lifetime, pole/ringdown decay, charge equilibration, natural-source replenishment and atmospheric/cloud response.
5. Both true real environmental work and purely reactive return can give apparent phase-sensitive changes and lingering pump-off responses. The energy source hypothesis is **independent natural supply** (Earth/ionosphere/solar wind/atmospheric/radiative port), not phase offset as an energy source. Any useful transfer must satisfy time-integrated boundary Poynting flux and signed v*i port work. Periodic reactive circulation may sum to zero net environmental energy over a cycle.
6. This extends to the user-origin atmospheric hypothesis: small active phase/time/conductivity control may redistribute a naturally powered flow and (if causal gain is verified) alter charged-cloud rain formation and downstream local evaporative/downdraft cooling. This is not proven to happen in the proposed hardware, and each cause/effect arrow requires distinct experimental admission.

### Mathematical source–receiver contract (DASHI extension, conditional)
Let physical state X(t) contain two driven resonators, spatial Maxwell E/B, material memory, natural source and receiver/load; input u(t), natural forcing s_nat(t), observation y(t).
\[
  y_i(t)=\int_{-\infty}^{t} G^{\mathrm{ret}}_{ij}(t,t';X)\,u_j(t')\,dt' 
       + y_{i,\mathrm{nat}}(t;X).
\]
G_ret is a *linearized causal response representation about X*, NOT a universal fixed linear convolution for nonlinear dynamic media. Full nonlinear PDE/integro-differential coupled evolution must be retained when phase control changes material state. In frequency domain for quasi-stationary selected media:
\[
  \Delta\phi(x,\omega)=\arg\!\left[\frac{s_2(\omega)H_2(x,\omega)}
                                     {s_1(\omega)H_1(x,\omega)}\right].
\]
Do not use a single frequency-independent delay for dispersive plasma or conflate group/energy transport with phase velocity. Phase can improve local field overlap or reduce losses; it cannot by itself pay load energy.

For ONE selected boundary:
\[
\frac{dU_{\rm included}}{dt} = P_{\rm driven}(t)+P_{\rm natural}(t)
 - P_{\rm useful}(t)-P_{\rm internal\,loss}(t)-P_{\rm outgoing}(t),
\]
where the signs and port crossings define every term and no secondary natural generator is counted twice. Compare matched **tuned and control trajectories with identical initial state and exogenous forcing**, but allow source backaction, natural replenishment, delay-dependent storage and environmental response to evolve differently.

### New explicit gates (all physical OPEN)
- \`S5e retardedPhaseAtInteraction\`: field/terminal phase at source vs RECEIVER across distance, with correctly separated electromagnetic flight, material group delay, switching, plasma memory; test phase coherence over the control bandwidth and load changes.
- \`S5f historyDependentNonlinearSourceReceiver\`: distinguish fixed transfer phasor from state- and history-dependent Green/Volterra/nonlinear response and delayed feedback; synthetic opposite-phase signals alone do not discharge this gate.
- \`S5g delayedReturnVsNewEnvironmentalInput\`: after pump switch-off, distinguish free ringdown, transported/returned old stored energy, independently replenished environmental work, and source- or observation-dependent multi-path delays.
- \`S8d matchedTimeResolvedPoyntingLedger\`: sign of cumulative natural power and net load work, including incoming/outgoing radiative work, time-resolved storage, ZVS supply and controller costs, not just RMS potential or acoustic carrier.

### Reused evidence and references
- **K. Papadopoulos et al.** *First demonstration of HF-driven ionospheric currents* (2011), https://doi.org/10.1029/2011GL049263: two causal stages (F-region modulated heating → magnetosonic propagation → E-region Hall currents and virtual radiating antenna), facility-scale source experiment, not Filsinger real power or measured mW gain.
- **M. B. Cohen et al.**, *Magnetospheric injection of ELF/VLF waves with modulated or steered HF heating of the lower ionosphere* (2011), https://doi.org/10.1029/2010JA016194: source-conditioned 3D heating/cooling, propagation, phase and steering matter; reported 5–7 dB modeled injection advantage for specified comparison, not a Filsinger conversion gain.
- **M. Gołkowski et al.**, *Amplitude and phase of nonlinear magnetospheric wave growth excited by the HAARP HF heater* (2010), https://doi.org/10.1029/2009JA014610: delayed echo arrival and nonlinear phase/amplitude evolution with source-strength-dependent onset; not a same-object Filsinger delay measurement.
- **Tong Wu and Philippe Lalanne**, *Exact Maxwell evolution equation of resonator dynamics: temporal coupled-mode theory revisited*, Optics Express 32, 20904–20914 (2024), https://doi.org/10.1364/OE.517237: standard temporal coupled-mode theory can miss full Maxwell terms in short-pulse, off-resonant or extended structures; motivation for not replacing retarded physics with an unconditional two-number phasor.
- **Thomas Christopoulos, Odysseas Tsilipakos, Emmanouil E. Kriezis**, *Temporal coupled-mode theory in nonlinear resonant photonics*, Journal of Applied Physics 136 (2024), https://doi.org/10.1063/5.0190631: framework for explicitly nonlinear and dissipative resonant dynamics, not source-specific verification.
- Earlier source-owned Smith/Filsinger reel, Don Smith Kelly/Darrer diagrams and mathematical owner ledgers above remain separate.

**Verification:** documentation-only continuation on draft PR, new gate statements neither Agda kernel proved nor physically admitted. The observed Filsinger ~0.303-s separation of acoustic pump-off envelope peaks is NOT by itself a Maxwell flight-time or environmental echo receipt.


## 2026-11-16 phase ↔ signed natural-work cross-PR acceptance

**Provenance and reuse:** This is a new *consumer* of the existing passive reciprocal reflection producer `scripts/smith_filsinger_reflection_energy_cut.py`, the coherent one-wave/two-mode producer `scripts/smith_filsinger_single_wave_fibonacci_modes.py`, `SmithFilsingerReflectedPortBidiExact.agda`, `SmithFilsingerTimeIndexedTransferExact.agda`, the source separation and work boundary in this PR, and the source-access/replenishment work in [PR #1521](https://github.com/chboishabba/dashi_agda/pull/1521). The proposed portable Filsinger midpoint/plate is separate from the demonstrated Earth reel and historical Smith drawings. The phase/source-sink interpretation originates with the user; the finite model and theorem statement are DASHI extensions. No ESD or TOE promotion surfaces were edited.

### Three coherence notions must not be conflated

- **Coherent single driver:** with fixed component parameters, both driven modes have a stationary *relative* phase. Positive real rescaling of the same driver does not change it. It is not a synchronization of independent natural radiation.
- **Retarded phase at the receiver:** even if the driver terminals are opposed, the local interaction-region phases depend on the separate retarded material/path responses `H1,H2`; pure sample delay gives `arg(a2/a1) - omega*(tau2-tau1)`. This simple phasor diagnostic is **not** a measured nonlinear Maxwell/plasma Green operator.
- **Independent natural source coherence:** the controller's relative phase to an independent incoming wave must remain known/stable for coherent interference optimisation. Under an independent uniformly random environmental phase, the phase-dependent quadratic cross terms cancel on averaging in the selected linear fixed-coefficient model. A nonlinear rectifying/memory/entrainment mechanism may differ, but must be separately modelled and sourced.

### Passive reciprocal two-mode/two-port example with actual backaction

The mathematical consumer `scripts/check_smith_filsinger_midpoint_phase_work.py` uses
```math
\dot a=(i\Omega-\Gamma_i-\Gamma_L-\tfrac12 KK^\dagger)a+Ks_+,
\qquad s_-=-s_++K^\dagger a.
```
Here `a` contains two energy-normalised modal amplitudes, `K` has **natural** and **controller** external ports, and outgoing waves include physically required backaction. For the steady harmonic, the **net signed** natural power is `|s_nat,in|²-|s_nat,out|²`, which may be negative. With nonnegative intrinsic/load damping the exact stationary ledger is
```math
P_{nat,net}+P_{ctrl,net}=P_{load}+P_{internal\ loss}.
```
Therefore driver-excited radiation into an otherwise source-free Earth-facing port cannot be misreported as naturally harvested work. The natural incident-wave amplitude **must be independently calibrated**: it is NOT inferred from GEC fair-weather J, 250kV global potential or the reported capacitor 48V reading.

**Selected *normalised* parameters, not Filsinger components:** natural external rate .035, controller external rate .04, intrinsic .02, load .05, modal splitting ±.075, conservative coupling .018, environmental incident amplitude .35, controller amplitude .60. Baseline: natural incident/returned .12250/.08656, hence **net natural +.03594**; controller incident/returned .36000/.10168, hence net controller +.25832; useful load .21018, internal dissipation .08407; residual ~2.8e−17. This demonstrates a possible externally energised receiver **assuming** the externally powered wave. No independent Filsinger source is established.

**Negative controls:** turn off that incoming natural wave with the same drive and load and the natural-port signed net is **−.03703** (outgoing radiation), not a natural generator; useful load drops to .15964. With both sources off, useful load is zero. Branch relative phase remains fixed upon scaling the *sole* common driver, but changes with selected loading and detuning.

**Phase sensitivity:** 72 controller phases against the **hypothetically phase-coherent** independent wave yield net natural work from −.02976 to +.12242 while useful load changes only .20633–.21403. Thus a phase-sensitive change in *signed environmental work* can be large while load power hardly changes. Under **random independent natural phase**, 128 phase samples give controller-phase-independent mean natural work, controller work, load and loss to numerical precision. Do not apply this linear cancellation to unproved nonlinear/active physical systems.

**1,728-case load/detuning/phase optimisation:**

| Maximized objective | Load rate | Split detuning | Controller phase relative to NATURAL wave | Net natural work | Useful load | Circularity |
|---|---:|---:|---:|---:|---:|---:|
| Useful load | .075 | 0 | 157.5° | +.09459 | .30757 | −.528 |
| Net natural real work | .05 | .075 | 262.5° | +.12247 | .21400 | +.718 |
| Absolute circularity | .025 | .025 | 300° | +.10275 | .23740 | +.998 |

All figures are dimensionless model outputs. `1:1.618` geometry is neither required nor an optimum discovered here. The physically constrained optimum depends on real source access, delay, material coefficients and controller costs, all still OPEN. The relative controller/natural phase is an **unknown** for an independent environmental wave, not a knob the original device has demonstrated controlling.

### Formalization and exact scope

`DASHI/Physics/Motors/SmithFilsingerMidpointPhaseWorkExact.agda` imports pre-existing source, reflection, time-index/flight and energy-bound owners; its `MidpointTwoPortWorkWindow` separates incoming and outgoing quanta of both ports. It defines `usefulNoGreaterThanIncidentAndStorage`, the constructive `driverOnlyCanRadiateIntoEnvironment` negative control, `noBoundaryInputNoUsefulLoad`, and `phaseReadoutAloneCannotIdentifyNaturalWork` (a two-world counterexample). `SameOriginalMidpointPhaseAndSourceWorkAdmission` demands same-original pins, incoming/outgoing real work, independent replenishment, actual interaction-region cross-spectrum and nonlinear causal Maxwell response. This admission is **intentionally not constructed**.

**Acceptance:** source-equivalent local Python **17/17 tests PASS**, including signed two-port passivity, known reflection and two-mode donors, source-off controls, phase rescaling, load-dependent phase, observation delay, incoherent averaging, and optimization criteria. The new `scripts/check_smith_filsinger_midpoint_phase_agda29.sh` uses the existing pinned wrapper but no Agda/Nix is installed here; **no kernel pass or GitHub-head replay is claimed**.

**Source authors:** Zhao, Guo and Fan (2019), *Physical Review A* 99 033839 (energy conservation, reciprocity and TCMT assumptions), https://cguo.org/pdf/zhao2019a.pdf; Wu and Lalanne (2024), *Optics Express*, https://doi.org/10.1364/OE.517237 (limits of conventional TCMT); Anisimov et al. (2026) https://doi.org/10.1016/j.asr.2026.01.090 and Tinsley (2022) https://doi.org/10.1029/2021JD035954 (real global-circuit sources/uncertainties, **not** proof of this device).

**OPEN:** S0/P1 physical pins and synchronous readings; S5c–S5g phase/coherence/full causal nonlinear response; S8c/S8d signed replenished natural work and matched work; P2 real Earth/atmospheric source operator; R1/R2/R3 full same-device explanation; D1/D2 pinned Agda and empirical proof weld. The environmental source power calibration from PR #1521 remains independent and prerequisite to any watt-level physical promotion.


## 2026-11-16 complementary DC source/sink matching: no external RF phase coherence needed

**Important correction to the coherent-wave branch above:** the *user's proposed mechanism* needs stable relative timing between the two **controller-generated branches**, not necessarily phase-locking the controller to an independent RF field. An independently maintained **DC or slowly varying** source can have no meaningful radio-frequency phase and yet supply real work through complementary timed receiving branches. This is a different model from two coherent incident waves, and its success does not imply the original source has a measured V_oc or free atmospheric watts.

New source-equivalent consumer `scripts/check_smith_filsinger_midpoint_dc_source_matching.py` and 12-case test module `scripts/test_smith_filsinger_midpoint_dc_source_matching.py` explicitly reuse the fixed positive-R source matching theorem from [#1521](https://github.com/chboishabba/dashi_agda/pull/1521) and `scripts/check_smith_filsinger_shunt_source_port.py` on master, without duplicating the Earth's actual source operator.

Let a physically separate *hypothetical* fixed Thévenin source have `V_oc>0,R_s>0`. Two **nonnegative controlled load conductances** `G_1(t),G_2(t)` are assumed to share its loaded terminal:
```math
G(t)=G_1(t)+G_2(t),\qquad
I(t)=\frac{V_{oc}G(t)}{1+R_sG(t)},\qquad
P_L(t)=\frac{V_{oc}^2G(t)}{(1+R_sG(t))^2}.
```
The source/matching identity holds instantaneously:
```math
P_{\mathrm{src}}=V_{oc}I=P_L+R_sI^2,
\quad
\frac{V_{oc}^2}{4R_s}-P_L
=\frac{V_{oc}^2(R_sG-1)^2}{4R_s(1+R_sG)^2}\ge0.
```
There is **no time-averaged output increase beyond the fixed source's matched maximum**; a scheduled controller can merely avoid periods of poor source matching. A separately assumed nonnegative controller-auxiliary power `P_ctrl` is explicitly dissipated outside the useful load: `P_src+P_ctrl=P_L+P_feedloss+P_ctrl_aux_loss`. The ideal conductances are abstractions, not free/no-loss high-voltage switches.

**Conditional anti-phase construction:** use `V_oc=R_s=1`, `G_1=.5+.35sin(omega t)`, `G_2=.5+.35sin(omega t+phi)`. At `phi=pi` the two branches are complementary and `G_total=1/R_s=1` for all t. The time-averaged useful load reaches the fixed-source maximum **0.2500**; in-phase operation `phi=0` produces useful load **0.229623**, an **8.9%** improvement for the specified source and branch ranges. With illustrative controller cost .01 in both cases, net load after control expenditure is .2400 vs .219623. Both cases obey source and cost accounting to ~1e−16.

**Non-universal phase negative control:** with *the same two conductance waveforms* but source resistance changed to `R_s=3`, the best sampled phase is ~0.638 rad (36.56°), **not 180°**. Thus even for this elementary DC-source arrangement, opposed timing is not a golden-ratio law or a source-independent optimum.

The anti-phase construction does **not** establish that the actual Filsinger opposed-polarity capacitor configuration behaves as two controlled parallel conductances, nor that the earth/plate supplies this hypothetical DC `V_oc`. Capacitor-branch voltage opposition, current-phase opposition, switching phase, measured environmental source voltage and environmental wave coherence are different observables. The actual conversion would additionally require capacitive/inductive state dynamics, switch driver work and losses, material dispersion, retarded coupling and source backaction. The full source power ceiling must be calibrated to [#1521](https://github.com/chboishabba/dashi_agda/pull/1521)'s physically available terminal V/I and GEC current-density constraints. Those **original P2/R2/R3 gates are OPEN**.

**Acceptance:** exact algebraic nonnegative-square identity and sin(t)+sin(t+pi)=0 checked with SymPy; local **12/12 tests PASS**, including source-off, controller-cost, fixed-source power ceiling, instantaneous conservation, nonnegative physical G and source mismatch. Together with the reciprocal coherent-wave submodel, **29/29 local source-equivalent tests PASS**. No pinned Agda 2.9 check and no exact GitHub-head execution claimed. This is a conditional mathematical source-matching advance, not a field measurement, automatic weather-response amplification, or evidence of excess natural power.

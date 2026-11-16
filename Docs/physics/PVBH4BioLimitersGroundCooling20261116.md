# Solar PV + BH4 bioengineering and ground-coupled condensate loop: 2026-11-16

**Owner:** DASHI Physics Photovoltaic cross-pollination, draft PR #1523. **Attribution:** existing BH4 proof discipline and 369 atomic formalism owned by original respective DASHI programmes; full external study authors/DOIs retained. No experimental coefficients or Agda kernel check are claimed. Ground truth must come from same-device receipts and source-authorised rates.

## Corrected goal

(1) In the **bioengineering** lane, transplant the BH4 methodology (species, stoichiometry, unknown rate, exchange, phenotype, source/parameter receipts, intervention and independent held-out observation). Do not assume a photosystem-electrode interface, a light-harvesting efficiency, or a photocurrent measurement constitutes a power-efficiency result.

(2) In the **thermal** lane, preserve the actual user hypothesis: PV cooled to 20–25°C by evaporative/condensate return refrigeration, staged heat upgrade and optional ground-source/sink. Condensate returns through expansion/equilibration to the cold-side evaporator, where the returned working fluid **absorbs additional heat by evaporation**. It does not arrive as an inherently cold fluid when it leaves a warmer condenser. Closed fluid and heat cycles must distinguish water condensed at high temperature, flashing after pressure reduction, ground-loop subcooling and source/sink roles.

(3) Sunlight is the exogenous energy source. Incident solar radiation's available work decreases when degraded to near-ambient panel heat, but this does not negate the value of cooling gains, exported hot water/process heat or subsequent non-PV products. Report `net electric`, `gross PV electric`, `heat at stated temperature`, `fuel chemical energy`, `time-averaged repair resources`, `solar-area capture` separately.

## Real experimental bio-limiting factors

Zhang/Plumeré (2026), *Photosystem-Based Biophotoelectrodes for Solar Energy Conversion*, Chemical Reviews DOI **10.1021/acs.chemrev.6c00021**: unstable isolated photosystems; narrow protein spectral windows; protein electrode orientation and poor wiring; direct electron tunnelling generally sensitive to <~14 Å gap; mediator charge shuttling can help but may induce short-circuit/backreaction, recombination and oxidative degradation; living platform trades longer stability/repair for competing metabolism and complex electron extraction.

Wang/Zhang/Li/Zhu et al. (2026), *Engineered conductive pili enable high-efficiency photosynthetic electron extraction in biophotovoltaics*, Nature Communications DOI **10.1038/s41467-026-72407-7**: measured electrode photocurrent around **0.19 to 0.82 µA/cm²** at **imposed +0.7 V vs Ag/AgCl**, not an unassisted MPP. Changes combine effective wired cell number and interfacial electron transport, approximately two coupled factors of ~2, not a universal 4× intrinsic light-to-energy conversion. Extended runs decline due to biological viability, illumination/gas/mass transfer/carbon source, not solely gold interface stability. Mediator-assisted 3D BPV quoted up to 245 µA/cm² initially, falling rapidly, and ~1.93 µA/cm² when mediator absent: never combine those separate experimental conditions as one sustained operating point.

Whole-cell systematic review, 2024, PMID 38531227, identifies extracellular electron transfer and terminal-oxidase competition as candidate bottlenecks. 2025 Synechocystis pathway-fluidity study DOI 10.1111/tpj.17225 flags uncertainties in direct coupling of photosystem and electrode.

## BH4-style state and transition operator

Each spatial compartment and time window must distinguish at least
`[incident photon bins, absorbed photons, PSII excitation, separated charge, electron transport carriers, ATP/NADPH/redox pools, carbon-fixation products, respiration, oxygen/ROS, biofilm-electrode bound electron states, extracellular redox mediator, exported charge, hydrogen/catalytic products, damaged/repaired photosystems, nutrient and dissolved gas pools]`.

For fixed gross photon uptake `G = phi * absorption` a source-conditional toy steady-state positive-rate model is:

`E = G / (k_sep + k_fluor + k_nonrad)`
`C = k_sep E / (k_transport + k_recomb)`
`R = k_transport C / (k_eet + k_carbon + k_resp + k_fuel + k_ros)`
`X = k_eet R / (k_contact + k_back)`
`J = q k_contact X`, `P_electric = V_MPP J` only when the source supplies a real MPP rather than an imposed potentiostat potential.

The corresponding stoichiometric matrix columns are individual transitions `excitation -> separation/fluorescence/heat`, `separated -> transport/recombination`, `transport -> EET/carbon/respiration/fuel/ROS`, `EET -> contact/backreaction`. Charge balance and energy balance are separately required because finite electron count doesn't prove available electron work. Include photon requirements for each electron, oxygen/water stoichiometry, hydrogen `2e^-/H2`, overpotentials, and heat/exergy.

**Source-independent synthetic rate test**, incoming 1e18 photons/m²/s at 1.88 eV, absorption .7, V_MPP explicitly **assumed** .4 V: predicted current 0.003263 A/m², power 0.001305 W/m², solar-electric fraction 0.00433 of the *synthetic monochromatic input*. Intervention outcomes:

| Hypothetical intervention | Electric-output ratio | Fuel-output ratio |
|---|---:|---:|
| Double extracellular export rate | 1.818 | 0.909 |
| Double electrode contact rate | 1.250 | 1.000 |
| Double intracellular transport | 1.200 | 1.200 |
| Double charge separation rate | 1.158 | 1.158 |
| Halve carbon allocation | 1.364 | 1.364 |
| Double fuel-branch rate | 0.938 | 1.875 |

These ratios are predictions **only of the stipulated synthetic rate competition**. A real engineered organism must measure all rates, biomass/ATP, absorber lifetime, fuel extraction efficiency, photon input, and actual two-electrode V-I power. Do NOT assert that EET is universally the dominant bottleneck: it dominates this selected toy case because of the supplied coefficients.

Intervention list: wavelength/time-resolved fluorescence to constrain excitation quenching; transient absorbance/PSII kinetics for charge separation and recombination; terminal oxidase and CO2 pathway perturbations; chronoamperometry and EIS to constrain EET/contact; in situ redox NADPH/ATP pools; isotope-resolved carbon and fuel products; 2-electrode unbiased electrical MPP; longitudinal viability, nutrients and membrane health. Include matched controls/negative controls. Do not equate electrode bias with useful produced electrical voltage.

## Ground-condensate refrigeration cycle

For a **water-as-working-fluid** conceptual vapour-compression cycle, same-mass enthalpies are:
- cold PV evaporator outlet: `h1`; compressed vapour: `h2`;
- warmer condenser liquid return: `h3`; post-expansion inlet: `h4`;
- `h4=h3` for ideal throttling;
- `Q_evap=m_dot*(h1-h4)`, `W_comp=m_dot*(h2-h1)`, `Q_cond=m_dot*(h2-h3)`;
- therefore `Q_cond=Q_evap+W_comp` if these are the same complete cycle.

This shows exactly where condensate return cools the **cold side**: after expansion and during evaporation. A hot condensate stream returning without pressure reduction/subcooling would instead impose a heat load at the cold end. Distinguish cooling delivered to the PV from a separate ground-loop heat exchanger and from returned heat delivered to the elevated-temperature preheater.

**Ground as heat sink**: `PV -> PV interface -> cooler ground loop`; possible near-passive cooling if ground T below PV T and thermal conductance adequate, with pump/electrical losses and seasonal ground heat buildup tracked.

**Ground as heat source**: ground supplies an additional positive `Q_ground` to a heat pump's evaporator when heating the high-T service load. This is **not** ground cooling the PV, and the source/sink modes must remain separate. A ground loop can switch roles or route by valving, but a port's signed work/heat cannot be counted twice.

**Illustrative performance**: 1000 W/m² solar, STC PV P25=300 W/m², 55°C uncontrolled, −0.4%/°C temperature coefficient -> hot PV=264, cooled PV=300, **gross PV gain 36 W/m²**. Cooled heat load is 700 W/m² if all remaining sunlight is thermalised; revise when reflectance/emission is measured.

Ideal temperature boost cold=25°C, condenser=70°C yields Carnot cooling COP 6.626, `W_min=105.65 W/m²`, `Qcond=805.65 W/m²`. If this compression were needed solely to cool the PV, the net electrical gain would be `36-105.65=-69.65 W/m²`; **this does not establish net loss of a combined PV + useful heat product**.

Ground at hypothetical 20°C, PV 25°C: to pass 700 W/m² across a mean 5 K exchanger ΔT requires `UA>=140 W/(m²·K)` for each m² PV. If pump uses illustrative 12 W/m² and heat transfer can actually be sustained, PV electrical net gain is `36-12=+24 W/m²`. Actual heat-transfer area, ground temperature, time-dependent soil storage and water pressure drop remain OPEN.

Approximate hot condensate 70°C throttled to cold saturation 25°C: flash fraction `x ~ cp*(70-25)/h_fg = 0.0771` (liquid cp=4.18 kJ/kg/K; h_fg≈2440 kJ/kg), so evaporator heat absorbed per kg circulated ≈ `h_fg*(1-x)`. To absorb 700 W would then take ~1.12 kg/hour circulating water, not the ideal 1.03 kg/hour assuming no return sensible heat. This ignores real saturation-pressure enthalpy tables, heat exchanger ΔT, pump mechanics and pressure losses; use steam tables and actual component states for physical acceptance.

## Proof and engineering gates

B0: Correct source/strain/bioreactor identity and quantitative paper evidence, especially whether *biased* / 3-electrode and energy consumption of potentiostat.
B1: Finite photosystem species/stoichiometric bookkeeping, electrons/photons/oxygen/NADPH/hydrogen and outside exchange, separate fuel/charge branches.
B2: Source-matched electron transfer, photosystem turn-over, EET, carbon flux, repair/stability kinetics without substituting missing rates with 0.
B3: Independent photosystem fluorescence/transient absorption/redox/isotope assays and electrode I-V / real maximum-power curves.
B4: Full power/exergy/lifetime optimisation with repeatability and engineering intervention controls.
T1: same-cycle condensate h1–h4 and pressure/throttle/flash with mass and energy.
T2: correctly signed ground *source* vs *sink* and interface thermal conductance.
T3: solar PV temperature-dependent efficiency and aperture/irradiance control.
T4: active compressor/pump/valve energy; thermal-value and useful heat sink receipts.
T5: measured combined plant steady/cyclic net benefit with weather and soil thermal dynamics.

### Sources
- https://www.nature.com/articles/s41467-026-72407-7
- https://doi.org/10.1021/acs.chemrev.6c00021
- https://pubmed.ncbi.nlm.nih.gov/38531227/
- https://doi.org/10.1111/tpj.17225
- https://samrepo.nlr.gov/help/pv_module.html
- https://pages.hmc.edu/spjut/E82/lec/RefrigerationVaporCompressionCycle.pdf

### Acceptance

Source-written Agda modules **not kernel-checked**; external Python tests 14/14 PASS on synthetic fixtures, with local reproducible script; physical B0–B4 and T1–T5 gates remain OPEN. Never promote an illustrative efficiency gain or kinetic stage ranking to a calibrated prediction. All original BH4 Golden surfaces untouched.

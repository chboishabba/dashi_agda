# Data-centre acoustics–thermal heat-reuse SOTA: 2026-10-24 max-cut

**Status:** source-attributed literature audit plus a conservation-verified illustrative site model. NO measured site-specific physical, financial, epidemiological or legal outcome claimed. This is a direct extension of `Docs/roadmaps/DataCentreAcousticExposure20261024.md`.

Owners:
- `DASHI.Environment.DataCentreThermalReuseBalanceExact` (energy-conservation witness, demand-dependence and source distinctions)
- `DASHI.Environment.DataCentreAcousticExposureAttributionExact` (acoustic-EM-provenance and site measurement gates)
- `scripts/datacentre_thermal_reuse_dispatch.py` (hourly synthetic dispatch, COP, exergy and fossil-boiler break-even counterfactual)
- `DASHI.Planning.DataCentreUrbanResourceConflictExact`
- `DASHI.Law.SensibLawWoogarooSwanbankDataCentreDevelopmentPressureExact` (Swanbank planning pressure, NOT a built/operating/certified heat-reuse project)
- `DASHI.Physics.Propulsion.JetEngineIndustrialEnergyBidiExact` (shared industrial system coordinates: electricity, water, thermal waste, useful output; DOES NOT transfer a jet turbine model)
- `DASHI.Environment.LESFluidPhysicsCouplingExact` (possible flow physics owner when real geometry, constitutive and boundary data exist)
- `DASHI.Policy.BerkmanDataCentreObscurationAnalogyExact` (Queensland political claim attribution; not an energy model)

## Source roots: keep author and date, distinguish deployment from projection

| Root | Source grade | Paid finding | Boundary |
|---|---|---|---|
| [European Commission COM(2026)500, 2026-09-21](https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:52026DC0500) | official report, first reporting period | 67 EU data centres reporting some reuse; approx 1.8% total heat reused across reported data | Not a world-wide rate or proof no economically feasible sites |
| [ISO/IEC 30134-6:2021](https://www.iso.org/standard/71717.html) | measurement KPI authority | Energy Reuse Factor: reused energy / all DC energy consumed; reuse-process boundary matters | HP output including extra power may not be called waste heat recovered; cannot equate ERF and PUE |
| [ITU-T L.1328 (2025-09)](https://www.itu.int/epublications/es/publication/itu-t-l-1328-2025-09-specification-for-waste-heat-reuse-in-telecommunication-rooms-and-data-centres/en) | international telecom engineering recommendation | low-grade heat generally around 30–80C, temperature upgrade often necessary | Not a supplier warranty or site heat availability |
| [ASHRAE AI Data Center Energy Framework](https://www.ashrae.org/technical-resources/topics-and-initiatives/ai-data-center/introduction-and-purpose) | engineering guidance | liquid cooling W17, W27, W32, W40, W45, W+ defines facility supply classes | W-class is NOT return heat or process offtake temperature |
| [Hao, Zhou, Tian, Zhang, Zhou, Shen, Wu & Li, Applied Energy 2025](https://doi.org/10.1016/j.apenergy.2025.125489) | peer-reviewed review | relative exergy recovery indicator and heat-recovery technology comparison | No site-specific lifetime cash flows or human-health results |
| [Wang et al., Energy and Buildings 2024](https://doi.org/10.1016/j.enbuild.2024.114327) | ORNL Frontier case-study model | heat-pump configurations and refrigerant comparisons | Not direct proof of quoted COP at user-selected operating point |
| [Vieren, Couvreur, De Paepe & Lecompte, Applied Thermal Engineering 2025](https://doi.org/10.1016/j.applthermaleng.2024.124799) | industrial heating network simulation | heat-pump supply configurations, energy/emissions/economic tradeoffs | 70–80% reported emissions reductions are case-dependent |
| [Cui, Du & Wang, Applied Energy 2025](https://doi.org/10.1016/j.apenergy.2025.126407) | thermal design and Guangzhou scenario | 50C-driven triple-stage LiBr/water chiller, 50kW chilled water, 80.5% case mechanical-load reduction, 78MWh modeled annual savings | A case study, not a validated general 80.5% site energy or noise reduction |
| [Chen et al., J Cleaner Production 2024](https://doi.org/10.1016/j.jclepro.2023.140495) | specific ecological farm case-study | co-use farm/IT waste heat, particular economic model | Farm economics/seasonality are not Queensland defaults |
| [Fortum, 2026-05-06](https://www.fortum.com/media/2026/05/fortum-has-started-heat-production-two-large-data-centre-sites-finland) | official deployment progress | Two heat-pump plants OPERATING; Microsoft DC waste heat not yet being integrated; integration projected from 2027; 40% 2TWh demand is projected full build | Do NOT claim completed 40% recovery or 2026 MS data-centre heat supply |
| [Alfa Laval, Odense case](https://www.alfalaval.com/media/stories/industrial-heat-pumps/waste-heat-from-odense-data-center-to-warm-local-community/) | supplier-reported operational project | water-source ammonia heat pumps and district heat; supplier reports 100,000 MWh/yr network potential | Supplier claim, not independent utility metering; some specification panels list an 80,000MWh/yr heat-pump subsection |
| [Stockholm Exergi via Eurelectric, 2026-06-03](https://www.eurelectric.org/stories/stockholm-exergi-data-parks-shows-the-potential-for-scaling-the-reuse-of-waste-heat-when-it-becomes-a-tradable-product/) | utility/platform case | temperature-indexed heat offtake terms, 30+ centres / 16 providers | Illustrative Sweden revenue not directly transferable to Australia |
| [A2EP Heat Pump Estimator](https://www.a2ep.org.au/heat-pump-estimator) | Australian practitioner screening resource | food/beverage, hotel, aquatic, hospital and building thermoeconomics sizing | Must enter site-specific temperatures, hours, costs and auxiliaries |
| [Australia Government waste heat](https://www.energy.gov.au/business/equipment-guides/waste-heat-recovery) | Australian government engineering guidance | specialist industrial HTHP can upgrade 45C heat to >100C | Does not assert feasible COP from arbitrary inlet, pinch, or refrigerant |
| [Cooper & Nguyen, Fluids 2026](https://doi.org/10.3390/fluids11080201) | academic review of 83 facilities / cooling data | heat-transfer technology, WUE differences and water-consumption boundaries | This is literature synthesis; do not confuse an equivalent evaporative-demand metric with measured WUE |
| [Jing, Zhan, Li, Cai, Xie & Jiang, Energy 2026](https://doi.org/10.1016/j.energy.2026.140076) | design optimization plus bounded Zhangjiakou demonstration | heat grade, exergy, long pipe/storage and reported on-site performance | Modeled 24.4km economics applies to a 100MW case, not to small Australian centres |
| [Sameti, Fan & Li, Energy 2026](https://doi.org/10.1016/j.energy.2026.141727) | city-scale exergy/GIS/MCDM/MILP study | source/sink GIS routing and cost/carbon/exergy co-optimization; study uses Dublin | **SOURCE TYPO** conclusion says recoverable 2.0–2.8 GWh/yr for 2.4 TWh/yr demand but Sec. 4.4 identifies 2.0–2.8 TWh/yr. Preserve exact conflict; only section-level TWh interpretation matches 13–90% supply forecasts, subject to independent validation |
| [Benn Jordan, 2026-02-18](https://www.youtube.com/watch?v=_bP80DEAbuo) and [Andy Masley, 2026-04](https://andymasley.com/writing/contra-benn-jordan-data-center-and/) | original creator experiment and adversarial critique | unresolved source noise, calibration, masking, expectation and effect-size research tasks | Not proven emissions or clinical effect sizes; engineering quieter-on-commissioning requires actual noise measurements |

## First-principles requirements

A facility's IT power largely becomes heat. A warm coolant loop is not a useful-energy claim until supply and return **temperature**, water flow, time alignment and customer demand are known. Thermal power `Q_dot=m_dot * cp * (T_out-T_in)` needs a measured `m_dot` and `DeltaT`; do not infer either from a facility nameplate.

At steady state:
`Q_IT + Q_overhead + W_heatpump = Q_heat_to_offtakers + Q_ambient`
with boundary choices excluding other imported/exported utilities. Every auxiliary pump, condenser fan, hydraulic pressure drop, pipe loss and storage loss must be restored in a real-site model.

Heat pump: `Q_hot=Q_source+W_HP`; `COP_H=Q_hot/W_HP`, ideal maximum `T_hot/(T_hot-T_cold)` (K). Published COP must be an operating map, not a single unqualified constant. For a sink requiring 75C and a 35C source ideal Carnot COP ≈8.70; fixture COP=3.5 is illustrative and not a vendor promise. Thermal pinch/approach means source-return grade must be modeled separately from evaporator temperature. At source 35C, ambient 30C, ideal reversible exergy fraction =1-303.15/308.15 ≈1.62%, showing why raw low-grade heat MW cannot be compared as if electrically equivalent.

Absorption chiller: `Q_reject = Q_drive + Q_cooling`; if COP_thermal=0.35 and 6MW of 50C drive heat is available, *illustratively* 2.1MW chilling and 8.1MW total external rejection result. More outdoor rejection capacity (and associated noise/water) may be necessary even when electric chiller load falls. 50C multistage designs are NOT ordinary 50C single-effect absorption chillers.

Avoid three metric errors: heat-pump hot output includes new compressor electricity; heat recovery alone does not improve PUE if site electricity is unchanged; reuse fraction and carbon savings are not synonymous. Apply ISO ERF boundaries and transparent recovered-heat, output and electric meter quantities. Site heat export always requires demand; spare potential without an offtaker must be rejected or stored.

## Conservation fixture: explicitly hypothetical, not an actual project

10 MW IT, PUE 1.25, site input 12.5 MW. IT heat diverted to direct low-temperature stream 2MW + heat-pump evaporator 6MW + uncaptured IT 2MW. Additional heat-pump electricity 2.4MW supplies 8.4MW higher-temperature useful heat (COP 3.5); total delivered 10.4MW; remaining site heat rejected 4.5MW, including non-IT overhead of 2.5MW. Conservation: `12.5+2.4=10.4+4.5=14.9 MW`.

Zero loss / perfect constant concurrent heat demand for a year: 91.104GWh delivered, of which 70.080GWh came from the DC heat and 21.024GWh from added heat-pump electricity. This is an **upper envelope** for the defined capture and offtake assumptions, not a heat-reuse contract or a real saving.

Hour-matched demand reduction (same source, same COP, different offtake):
- 10-hour weekday-independent daily commercial hot sink 1MW direct and 6MW upgraded: 25.550GWh/yr heat delivered and 6.257GWh/yr HP electric.
- 100 days per year, 8 hours per day, 3MW heat sink: 2.400GWh heat delivered and 0.686GWh extra electric.

Synthetic marginal-carbon crosscheck only: if 10.4MW useful heat displaces 90%-efficient fossil boiler at assumed 0.20tCO2/MWh primary fuel, and heat pump uses 2.4MW new electricity, the threshold marginal grid factor is ~0.963tCO2/MWh. Other auxiliaries, baseline heat supply, alternate electric heat pump counterfactual, distribution losses, real gas and marginal-grid factors and embodied emissions are not included. Never interpret the figure as actual Queensland savings.

## Commercial / industrial offtaker hierarchy (qualified)

1. **Low pinch / direct:** incoming water preheat, pool and aquatic heating, properly separated process wash preheat, specific aquaculture tanks and tempered loops. Healthcare potable hot-water safety requires appropriate legionella/scald controls; never supply a low-grade direct loop as finished hygienic hot water by assumption.
2. **Moderate lift:** laundries, food/beverage CIP preheat, packaged commercial water heating, some process hot water and drying. Demand trace must be obtained.
3. **High temperature:** specialist 80–150C industrial heat pumps, multistage and hybrid boilers. High lift is not automatically favorable—COP, refrigerant and industrial operating window dominate.
4. **Warm-climate internal sink:** 50C-driven multistage absorption/adsorption or desiccant regeneration, selected only if measured temperatures, condensation ambient and net electric savings support it.
5. **Storage/cascade:** short-duration stratified hot-water buffers for hourly demand mismatch; seasonal storage only with actual medium and loss accounting. Source temperature ordering and series preheat matter.
6. **No offtake:** reject heat safely, reserve heat export interface for future potential; claiming theoretical recovery as realized energy is prohibited.

## Max-cut selection — what pays the most independent residuals

**MC1 Measurement + site boundary (Pareto high):** measure actual IT and facility electrical, coolant supply/return temperatures + mass flow + enthalpy, compressor/fan/pump power, outdoor third-octave spectra, background levels, water makeup/evaporation, weather and operations timestamps. Reuse existing acoustic instrument provenance, EM channel separation, physical flow and planning owners. Output one hourly aligned energy/noise table with uncertainty intervals, not fabricated generalized 'noise reduction' percentages.

**MC2 Demand matching:** collect GIS of heat sinks and their *actual* flow/return temperatures, process schedule, peak/base heat needs, alternative heating fuels, contracts and distance/corridor constraints. Prioritize 24/7 industrial process customers over politically appealing but intermittent space heating where physical evidence supports. GIS–graph–MCDM–MILP methods from Sameti et al. are methodological prior art; without parcels and network data this is a planning model, not a Queensland route survey.

**MC3 Thermodynamic stack:** enumerate direct exchanger, HTHP, district low-temp loop, buffer, hot-water duty, absorption chiller, heat rejection options, including source temperature constraints and ambient humidity; run Pareto frontier `{capex, operating electricity, gas displacement, water, noise, carbon, reliability, exergy}` over *feasible* hydraulics, not a single weighted performance score.

**MC4 Explicit before/after acoustics:** measure fan, pump, compressor, generator contributions separately and total acoustic **pressure spectrum at offsite receptor**. Liquid cooling can reduce internal air fans but heat-pump compressors and external dry-cooler fans still sound; engineering mitigation possible but no default sign is proved.

**MC5 Policy/finance:** agreement for heat access, grade guarantee, heat-offtake volume, metering boundary, outage backup, data-centre cooling independence, thermal network ownership, Queensland/Ipswich permitted uses, safety, water rights and right-of-way. Keep reported 2026 Swanbank planning proposal a contextual witness only; no onsite or offsite network inferred.

## Roadmap phase change and remaining proof burden

- P0–P1 **paid to illustrative-model standard**: source attribution, mechanism separation, exact finite balance proof, independently executable counterfactual model; not Agda typechecked yet.
- P2 **partial**: enough SOTA for technology shortlist and credible design physics; raw temperature/COP/demand transfer functions still missing.
- P3 **OPEN highest-value**: one verified site source profile joined to one measured suitable thermal offtaker and actual separation distance.
- P4 **OPEN**: seasonally and hourly optimized process/cooling case with exact electricity, water, acoustic and carbon counterfactual.
- P5 **OPEN**: complete permitting, long-run economics and robust case with shutdown backup and heat-sale contracting.
- P6 **separate**: human health/noise causal study. Financial optimization does not constitute safety or risk proof.

**Claim limitation:** the original @itsgingertheory/MKUltra historical hypothesis receives no new support from industrial heat-recovery feasibility. This new engineering programme can stand independently on established thermodynamics and actual industrial demonstration.

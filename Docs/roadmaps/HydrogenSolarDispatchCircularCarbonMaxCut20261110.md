# Highest-alpha solar hydrocarbon power station cut: steady-state carbon, dispatch and measured pilot

Date 2026-11-10. This is the USER'S clarified proposed application: external solar PV co-located with hydrocarbon-fired power plants, external water converted to H2, flue/atmospheric CO2 captured, additional hydrocarbon synthesised and consumed to reduce fossil extraction. The car demonstration has **externally charged batteries**; it is **not** assumed to carry a CO2 synthesis reactor, and the energy is not secretly alternator-powered.

## Source ownership / attribution firewall

- Existing DASHI physics/SI/BIPM/Atomic369/Prohaska and source-attributed NIST owners retained. Conventional reaction stoichiometry and resource/dispatch analysis are mathematical/engineering prior art.
- User-directed architecture and constraints, ChatGPT-drafted adaptation and script. The physical McLaren/XFuel device cannot be validated by another vendor's pilot.
- Emanuele Moioli, Patrick Senn, Simon Østrup, Christoph Hütter, **Results from the operation of an efficient and flexible large-scale biogas methanation system**, *Energy Advances* 3 (2024), 131–142, DOI **10.1039/D3YA00436H**, https://pubs.rsc.org/en/content/articlehtml/2024/ya/d3ya00436h. **They**, not McLaren/ChatGPT, built/operated the published 240-kW-class SNG plus steam PV-electrolyser/biogas demonstration.
- Pavel Panek, T. S. M. Fernando and Mohsen Talei, **Techno-economic assessment of synthetic natural gas production from green hydrogen and carbon dioxide in the Australian context**, *Journal of CO2 Utilization* (2026), article 103536, DOI **10.1016/j.jcou.2026.103536**. Authors' estimates with zero-cost electricity: 21–32 AUD/GJ of SNG, 7–22 AUD/GJ premium compared with H2; scope includes 5–500 MW plants and varying CO2 sources. **Not site-specific McLaren economics.**
- International Energy Agency **Global Hydrogen Review 2024**, chapter 7, says carbon source and electricity lifecycle emissions matter materially; synthetic methane and kerosene carbon advantages relative to fossil depend on very low-emissions electricity. https://www.iea.org/reports/global-hydrogen-review-2024/ghg-emissions-of-hydrogen-and-its-derivatives

## P0 physical proof: a real pilot exists and the denominator matters

Moioli et al. (2024), Fig. 6/Table 3, give approximately:
- electrolysis electricity **188 kW**;
- existing biogas chemical feedstock **130 kW**;
- other utilities **34 kW**;
- **total input 352 kW**;
- methane product **248 kW** chemical power;
- useful 30-bar steam **19 kW** thermal output;
- paper reports **70%** gas-only and **76%** gas+steam efficiencies, rounded.

Recomputed: 248/352=70.45% and (248+19)/352=75.85%. **Never** compare 248 kW fuel output only against 188 kW electrolyser input: the other feedstock and utilities are essential. This is a valid third-party example of renewable gas and heat integration, but does **not** show a pure PV-to-methane 70% solar-energy conversion, and the biogas already contains chemical fuel. `HydrogenSolarCarbonPublishedPilotExact.agda` records the source and whole-system energy denominator. Deployment uses biogas (biogenic carbon) and does not establish performance on a fossil hydrocarbon power-station flue-gas composition.

## P0 steady output versus fading batch: two fundamentally different carbon models

The previous one-batch no-replenishment model has carbon q^k C in the kth reuse. But a **constant-output power station** consumes C units every period; with recovered+resynthesised fraction q, it requires (1-q) C new input each subsequent period.

- First period: C initial virgin carbon.
- Next N-1 periods: qC recovered + (1-q)C makeup per period.
- Total virgin carbon across N periods: **C[1+(N-1)(1-q)]**.
- Virgin-only baseline carbon: NC.
- Avoided virgin extraction: **(N-1)qC**.
- Continuous steady-state virgin replacement rate: (1-q)C per period.

For q=0.90 and 10 periods of demand C=100: 1000 total carbon-duty units, 190 total virgin input, 810 reused units and **81% cumulative avoided virgin** relative to that period-wise virgin-only reference. This assumes **all fresh carbon makeup is newly extracted fossil carbon**. If makeup originates instead from direct air capture or truly biogenic feed, classify it separately; do NOT call all new carbon fossil extraction. Solar energy and water must still regenerate the qC fraction after each burn. Such repeated use is not equivalent to permanent atmospheric sequestration.

`HydrogenSolarCarbonSteadyStateExact.agda` now has an exact 100-scaled all-period source-balance theorem and a finite cumulative avoided-extraction identity, leaving source-actual operating receipts open.

## P0 solar electricity allocation: direct grid vs storable methane

Thermoneutral electricity-only ideal solar feed per mole CH4: 4×285.830 kJ = 0.317589 kWh.
Resulting methane HHV: 890.350 kJ = 0.247319 kWh.
Assumed methane-to-electric generator η=40%: 0.098928 kWh delivered per mole.
Solar electricity-to-methane-to-generator ideal physical ratio: **31.1496%** before capture, transport, heat, battery or parasitic loads.

At the same time and equally-valued service, **direct-use PV is preferable**: the methane route uses >3.21 kWh solar electricity per kWh of dispatched generator electricity (in the example). However direct solar may be unavailable at the required time, constrained by grid connection, curtailment, network demand, dispatch, equipment compatibility or storage needs. The correct decision compares *the value/time/location of output* and alternative battery/thermal/geologic/hydrogen stores.

In the ideal two-option linear dispatch model, if:
- `a` = value of immediately usable direct solar per input kWh;
- `b` = value of methane-generated electricity per solar kWh after storage and conversion;
then **send PV to synthesis iff b>a**, until carbon, gross-water, synthesis or solar bounds bind. Otherwise send PV directly. Do not convert a financially arbitrary multipler into physical energy.

`HydrogenPowerStationDispatchDecisionExact.agda` formalises the source-paid crossover; `scripts/hydrogen_solar_carbon_optimizer.py` now includes `dispatch_choice`, `steady_state_carbon_inventory` and seven additional source-written regression tests (20 total). The exact updated Python file was not executed here, but 11 independent arithmetic/mass/efficiency sanity checks passed in the local numerical session. These are source-written and numerical results, **not** empirical validation of a chosen plant.

## P1 complementary process optimisation

1. First recycle synthesis water: gross electrolysis uses 4 H2O per methane; synth returns 2 H2O; make-up water is 2 H2O if recovered with acceptable quality. Gross water processing capacity remains 4 H2O.
2. Recover heat only as actually usable at required temperature and transfer rate. The reversible electrical reduction (285.83→237.13 kJ/mol H2) **must include** source-matched ~48.7 kJ/mol imported thermal energy, not free heat. Methanation's nominal 252.97 kJ/mol CH4 gross heat exceeds the 194.8 kJ/mol CH4 reversible electrolysis heat demand *arithmetically* but real enthalpy, temperature, condensation and work/heat streams matter.
3. Prioritise economically and materially available CO2. Flue/biogas, direct air and previously recycled fossil carbon have distinct capture burdens and lifecycle counterfactuals.
4. If direct H2 can be used at equivalent real-engine efficiency and service, methanation does not increase chemical HHV: 4 H2 1143.32 kJ HHV to CH4 890.35 kJ HHV (22.13% lower). The benefit is dispatchable, fungible, storable carbon fuel, not energy multiplication.
5. Net atmosphere/lifecycle impacts require methane leakage, CO2 origin, virgin fossil comparator, PV lifecycle emissions, equipment and startup/storage differences and displaced original fuel, not only a closed atom ledger.

## Residual high-alpha gates, K0 deferred by user

- Site geometry, actual solar electricity yield, inverter, weather, grid constraints, dispatch objective and solar alternative use.
- Original power-station exhaust CO2 composition, carbon capture yield and regeneration chemistry actually producing compatible hydrocarbon.
- Metered continuous hydrogen/oxygen amount, reactor heat/exergy, synthesis product assay, full source electrical/thermal/chemical input and storage.
- Fixed-output carbon makeup source, leaks/purge, actual virgin fossil avoided, complete lifecycle atmospheric carbon effects and cost.
- Battery-car SOC/external charger energy and independent diesel efficiency/NOx/PM results (different application).
- Source-specific transcript and claimed 2026 patent/IP title; independent performance and authorship review.

The mathematical first-law/stoichiometric/conditional dispatch proof sources do not certify commercial performance or an experimentally closed-loop carbon station.

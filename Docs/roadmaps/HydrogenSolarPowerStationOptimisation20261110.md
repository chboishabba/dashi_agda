# Solar power-station hydrocarbon regeneration: ideal optimisation cut

Date: 2026-11-10. User-directed interpretation of the inventor's intended **solar co-location at hydrocarbon power stations** plus separate **externally charged battery hydrogen enrichment in a car**. These are user statements, not verbatim transcript citations. Neither requires closed-loop surplus energy.

## Prior art / scientific source ownership

- Classical balanced water electrolysis, stoichiometric combustion and Sabatier CO2 methanation: original chemistry, not original to inventor, user, DASHI or ChatGPT.
- Existing DASHI `AtomicPeriodicTable369GenerativeExact` proton numbers, `ChemistryFiniteRuleTargets`, `SI` (BIPM SI DOI 10.59161/AUEZ1291), `HydrogenMolecularInventoryExact` and attributed Prohaska standard weights are reused through `HydrogenFuelCycleAtomicIdentityExact`.
- NIST WebBook, attributed experimental standard-state water formation -285.830 ±0.040 kJ/mol and methane HHV 890.35 ±0.30 kJ/mol, recorded in `HydrogenFuelCycleNISTThermochemistryExact`. These are reference data, not absolute exact thermochemistry or measured device performance.
- RSC review, DOI 10.1039/D2MA00185C: at standard 298.15 K, electrolysis reaction enthalpy ≈285.8, Gibbs free-energy demand ≈237.1, externally supplied heat ≈48.7 kJ/mol H2. **The 285.83 kJ/mol HHV is not the universal minimum *electricity*: lower reversible electrical demand requires additional heat.** These are distinct budgets. Link https://doi.org/10.1039/D2MA00185C.
- IEA Advanced Motor Fuels Task 64 report identifies power-to-methane thermochemical and catalytic prior art: https://iea-amf.org/app/webroot/files/file/Annex%20Reports/AMF_Task_64.pdf
- Author attribution for the new generalisation: user directs scope; ChatGPT authored adapters/scripts; original physical and formal authors retain ownership.

## Exact general balanced reaction (integer coefficient representation)

For any nonnegative carbon count `x` and hydrogen-pair count `b`, let a selected hydrocarbon be C_x H_(2b), e.g. CH4 is (x=1,b=2) and an alkane C_x H_(2x+2) is (x,b=x+1).

Two molecules permit integer oxygen coefficients:

```text
Electrolysis:
 (4x+2b) H2O -> (4x+2b) H2 + (2x+b) O2

CO2 hydrogenation (net *stoichiometric target*, not a single-step catalyst):
 2x CO2 + (4x+2b) H2 -> 2 CxH(2b) + 4x H2O

Combined solar-fuel synthesis:
 2x CO2 + 2b H2O -> 2 CxH(2b) + (2x+b) O2

Combustion of regenerated fuel (reverse atom ledger):
 2 CxH(2b) + (2x+b) O2 -> 2x CO2 + 2b H2O
```

Every statement is atom-balanced in C/H/O. The apparent return of both CO2 and water after later combustion does not replace the previously supplied **solar energy** that left as useful work/heat.

Per ONE hydrocarbon molecule, ideal target:
```text
CO2 feed: x mol
H2 needed: (2x+b) mol
Gross water through electrolysis: (2x+b) mol
Water produced in synthesis: 2x mol
Net water make-up with ideal recycle: b mol
O2 coproduct: x+b/2 mol
```

The integer two-molecule version is source-written in `HydrogenSolarCarbonGeneralStoichiometryExact.agda`. The actual chemical route to an arbitrary CxH2b is **not** claimed known or feasible from atom balance alone.

## Optimise the concrete, literature-grounded methane case

One CH4 from captured CO2 uses 4 H2 and nominal thermoneutral electrolysis of 4 H2O, producing 2 O2; 2 H2O return from Sabatier so **net 2 H2O consumed**. Heat is source/sink-dependent.

From 1.000 kg captured CO2, assuming complete selective conversion and compatible feed:
- CH4 produced **0.36454 kg**; gross water feed **1.63739 kg**, synthesis water returned **0.81870 kg**, net water consumed **0.81870 kg**.
- H2 produced for methanation **0.18324 kg**; co-produced O2 **~1.454 kg**.
- Thermoneutral *electricity-only reference* **7.21645 kWh**, methane HHV **5.61975 kWh**, exothermic methanation enthalpy in liquid-water HHV reference **1.59671 kWh**.
- Methane chemical output / nominal thermoneutral electrolysis electricity = **77.87%**; this excludes CO2 capture, compression and water processing. This is NOT a general maximum for all heat-assisted configurations.
- Ideal reversible electricity, when the remaining electrolysis enthalpy is supplied by compatible external/recovered heat: **5.98691 kWh per kg CO2**, with **1.22954 kWh** of heat required for this amount of H2. Heat availability, temperature, transfer and entropy production need separate source-paid receipts.
- At an assumed 40% electricity-generation efficiency, chemical methane would yield **~2.248 kWh** electricity per kg CO2. The thermoneutral solar-electricity→methane→generator conversion is only **~31.15%** absent auxiliary inputs.

Scaling to **1 Mt CO2 per year**, ideal electricity-only thermoneutral process:
- About **7.216 TWh annual PV electricity** and **5.620 TWh annual methane HHV**.
- If, purely illustratively, annual irradiance =1500 kWh/m2/year and net PV efficiency =20%, electrical yield =300 kWh/m2/year. Solar *module aperture area* is at least **~24.05 km2** in this simplified ratio. **Land footprint is larger and this is not site-specific solar availability.**
- Carbon originates either from power station exhaust or DAC. Reusing fossil exhaust carbon changes extraction demand over repeated recirculations, but does not by itself establish atmospheric net-zero or negative emissions. Atmospheric carbon origin and full lifecycle/energy counterfactual need separate testing.

## Max-cut optimum (within the deliberately simple linear methane objective)

The optimiser `scripts/hydrogen_solar_carbon_optimizer.py` sets `n_CH4` to the smallest of three admissible caps:
```text
n <= (available CO2 mol) * capture fraction * conversion fraction
n <= solar electricity kWh / (electrolysis kWh per mol
     + capture allocation kWh per product mol + reactor auxiliaries)
n <= available *gross* water kg / (4 * 0.018015 kg/mol)
```

The cap is optimal **only** for independent proportional resource budgets and fixed technology efficiencies, with a pure objective of maximizing methane moles. It does not optimise economic value, grid dispatch, storage, catalyst temperature, CO2 capture energy, renewable curtailment, competing direct-use PV, or water-recycle plant makeup. For example, water availability here is a *gross feed capacity*; ideal recycling permits reducing fresh net water makeup to 2 water moles per methane.

An optional ideal heat-reuse mode may replace at most 4×48.70 kJ per mole CH4 of the thermoneutral electricity with externally compatible heat. The script never credits more heat than both the reversible heat requirement and a user-admitted fraction of reference-state methanation heat. This is a **hypothetical thermal match**, not a real heat exchanger design.

**Optimisation insight:** if H2 is compatible with the power generator and other constraints are identical, direct use of 4 moles H2 retains 1143.32 kJ HHV, while converting that H2 to 1 CH4 retains 890.35 kJ HHV. Methane sacrifices ~22.13% of the original hydrogen HHV but may improve storage, infrastructure compatibility, transport and carbon reuse. Those benefits should be assessed against direct PV, H2 and storage alternatives, not claimed as free energy.

## Exact evidence gates remaining, excluding K0 per user direction

1. Source-specific solar irradiance, area/dispatch/curtailment, inverter and conversion efficiencies at the actual power station.
2. Power-station exhaust composition/capture route versus DAC energy/heat inputs and real captured CO2 product assay.
3. Actual electrolyser electricity and heat, operating T/P, H2 rate and gas separation; dynamic heat recovery from methanation is temperature/exergy constrained.
4. Actual hydrocarbon product distribution, e-fuel refining/liquefaction/compression, methane leakage and station fuel compatibility.
5. Annual multi-cycle material carbon/water/oxygen inventory, startup storage and precise fossil displacement baseline.
6. Real car battery *offboard charged* kWh and SOC trajectory, diesel load, H2/O2 flow, emissions and net useful output.
7. Independent raw data, causal engine study, lifecycle/cost/counterfactual, original transcript and source-specific IP title. No measurements or direct transcript were fabricated.

**Kernel note:** Agda source-written ≠ Agda typechecked. User asked not to prioritise K0. The Python optimiser source and numerical arithmetic test are independent of an Agda kernel acceptance.

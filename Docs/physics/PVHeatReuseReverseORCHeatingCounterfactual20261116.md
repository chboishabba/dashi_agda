# PV heat co-products, heating displacement and reversible A/C-as-generator (2026-11-16)

**Status:** same-service accounting theorem and source-audited experimental precedents. Existing PR #1523; draft and **Agda kernel unverified**. No actual system has been built or measured. Preserve names and original attribution of published experimental research.

## Primary-source experimental precedents: not hypothetical

1. Dumont, Quoilin and Lemort (2015), DOI https://doi.org/10.1016/j.ijrefrig.2015.03.008, built and tested a reversible heat-pump/Organic Rankine Cycle (HP/ORC) machine intended for a **120 m² solar thermal roof** and ground heat exchanger. Modes: direct solar heating, heat pump for winter heating, ORC generator for surplus summer heat. A modified HVAC scroll compressor acted as an expander/generator when configured for the ORC. Observed HP COP 3.1 at 21 C evaporating / 61 C condensing and ORC 4.2% cycle efficiency at 88 C evaporating / 25 C condensing. Source: https://orbi.uliege.be/handle/2268/182307
2. Ravindran et al. (2024), DOI https://doi.org/10.1016/j.applthermaleng.2024.124237, independently tested an R1233zd(E) reversible HTHP-ORC system using a modified Sanden TRSA09 automotive AC scroll unit, valving/ORC working-fluid pump and alternator. Observed HP mechanical COP max 4.8 for 41 K lift, ORC 512.4 W net and 3.01% overall cycle efficiency at 90 C input; NOT a universal 3% coefficient at arbitrary source temperature.
3. Quoilin, Dumont et al. (2015), DOI https://doi.org/10.1115/1.4031004, analysed reversible solar roof/ORC and heat-pump seasonal dispatch; highlights pump and four-way-valve adaptations, not just reversing a stock motor.
4. Data-centre analogue: a 2026 study in *Energy*, DOI https://doi.org/10.1016/j.energy.2026.140076, reports a weather-calibrated district-heating retrofit employing multiple heat pumps/thermal storage with 69.61% observed heat utilisation and comprehensive COP 3.46 in the reported facility. This is a context-dependent source, not PV or a directly transferable PV COP. Odense, Denmark, heat recovery also reported by industry integrator Ramboll (late 2026): about 45 MW to district heat via heat pumps operating at 70–75 C, with 35 MW of data-centre cooling. https://ramcmswebsiteprod.azurewebsites.net/en-us/insights/decarbonise-for-net-zero/the-emerging-role-of-data-center-heat-reuse

## Distinct physical modes, selected by same-service marginal gain

- **Cooling-only:** use PV heat sink (ground or ambient) for better PV efficiency if extra P_PV exceeds auxiliary energy and other operational costs.
- **Direct heat service:** route source heat to a preheater, space heating, domestic hot water or industrial low-grade process when source temperature exceeds receiving-side temperature plus exchanger approach. Avoided energy = separately measured electricity/fuel of heating system that would supply the *same delivered heat service* at the *same temperature/time*. Do not conflate heater electricity with the solar heat input or treat district heat as electric output.
- **Heat pump upgrade:** source heat Q_c from PV/ground plus compressor work W yields Q_h=Q_c+W. Output heat is useful only with a sink/demand at the delivered grade, storage or a valid heat trade. Gross PV boost and heating displacement must be separately reported. Example solar PV held at 25 C while 50 C water service requires compressor temperature lift; no passive 25->50 C exchange.
- **ORC generation:** only on an independently hot available stream with a colder physical heat sink, a suitably engineered expansion machine and actual net after working-fluid pump, transmission, alternator and condenser. At given Q_h, ideal upper bound is `W<=Q_h*(1-T_c/T_h)`, **temperatures in Kelvin**, with real source/sink approach losses. Do not infer 70 C hot source from an unpowered PV kept at 25 C.
- **Heat-pump-to-ORC roundtrip:** if heat is first pumped from a 25 C pool to 70 C and then converted back to shaft work against exactly the same 25 C pool, a reversible engine cannot recover more work than supplied to the pump in that closed two-reservoir loop. The exception is an *additional independent heat source or sink/exergy input* (e.g., concentrated solar heat, hot data-centre exhaust, independent thermal storage, otherwise unrecovered heat), which must be logged.
- **Heat/fuel/chemical storage:** allocate the source to the storage compartment once, and count future withdrawal as storage depletion rather than new sunlight.

## Numerical discriminator, illustrative only

Source heat=700 W/m², target hot-service 50 C, PV-side 25 C, use source heat as evaporator input. If a hypothetical heat pump has **cooling COP 4**, its electric input is `W=700/4=175 W/m²`; useful hot output `Qh=875 W/m²` (heating COP 5). The hypothetical PV temperature gain versus a 55 C reference is 36 W/m² from 300 W/m² P25 and −0.4%/C coefficient. This gives:
- **No heating demand:** PV increment 36−175 = −139 W/m², before other auxiliaries. Use cheaper ground/passive loop, don't run this upgrade.
- **875 W/m² heating demand otherwise met by electric resistance:** displace 875 W, consume 175 W to upgrade, add 36 W extra PV => +736 W/m² same-service electrical-grid benefit, before auxiliaries and counterfactual changes.
- **Identical heating demand otherwise met by a COP 4 heat pump:** avoided electricity 875/4=218.75 W, new upgrade input 175 W, extra PV 36 W => +79.75 W/m² electrical benefit before auxiliaries. This is a synthetic *comparison*; real alternative COP depends on source conditions and delivery temperature.
- **Alternative hot independent source 70 C, sink 25 C:** at 700 W/m², Carnot ORC power max = 700*45/343.15 = 91.8 W/m²; a **hypothetical** measured 3% conversion would produce 21 W/m². 3% is drawn from a different 90 C experimental point and cannot be claimed feasible at 70 C without independent device data.
- **Waste heat at 25 C, sink 20 C**: reversible max 700*5/298.15=11.74 W/m². The 2015 4.2% ORC result at 88/25 C must NOT be applied at 25/20 C (would exceed Carnot).

The same-service heating counterfactual can drive a carbon/cost comparison: if baseline uses a gas heater, report *fuel energy* avoided and fossil CO2 separately rather than pretending it equals exported electricity. For a baseline COP-electric heating service, avoided kWh electric = useful displaced heat / actual source-qualified reference COP. Heating demand/seasonal mismatch, equipment capital/maintenance and district heat/network distribution temperature are key.

## Agda exact owner

`DASHI/Physics/Photovoltaic/HeatReuseReverseORCExact.agda`:
- separates source solar thermal allocation, direct heat delivered, heat-pump upgrade, hot source ORC, ground reject and stored heat;
- requires first-law equalities for upgraded heat and ORC;
- proves ORC electrical work is bounded above by available hot-stream heat (first law only);
- declares a **separate, unapplied** second-law Carnot cross-product inequality (not manufactured from energy conservation);
- requires a heat-demand matched before/after heating service and separately paid electrical counterfactual; signed savings model admits costs as well as benefits;
- provides illustrative Nat fixtures, not validated real thermophysical values.

**Open gates:** actual source temperature and heat grade, baseline heating metered COP and same-service delivery, heat demand/storage, actual scroll expander efficiency and valving, ground storage/dissipation, HX pinch and pressure loss, net electric work, lifetime economics, local Agda kernel checker and Golden import. All remain OPEN even when synthetic Nat identities reduce by `refl`.

## Source/attribution safeguards

Use exact authors/DOIs; solar *thermal* collector must not be called experimental PV. Reversible HVAC scroll unit must not be called an unmodified plug-and-play stock air conditioner. Original DASHI PV source and BH4 bioengineering owners remain intact. This is an optional thermal consumer of PV generated energy/heat and should later attach to the TOE import graph after local acceptance.

# PV thermal dispatch: activate stages under optimal conditions (2026-11-16)

**Status:** synthetic constrained optima, local Python regression only; associated Agda owner source-written and NOT kernel checked. This is a correction to the earlier all-700-W-to-70-C example, which represented a comparison endpoint, NOT the user's architecture or an optimum.

## Real proposal and correct objective

The user proposes PV operated efficiently (20–25 C is a target, not an immutable setpoint) by an appropriately staged **evaporation -> condensation -> condensate return/expansion -> evaporation** refrigeration cycle, optionally coupled to a lower-temperature ground loop. Recovered heat may flow as preheat, stored heat, useful heat, or later be upgraded through a high-temperature cascade. Stages need not operate simultaneously. No heat is repeatedly counted as newly acquired sunlight.

**Optimisation variables:** PV temperature `Tpv(t)`, heat/flow allocations `q_ground(t)`, `q_air(t)`, `q_passive_2phase(t)`, `q_low_lift(t)`, `q_useful_upgrade(t)`, source/sink mode for ground, compressor and pump states, temperature lifts and available high-grade heat demand. For true hardware add switching startup wear, finite time-dependent state, fluid inventory, phase pressures and thermal capacitance.

At a given instant:

```
P_pv = P_STC*(I/1000)*(1 + gamma*(Tpv - T_STC))
Q_solar_heat = I - P_pv - Q_reflected_or_radiated
Q_requiring_disposal = Q_solar_heat - Q_air_passive
                       + Q_heat_leak_from_ambient
Q_requiring_disposal = Q_ground + Q_two_phase_passive
                       + Q_low_lift_evaporator + Q_hot_upgrade_evaporator
P_aux = P_ground_pump + P_low_lift_compressor
      + P_high_lift_compressor + P_controls + P_other
P_electric_net = P_pv - P_aux
Q_low_condenser = Q_low_lift_evaporator + P_low_lift_compressor
Q_hot_export = Q_hot_upgrade_evaporator + P_high_lift_compressor
```

Heat-recovery co-products must remain visible, **not silently converted to electrical-equivalent output**. If a heat valuation or exergy objective is introduced, report a Pareto frontier over net electricity, useful heat at *specified output temperature*, thermal storage, maintenance/lifetime, and cost instead of pretending they share units.

The correct decision is not `run ground at maximum`: a nonzero fixed pump cost and increasing pumping loss can make fractional ground dispatch optimal. Also `P_pv(Tpv)` is not necessarily maximized at the **net-electric** optimum.

## Conditional thermal gates for the equipment

- Ground cooling is allowed if `Tpv > Tground + required temperature approach` and the measured exchanger and subsurface storage can sustain `q_ground <= min(UA_ground*deltaT, ground_storage_capacity)`. Long-term ground heating matters. In a heat-source mode, the ground supplies heat to the upgrade circuit instead; **do not conflate the signed modes**.
- Passive evaporative/condensing heat pipe is allowed only if the condenser's receiving medium is colder than the source by the specified approach. Working-fluid condensate returns to its cold-side evaporator by wick/gravity, or after a pressure/enthalpy stage in an active vapour-compression loop. These are **different thermodynamic devices** with potentially shared exchangers.
- Powered cooling operates where direct/ground and passive phase-change routes are insufficient and its incremental electrical cost is justified by PV cooling, durability, or measured useful-heat demand. Compressor COP depends on actual evaporating/condensing **absolute temperatures and heat exchanger lifts**, never ambient temperatures alone.
- High-temperature upgrade is routed only to the fraction whose downstream demand, timing and temperature merit it; one does not automatically compress all 700 W/m² of PV heat to 70 C.
- An air-side or hot-side condenser needs a finite `UA_cond*(Tcond - Tsink)` to dispose of `Q_evap + W_comp`; setting zero lift and allowing infinite flow is an unphysical algorithmic bug, explicitly guarded in the present numerical harness.
- Heat exchange with hot ambient air can add rather than remove PV load. Include reversible convection/radiation sign, wet-bulb humidity where appropriate, and avoid assuming an ambient heat sink is always usable.
- Do not force PV to 20–25 C if measured auxiliary cost exceeds electrical/durability value. It remains a possible engineering target, especially with enhanced exchanger capacity or an unusually cool source.

## Local executable discriminator, 16 Nov 2026

The separate user-visible package `pv_stage_dispatch_20261116.zip` contains an executable Python optimizer and full result JSON+CSV. **752 / 752 local synthetic checks passed**, including mass/energy allocation and 121 alternative ground-flow checks per optimised scenario. The run uses a global coarse T and ground-flow search with local refinement; continuous/global optimality is not certified.

**All these values are hypothetical test parameters per 1 m² PV:** solar 1000 W/m², 25 C electric power 300 W, gamma=-0.4%/C, hot ambient 33 C, ground 20 C, `UA_air=15 W/(m² K)`, `UA_ground=120 W/(m² K)`, separate passive two-phase heat exchanger `UA=50 W/(m² K)`, ambient condenser `UA=55 W/(m² K)`, ground heat cap 600 W/m², approaches (ground 2 C, passive heatpipe 5 C, evaporator 3 C, condenser 4 C, minimum active lift 2 C), 45% of Carnot cooling COP, illustrative pump-electricity function `2+10(qground/600)^3 W` when on, plus 2 W active-stage auxiliaries.

**These exchangers/conditions are NOT specified equipment or site measurements.** The passive air and passive heatpipe branches require physically separate receiving exchange surfaces; do not use both over the same physical surface without recalibration.

| Case | Tpv selected | Ground thermal | Passive two-phase thermal | Low-lift compressor thermal | PV net electric | Useful upgraded heat |
|---|---:|---:|---:|---:|---:|---:|
| 33 C air / 20 C ground; electric-only objective | 42.27 C | 368 W | 214 W | 0 W | 275.0 W | none |
| Same, 100 W source heat upgraded to 50 C | 46.47 C | 0 W | 424 W | 0 W | 267.7 W | 104.6 W |
| Same, 100 W source heat upgraded to 70 C | 46.47 C | 0 W | 424 W | 0 W | 253.6 W | 118.6 W |
| 37 C air / 24 C ground; electric-only | 46.35 C | 368 W | 217 W | 0 W | 270.1 W | none |

In these synthetic cases the staged optimizer chooses a **warmer PV operating point** than the 20–25 C target, because its assumed cooling machinery is more expensive to operate at that lower setpoint. This is a **control result**, not an argument that 25 C cannot be achieved.

Fixed **25 C** operating point, same 33 C air:
- Ground 20 C, `UA_ground=120`, cap 600: ground 360 W, active heat pump 460 W, auxiliary ~77.7 W, net PV ~222.3 W.
- Cool ground 15 C, `UA_ground=160`, cap 900: ground 820 W, active heat pump 0 W, auxiliary ~9.56 W, net PV ~290.4 W.
- Ground 20 C, substantially higher `UA_ground=600`, cap 1100: ground 820 W, heat pump 0 W, auxiliary ~6.14 W, net PV ~293.9 W.

For context, the hypothetical 55 C uncooled electrical reference is 264 W. The fixed-25-C examples demonstrate that the same PV target may have positive or negative *net electric* value depending on actual ground/sink and exchanger capability. They are **not** predictions for a real Brisbane ground loop.

## Max-cut / strict gates

T0: site/hour irradiance, ambient wet-/dry-bulb, irradiance spectral temperature coefficient, real PV cell IV vs T, optical/radiative fraction.
T1: thermal source and ground sink temperatures, heatpipe and ground UA, fluid inventory, seasonal long-term ground flux capacity and recovery.
T2: fluid identities and same-cycle enthalpy `h1 h2 h3 h4`, phase pressures, pressure losses, flash vapour and proper condensate return.
T3: measured pump curves, compressor COP vs lift/load, controls, defrost/maintenance/startup, condenser heat exchange `UA_cond`.
T4: source-qualified heat demand, specified use temperatures, heat storage, exergy and avoided cost.
T5: instrumented operation and time-series weather/cycling optimization against the same uncooled PV and simpler passive alternatives.
T6: local Agda 2.9 source checker acceptance of the temperature/flow dispatch owner and regression receipt.

## Native formal owner / provenance

`DASHI/Physics/Photovoltaic/ConditionalStageDispatchExact.agda` (this PR) provides the conditional **same-service minimum auxiliary work** lemma, a passive-sink finite-capacity admission, and a partition into ground, passive, low-lift and high-lift heat paths. It is mathematics on Nat quanta, not an empirical optimiser or an accepted global optimality proof. It does not modify the existing `GroundCondensateActiveCoolingExact.agda` owner.

Scientific lineage:
- [NREL PVWatts](https://samrepo.nlr.gov/help/pvwatts.html): temperature-linked PV maximum-power model.
- [CIBSE TM51, section 4.4](https://s3.amazonaws.com/fonteva-customer-media/00D8E0000008w4FUAQ/TM51%202013%20b.pdf): choose exchanger size and minimum compressor lift.
- [ASHRAE Chapter 35](https://handbook.ashrae.org/handbooks/A23/SI/a23_ch35_si.aspx): hybrid heat rejectors, ground thermal interference and long-term site constraints.
- [US DOE heat-pump vapour compression](https://www.energy.gov/cmei/buildings/articles/hvac-water-heating-and-appliance-rd-magnetocaloric-presentation): condenser, expansion and returning working-fluid physical interpretation.

**No >50% cell or system efficiency claim is established by this optimisation.**

# Hydrogen-assisted combustion and carbon regeneration: maximum-cut ledger

Date: 2026-11-09. Branch: `feat/hydrogen-fuel-cycle-maxcut-20261109`.

## Attribution / authority

- Existing DASHI theorem owners: `DASHI.Analysis.StoichiometricConservation`, `DASHI.Analysis.OpenSystemBalance`, `DASHI.Biology.Cell.MetabolicOpenSystemBalance`, `DASHI.Chemistry.TransitionKernel`, and `DASHI.Analysis.DissipationPathMonotonicity`.
- Standard prior chemistry: water electrolysis; Sabatier methanation; hydrocarbon combustion. This chemistry is **not** credited as Michael McLaren's invention.
- Michael David McLaren and related corporate statements are **claims/sources to investigate**, not authority for the mathematical balances. Patent title/inventorship is not inferred from company names or marketing.
- User provided project direction and the source material. ChatGPT supplied the drafted implementation in this tranche; repository ownership and earlier proof authorship remain with their existing owners.
- Static source writing, exact Agda kernel checking, independent experimental validation, and patent-chain verification remain distinct.

## Formal module ownership

1. `IndustrialReactiveEnergyBalanceExact`: carries the existing reaction-path conservation theorem into an industrial instance without reproving it; offers a bounded open-energy ledger, device-mode separation and evidence-class negative controls.
2. `HydrogenFuelCycleExact`: literal balanced C/H/O equations for water splitting, Sabatier methanation, methane combustion; unique hydrogen stream allocation; conditional matched-output efficiency identity; exact 35%/50% demonstration for a 30% diesel displacement without hydrogen.
3. `CarbonFuelRegenerationExact`: carbon capture/synthesis inventory equalities; 100→80→64→51 illustrative attrition; zero-external-input, zero-storage-change work negative control; stoichiometry ≠ measured yield.

## Critical limitations

- `SameCHO` proves literal element-count identities, not any reaction's kinetics, equilibrium, achievable yield, or observed apparatus.
- `MatchedOutputCombustion` records the equal-output relation; the construction does **not** prove that hydrogen changes real engine efficiency.
- Natural-number models are exact discrete ledgers, not calibrated SI engineering measurements.
- The negative controls distinguish constructors/claims. They do **not** by themselves constitute measured performance.
- The public 2026 grant number and the actual legal assignment chain remain unverified.
- This tranche has **not** been Agda-kernel-checked in the current assistant environment. No claim of verified typechecking is made.

## Highest-alpha unpaid cut

| Gate | Exact next obligation | Owner / dependency |
|---|---|---|
| K0 | Type-check all three files and `DASHI.Chemistry.Everything` with pinned Agda 2.9 + standard library; fix concrete errors only | exact-head Agda |
| K1 | Replace model-only `SameCHO` with a concrete `StoichiometricSystem` instance and left-kernel proof for all reaction columns; connect to the existing generic finite-path certificate | stoichiometry bridge |
| K2 | Pay source-specific water-electrolyser electrical/chemical efficiency in exact SI units and prove H2 production bound | physical instrument/source |
| K3 | Bind measured hydrogen allocation and no-double-counting to actual flow-meter observations | material interface |
| K4 | Prove symbolic equal-output fuel-displacement and energy-break-even equivalence for strictly positive engine efficiency using ordered rationals | math/efficiency |
| K5 | Bind any observed assisted efficiency to replicated calibrated paired engine tests, including oxygen control and NOx | empirical |
| K6 | Bind CO2 capture, reactor conversion, separation and storage work to metered full carbon inventory for each repeated cycle | empirical |
| K7 | Retrieve 2026 patent publication, independent claims, inventor names, and patent assignments; explicitly distinguish Converde, Cycle Energy, Olenox and CleanTec corporate identity | legal provenance |
| K8 | Independent review of source attribution, acquisition chain, data uncertainties and claimed practical improvement | independent verifier |

## Experimental controls

Compare matched engine work or generator electricity at matched load/speed/ambient intake:
A. stock operation; B. retrofit powered with no hydrogen; C. independently metered hydrogen; D. electrolyser-fed H2/O2; E. oxygen-only control where safe/feasible. Measure diesel mass, H2/O2 flows, battery/grid electricity, operating temperatures, exhaust carbon, NOx/particulates, and stored energy before/after. The power-plant carbon route additionally requires identified hydrocarbon product and isotope/material inventory.

Modes stay separate. A low-voltage intake electrolyser does not inherit palladium-heater loads of a different plasma-membrane device.

## Verification commands

```sh
agda -i . -i /path/to/agda-stdlib DASHI/Chemistry/IndustrialReactiveEnergyBalanceExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Chemistry/HydrogenFuelCycleExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Chemistry/CarbonFuelRegenerationExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Chemistry/Everything.agda
```

Check under the project's pinned Nix/Agda 2.9 environment and record commit SHA, import graph, kernel output, and independent validation separately. No postulates, unsolved metas or termination/positivity escapes were intentionally introduced.

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

## 2026-11-09 continuation: new mathematical leaves

New files:
- `DASHI.Chemistry.HydrogenFuelCycleStoichiometricExact`: a **concrete projection to elemental-total state** for all three selected reactions. The signed molecular stoichiometric matrix, feed availability, and kinetic state transition still remain open. `selectedFuelCycleCertificate` consumes the existing DASHI `SC.certifyStoichiometricConservation` theorem. The residual is computed from literal C/H/O input/output counts.
- `DASHI.Chemistry.HydrogenFuelCycleBreakEvenExact`: `energySavingIffDisplacementExceedsElectricity` gives both directions of the energy-input criterion for a supplied fossil displacement identity, using constructive strict-order cancellation, not an assumed efficiency measurement.
- `DASHI.Chemistry.HydrogenElectrolyserEnergyExact`: `hydrogenHHVWithinElectricity` derives an energy bound when a **source-supplied** first-law equality and nonnegative heat/storage residual are provided. It does not supply an experimental input/output record.

These files have been added to `DASHI.Chemistry.Everything`.

### Updated exact cut (status is proof-source, not kernel acceptance)

| Gate | Narrow leaf | Source-written status | Still unpaid |
|---|---|---|---|
| K0 | Exact-head Agda kernel typechecking, including consumer | **OPEN** | Run under pinned project Agda 2.9 and standard library; record full output |
| K1a | `reactionResidual` for three balanced reactions + projected `elementalLeftKernel`, finite path proof | **WRITTEN** | Kernel check |
| K1b | Molecule-resolved inventory, source reaction-column `ν`, and valid nonnegative reaction step `x→x+ν` with feed guards | **OPEN** | Native molecule inventory and guarded transition weld |
| K2a | `hydrogenHHVWithinElectricity`, assuming the metered first-law equality | **WRITTEN** | Kernel check |
| K2b | Calibrated Joule/kWh unit bridge, heating value, water/H2 flow, process conditions and uncertainty intervals | **OPEN** | External measured/source receipt |
| K3 | Actual hydrogen partition and provenance across engine, synthesis, storage, venting | **OPEN** | Metered flow/hold-up, not constructed sample partition |
| K4a | `energySavingIffDisplacementExceedsElectricity` | **WRITTEN** | Kernel check |
| K4b | General rational efficiency relation with positive denominator and additive fuel substitution; derivation of engine-efficiency break-even from matched output | **OPEN** | Ordered-rational constitutive abstraction |
| K5 | Replicated baseline/device/no-H2/H2-only/O2-only matched-output tests | **OPEN** | Experiment |
| K6 | Carbon product identity, flow, carbon isotope/mass inventory, energy, separated heat/work losses | **OPEN** | Experiment |
| K7 | Patent claims + inventor/assignment chain | **OPEN** | Authoritative legal records |
| K8 | Independent scientific, mathematical and provenance review | **OPEN** | Independent verification |

### Precisely what the new theorems do *not* prove

`electrolyserProductionWithinInput` is represented by `hydrogenHHVWithinElectricity`; its source balance is an **input proof obligation**, not discovered evidence.

The atom residual is a zero discrepancy in the atomic projection of standard balanced reaction formulae. It is not an assertion that a particular plasma, palladium, electrolyser, intake or CO2 conversion mechanism implements those formulae.

`energySavingIffDisplacementExceedsElectricity` compares input-energy totals for a prescribed fuel displacement. It does not establish that a hydrogen retrofit causes any efficiency rise. The full physical experiment must hold useful work constant and include changing battery/tank inventory.

Do not conflate "source written", "Agda kernel accepted", "executably simulated", "independently measured", "patent disclosed", or "legal title verified". This separation implements the existing DASHI attribution policy.

### Same-run source/consumer weld

`DASHI.Chemistry.HydrogenCombustionBreakEvenBridgeExact` introduces `SameRunFuelSaving` with explicit field equalities between the fossil-displacement source and the matched-output engine source. `sameRunEnergySavingIff` consumes the canonical net-input theorem through this joined record. Its sample 35%→50% engine-efficiency construction is **only an arithmetic fixture** and must not be interpreted as an XFuel observation.

The complete new import tranche is now six Agda modules plus the roadmap, all reached through `DASHI.Chemistry.Everything`.

### Precise theorem-to-observation boundary

The formalism permits an efficiency improvement as an input; it does not prove one occurs. In particular, the matched-output equation includes the combined combustible energy `diesel + hydrogen + synthetic fuel`. Neither flamespeed assertions nor corporate disclosures discharge `K5`. The next source-specific work is to calibrate engine efficiency and gas/fuel flow at identical load, output and inventory boundary with uncertainties, and to distinguish the three architectures.

The next **unproved mathematical** leaves after this tranche remain: molecular nonnegative-guarded reaction transitions (K1b), explicit SI unit/higher-heating-value transport (K2b), and source-paid ordered-rational engine efficiency algebra (K4b). Kernel acceptance K0 remains unpaid for all new source.

## 2026-11-09 final source tranche: molecular conservation and efficiency fractions

The following subsequent modules supersede the earlier statement that a molecule-resolved reaction model had not been supplied:

- `DASHI.Chemistry.HydrogenMolecularInventoryExact` defines a 5-species water/H2/O2/CO2/CH4 molecule inventory, guarded reaction constructors for water splitting, Sabatier methanation and methane combustion, and `stepConservesCarbon`, `stepConservesHydrogen`, `stepConservesOxygen`. Finite-path preservation is transported by `pathConservesCarbon`, `pathConservesHydrogen`, `pathConservesOxygen`; each algebraic reaction conservation identity is solved with the already-used Agda standard-library `Data.Nat.Solver`.
- `DASHI.Chemistry.HydrogenEfficiencyCrossMultiplyExact` defines positive-denominator efficiency ratios from independent measured-work equalities and derives the exact `matchedOutputCrossMultiplies` identity without floating point. The numerators and denominators remain source obligations, and the theorem does not infer actual efficiency gain.

Thus the **source-written abstract mathematical leaves** K1a, K1b (for the selected finite ideal reactions), K2a, K4a and matched-output rational cross-product K4b are represented. This is **not** an Agda-kernel acceptance declaration. For K1b, kinetics, transport, thermodynamic work and physical reaction feasibility are separately unpaid.

### Final exact maximum cut, without false closure

1. **K0 — kernel**: independently type-check each of the nine new Agda modules, their transitive imports and `DASHI.Chemistry.Everything` under repository-pinned Agda 2.9/Nix. Current execution environment has no Agda compiler. Resolve actual reported errors rather than treating static import checks as typechecking.
2. **K2b — SI/source**: provide source-specific measured water/H2/O2 flow, HHV convention, calibrated electrical supply, storage delta and heat rejection and bind them to an `ElectrolyserFirstLaw` instance. Unit conversion and uncertainty propagation must be verified.
3. **K3 — stream identification**: source-bound each actual H2/O2 flow to a unique combustion/synthesis/storage/vent route; distinguish true consumption from catalyst-like *effect*.
4. **K4c — physical efficiency admission**: supply measured true matched-output efficiency across loads, air/fuel stoichiometry and oxygen-enrichment controls. Algebraic cross-multiplication and saving iff cannot establish `η_assisted > η_baseline`.
5. **K5 — causal identification**: independent randomized/crossover baseline, powered-no-flow, H2-only, O2-only and full-system arms with measured NOx, particulate emissions and uncertainties.
6. **K6 — carbon/reaction identity**: identify reactor, products and yields; demonstrate carbon mass closure and energy/enthalpy/auxiliary losses over cycles (including any plasma or palladium mode *only if physically present*).
7. **K7 — intellectual-property title**: independent patent grant numbers, claim text, inventors, ownership records and corporate assignment transactions.
8. **K8 — independent checks**: signed source, compiler, measurement, legal and review receipts kept disjoint under attribution policy.

The new nine Agda files were fetched back successfully from the PR branch; no explicit `postulate`, `TERMINATING`, `NON_TERMINATING` or `trustMe` in executable declarations was found by static inspection. **No kernel check or independently replicated device experiment was performed.**

## 2026-11-09 SI / Atomic369 integration extension

**Inspected existing owners directly:** `DASHI.Physics.Units.SI`, `DASHI.Physics.Units.SIMetrologyBridge`, `DASHI.Physics.Chemistry.AtomicPeriodicTable369GenerativeExact`, `DASHI.Promotion.ChemistryFiniteRuleTargets`, and `DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact`. The SI source is the BIPM 9th-edition brochure (DOI 10.59161/AUEZ1291); periodic-table proton-number identity is an existing DASHI owner; atomic standard-weight source is Prohaska et al. (DOI 10.1515/pac-2019-0603). The additional bridges do not reassign prior mathematical/scientific authorship.

### New modules and declarations

- `HydrogenFuelCycleSIExact`: `kilowattHourToJoule` gives 1 kWh = 3,600,000 J as an exact integer conventional conversion. `SIHydrogenProcessReceipt` requires all four measurement roles in `SI.Measurement SI.Energy SI.unitScale`, source/version/uncertainty carried by the existing SI type, explicit nonnegative signs, and a first-law balance. `siToElectrolyserFirstLaw` transports it into the existing hydrogen bound; `siHydrogenEnergyBound` reuses that theorem. The receipt has **no actual measurement inhabitant** in this tranche.
- `HydrogenFuelCycleAtomicIdentityExact`: `hIndex`, `cIndex`, `oIndex` are existing Atomic369 `neutralAt` instances, with proton numbers exactly equal to the repository's established finite H/C/O periodic targets. `hMassMilliU`, `cMassMilliU`, `oMassMilliU` refer directly to the already attributed atomistic convention; water, methane and CO2 derived *rounded convention* masses are 18015, 16043 and 44009 milli-u respectively. These are **not exact isotopic masses, empirical molar masses, nor HHV values**.
- `HydrogenFuelCycleAtomicMassConservationExact`: `oneStepConventionMassConserved` and `pathConventionMassConserved` apply the existing guarded molecular C/H/O conservation to any fixed weighted elemental mass functional, using the existing source's standard-atomic-weight constants. The result concerns a source convention along the **ideal, closed five-species reaction network**, not lossless capture, measured mass, or energy.
- All three modules imported into `DASHI.Chemistry.Everything`.

### High-priority outstanding verification and source maximum cut

| Gate | Required payment | Why it stays open |
|---|---|---|
| K0 | Agda kernel check for all 12 new modules, exact-head Chemistry.Everything and imports | No Agda/Nix toolchain in current execution runtime; static file fetch is not typechecking |
| SI-01 | Instrument-calibrated power→energy integration and timing | `SI.Measurement` carries source/version/uncertainty fields but no measured run is supplied |
| SI-02 | Real H2 flow measured as amount/time and converted to HHV chemical energy using attributed thermochemical source with uncertainty | Periodic-table identity/atomic mass is **not** the H2 heating value |
| SI-03 | Tight unit-aware inequality with uncertainty interval propagation, storage delta and auxiliaries | Current proof assumes nonnegative losses and an exact source-provided energy equality |
| AT-01 | Element identity + molecular species resolution for actual reactor products beyond H2O/H2/O2/CO2/CH4 | Existing network is selected ideal chemistry only |
| AT-02 | Actual isotope/atomic weight convention for measured inventories and calibrated gas-flow-to-moles bridge | Existing abridged weights do not prove a gas-flow instrument conversion |
| PH-01 | Real H2/O2 injection rates, generator load/speed and paired efficiency responses, including NOx/particulate uncertainty | Vendor/patent disclosures are not actual measurement certificates |
| PH-02 | Source-selected CO2 capture/reactor conversion/heat/plasma and inventory trajectory, when the corresponding architecture exists | No source-specific apparatus proven |
| IP-01 | 2026 patent grant number, claims, inventor and chain of assignment | Corporate narratives alone do not identify a legally operative claim |
| V-01 | Independent scientific, legal and kernel-verification receipts | The formal code cannot confer those on itself |

### Absolute negative controls

- Dimensional validity does not imply accuracy of measurement or physical process identity.
- `AtomicIndex` identifies proton number, and `ElementEquivalent` does not imply neutron/isotope equivalence.
- The Prohaska rounded standard atomic-weight convention must never be promoted into an exact single-isotope mass or into a fuel enthalpy.
- Reaction balance is neither reaction feasibility nor demonstrated reactor performance.
- Hydrogen may change flame kinetics yet its chemical energy input cannot be erased as a 'catalyst'.
- Source code, independent checker run, empirical reproducibility and patent title remain disjoint provenance receipts.

## 2026-11-09 maximum-cut continuation (user expressly deprioritised K0)

Do not treat K0 as the current work blocker or claim it is complete. The following **five additional conditional modules**, plus one local independent arithmetic script, advance the *non-kernel* cut:

| File / declaration | Completed construction | Required external witness |
|---|---|---|
| `HydrogenFuelCycleIntervalBoundsExact`: `addInterval`, `insideSum`, `robustSavingAtEveryAdmittedReading`, `actualInputReduction` | General interval sum, true-value inclusion and guaranteed strict saving whenever upper assisted fuel + upper electrical input is below lower baseline fuel | Calibrated source uncertainty envelopes, equal engine/generator work and correct run alignment |
| `HydrogenFuelCycleMolarThermochemistryExact`: `MolarHHVSource`, `hydrogenBulkEnergy`, `HydrogenFlowReceipt`, `HydrogenProcessAllocation`, `CarbonSynthesisReceipt` | Typed J/mol→bulk-J for measured mol count, source-demand for HHV, and exact 4 H2 : 1 CH4 allocation with product identity as a separate condition | Primary thermochemistry value, temperature/phase/HHV scope, flow-to-moles calibration, actual chromatographic synthesis yield |
| `HydrogenFuelCycleDeviceEvidenceExact`: `ModeAuxiliaries`, `PairedPerformanceStudy`, `AdmittedStudySavings` | Intake-electrolysis, plasma/membrane, carbon-synthesis auxiliaries have disjoint device-specific constructors; five experimental arms and interval-savings consumer | Independent matched-output and electrical/thermal/chemical inputs, output/emissions readings, controls and reproducibility |
| `HydrogenCarbonOpenCycleExact`: `CarbonPath`, `carbonPathBalance`, `cyclicCarbonMakeupEqualsEmissions` | General ordered multi-step carbon inventory identity including external makeup and vented losses; no indefinite self-recycling claim | Measured recovered/vented/added carbon, products, storage, water/O2, and complete energy/auxiliary balance |
| `HydrogenFuelCycleSourceAuthorityExact` | Specific source metadata for US9809774B2 versus US20150118145A1; grant-unresolved, patent/vendor evidence not promoted to independent measurement; patent-specific title receipt | Authoritative 2026 grant publication and claim text; executed patent-specific assignment documents (Converde/Cycle/Olenox etc.) |
| `scripts/check_hydrogen_fuel_cycle_maxcut.py` | 11 self-contained Python unittest numerical checks committed; no CI or external dependencies | **Execution result not supplied** in this environment; should run locally |

### Externally confirmed patent anchor

Google Patents https://patents.google.com/patent/US9809774B2/en explicitly identifies Olev Trass and Michael David McLaren as inventors of *Method of separating solids using bio-oils*, grants on 2017-11-07, and shows the Converde 2016 assignment at 037501/0239. This is a patent-publication anchor with a registered event, **not** a verified transfer into a later Olenox entity or proof of any claimed 2026 artificial-photosynthesis grant. Search did not positively establish the 2026 grant.

### Updated physical/informational maximum cut (no K0 focus)

1. **SI-01** meter AC/DC power and time; integrate battery/grid/solar plus thermal/chemical inputs and changes in stored energy. Input *energy*, not voltage or installed power, is the invariant.
2. **SI-02** acquire source-specific H2 HHV (J mol^-1) including reference state, calibration and uncertainty; gas flow, pressure, composition and temperature produce admitted molar amounts.
3. **SI-03** assign interval uncertainties conservatively for fossil fuel, electricity and outputs; use `robustSavingAtEveryAdmittedReading` rather than nominal 30% marketing.
4. **AL-01** source-identify all H2 streams and keep direct combustion, 4:1 methane synthesis, storage and losses disjoint.
5. **PH-01** obtain actual paired baseline, powered-no-H2, independent H2, O2 control and full device results; verify equivalent useful output, exhaust NOx and particulate emissions.
6. **PH-02** establish device-specific plasma/heater/thermal/electrolysis and compression duties rather than applying historical patents to unknown hardware.
7. **C-01** demonstrate actual exhaust carbon capture, physical product identity, measured methane/hydrocarbon output, net process heat/storage and cycle losses.
8. **IP-01** obtain the newly claimed 2026 patent number and check claim/assignment chain at the publication level, preserving corporate legal distinctions.
9. **V-01** independent instrument/scientific replication and original proof/verification attribution, separately from this drafted code.

**No empirical observation, thermochemistry constant, patent grant number, instrument uncertainty, or signed independent receipt was fabricated.** Source-level conditional record types and symbolic theorems are meaningful mathematical deliverables but they cannot themselves establish a commercial claim.

### Necessary energy-bound qualification

`hydrogenHHVWithinElectricity` assumes a *selected electricity-only boundary with nonnegative heat/storage residual*. For a high-temperature steam electrolyser or plasma/heat-assisted process, **imported process heat and chemical fuel must appear on the input side**. One must not apply this specialised bound to such a system without those additional energies. Oxygen injection may change combustion kinetics but oxygen is not a fuel. No claimed combustibility-enhancement factor is inferred from patent/marketing text.

## Source-paid reference thermochemistry (not a device measurement)

`HydrogenFuelCycleNISTThermochemistryExact` adds **attributed** literature numbers rather than invented fuel constants:

- NIST water liquid standard enthalpy of formation at 298.15 K: −285.830 ± 0.040 kJ/mol. Under H2(g)+0.5 O2(g)→H2O(l), the reported HHV magnitude is represented by 285830 ± 40 J/mol, with explicit source and phase.
- NIST methane gas combustion: Prosen/Rossini measured −890.35 ± 0.30 kJ/mol, represented by 890350 ± 300 J/mol under the specified combustion/product-water convention.
- `fourHydrogenVersusMethaneHHVDifference` proves, as an exact identity of these **reported numerals**, 4×285830 = 890350+252970 J/mol of CH4 production; `conservativeHHVGap` uses 4×285790 = 890650+252510. This is **not a measured Sabatier synthesis thermal yield or plant efficiency**.
- NIST literature records and numerical uncertainty are independently attributed; the Agda equation is a user-directed ChatGPT integration. Neither is McLaren's original scientific contribution.

Primary locators:
https://webbook.nist.gov/cgi/cbook.cgi?ID=C7732185&Mask=187&Units=SI
https://webbook.nist.gov/cgi/cbook.cgi?ID=C74828&Mask=1

**SI-02 status:** reference-state H2 and methane HHVs sourced; device-specific H2 molar flow, gas composition and calorimetry still external. Source uncertainty is not a claim that reactor-level uncertainty is ±0.040 kJ/mol. The measurement-dependent gates SI-01, SI-03 field acquisition, AL-01, PH-01, PH-02, C-01, IP-01 and V-01 remain open. The interval theorem is conditional on actual admitted readings.

**Total source tranche:** 18 new Agda modules plus an independent no-CI Python regression source file, 2026-11-09. K0 not prioritised in this iteration per user instruction; its actual kernel status is unchanged.

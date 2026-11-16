# PV-primary 369 conversion programme — 16 November 2026

**Research objective:** maximise measured solar electrical conversion (>50% target) while accounting separately for chemical/fuel, captured excitation, useful heat, and external drive inputs. This is a draft. It makes NO claim of Agda kernel acceptance, real 50% cell efficiency, calibrated oscillator strengths, material Hamiltonian or driven solar improvement.

**Explicit correction:** previous PR #1523 over-indexed heat. Existing heat, ground, condensate return, heating displacement and reversible scroll ORC studies are retained ONLY as referenced auxiliary models. Physical PV conversion is the main graph.

## Reuse-first source graph

1. Atomic 369 and finite C3: DASHI/Physics/Chemistry/AtomicPeriodicTable369C3FourierSpatialRestrictionExact.agda and AtomicPeriodicTable369ManyBodyHamiltonianTerminalMaxCutExact.agda; restricted p² Coulomb interaction has already been executed. Remaining: actual periodic crystal / quantum-dot Hamiltonian on the same atomic carrier, real optical dipole operator, oscillator strengths, optical transition energies, correlation and spectra. Reuse AtomicPeriodicTable369SymmetryProjectionCompilerExact.agda. Do not insert arbitrary nine solar wavelength bins.
2. Diamond: DASHI/Mathematics/Symmetry/DiamondNearestNeighbourBlochExact.agda, existing NV spin source owners, and a same-device defect-state photoelectric + unbiased photovoltaic JV receipt. Test mechanisms before rejecting on economic or pure-diamond bandgap grounds.
3. Semiconductor carrier transport: DASHI/Physics/Semiconductor/Device/DriftDiffusionContinuityExact.agda, real absorption, exciton separation, recombination, contact and actual maximum-power point; an optical shift alone is not conversion.
4. Strong driving / nonlinear source: exact C3 optical square plus SmithFilsingerTimeIndexedTransferExact and signed port ledgers. Need a time-dependent same-material Hamiltonian, propagation/field history, measured EQE/IV and signed RF work. Fixed-memoryless J(V) arguments do not automatically apply to a different periodically driven physical device.
5. Multiple excitons: separate absorbed-photon count, created pairs, recombined/carrier-trapped fractions and exported power. EQE >100% is a carrier-count fact, not a >100% energy-efficiency fact.
6. Biological conversion: BH4 original finite stoichiometric/rate/provenance methodology to photosystems, membrane EET, carbon fixation, hydrogen/chemical catalysts, respiration, repair and fuel output, with original experimental parameter receipts. Distinguish imposed-potentiostat photocurrent from autonomous power generation.
7. Thin-film spectrally selective optical routing, photon recycling, 2T vs 4T, CPV A versus scalable thin-film B. Compare actual aperture, angular and wavelength losses, spectral/current matching and manufacturability.
8. Thermal auxiliary: GroundCondensateActiveCoolingExact, ConditionalStageDispatchExact and HeatReuseReverseORCExact are source-written conditional devices; references in Docs/physics/PVHeatReuseReverseORCHeatingCounterfactual20261116.md and PVConditionalThermalStageOptimum20261116.md. They affect PV temperature, auxiliary draw and separately valuable heat but do NOT replace the light-to-charge physical chain.

## Validated external source references

- Official independently verified baselines: Green et al., Solar Cell Efficiency Tables Version 68, Joule 2026, DOI https://doi.org/10.1016/j.joule.2026.102494 : 35.2% certified 1 cm² perovskite/Si tandem; national lab research efficiency chart https://www.nlr.gov/pv/cell-efficiency identifies 47.6% 4-junction concentrator category. Company announcements must retain their distinct non-certified provenance.
- ASTM G173 terrestrial solar wavelength reference, global tilted and direct normal distinct: https://www.nlr.gov/grid/solar-resource/spectra-am1.5 . Earlier diluted 5778 K blackbody numerical upper-bound model is not the AM1.5G spectrum.
- Measured GaAs bias-dependent Franz-Keldysh EQE: 2020, DOI https://doi.org/10.1002/pip.3270 ; absorptance changes sign in parts of the spectrum; no established net RF-enhanced PV efficiency in that experiment.
- THz-driven CdSe/CdS quantum-dot optical-gap shift >0.5 eV: Pein et al. 2017, DOI https://doi.org/10.1021/acs.nanolett.7b01837 ; driven optical shift, NOT photovoltaic electric gain.
- >1 collected carrier per photon in part of visible spectrum: Congreve et al., Science 2013, DOI https://doi.org/10.1126/science.1232994 ; 109 +/-1% EQE at 670 nm in singlet-fission organic solar cell, NOT energy output > light input.
- Quantum-dot PV review as of 2024: DOI https://doi.org/10.1021/acsenergylett.3c01983 ; perovskite QD standalone cell certified 18.1% stated as-of-publication, not current 2026 benchmark.
- Scalable ambient-processed perovskite / Si tandems, Nature Sustainability 2026, DOI https://doi.org/10.1038/s41893-026-01916-6 ; certified 33.0% for its named manufacturing approach.
- Diamond NV photoelectric readout, Bourgeois et al. Nature Communications 2015, DOI https://doi.org/10.1038/ncomms9577 ; no independent zero-bias PV output established by spin readout alone.
- Engineered cyanobacterial electron transfer, Nature Communications 2026, DOI https://doi.org/10.1038/s41467-026-72407-7 ; externally biased photocurrent measurement remains separate from PV Pmax.
- Photosystem electrode bioengineering review, Chemical Reviews 2026, DOI https://doi.org/10.1021/acs.chemrev.6c00021 ; original source for lifetime/orientation/wiring competing pathways.
- Thermal appendix sources: Dumont et al., 2015 DOI https://doi.org/10.1016/j.ijrefrig.2015.03.008 (solar thermal/ground HP-ORC), Ravindran et al., 2024 DOI https://doi.org/10.1016/j.applthermaleng.2024.124237 (adapted automotive HVAC scroll expander, not ordinary plug-and-play air conditioner).

## New numerical falsifiers

The 31-check standalone script scripts/check_pv_c3_optical_discriminator.py evaluates a true 3-state C3 cycle/DFT, three dipole-charge allowed/forbidden patterns, and a synthetic three-site Hermitian field perturbation. At a selected hopping t=-0.25 eV the finite orbital gap is 0.75 eV (NOT semiconductor bandgap). Optical dipole zero is a symmetry-compatible NO-ABSORPTION counterexample; zero hopping has zero gap. The synthetic field rotates oscillator strength and transition energies; broad blackbody photon-weighted response can DECREASE under the selected perturbation, while one narrow incident band improves and another deteriorates. No actual material, contacts, RF energy or photovoltaic conversion is inferred.

## New physical admission and TOE roots

DASHI/Physics/Photovoltaic/PVPrimaryConversionMaxCutExact.agda: conditional signed solar/RF/stored energy ledger and first-law electrical upper bound; separate photon/electron count and collected-carrier bound; same-aperture same-light matched driven net gain criterion, without false positive physical witness.

DASHI/Unified/PVPrimaryTOESpliceExact.agda imports atomic, diamond, transport, bio and PV converters, with heat imports explicitly supporting only. Draft root imports appended to DASHI/EverythingTOESymmetryResolved369.agda, DASHI/Unifier.agda and DASHI/Unified/Everything.agda. Original owners and ESD surfaces untouched.

## Remaining max-cut priority order

P0: ASTM G173-calibrated optical and radiative multijunction baseline (A concentrated and B scalable, independent vs series current constraints).
P1: actual 369 orbital and C3 many-body material/quantum-dot/diamond Hamiltonian + real dipole/oscillator strength and symmetry-broken control.
P2: measured absorption -> carrier/separation/recombination -> real electrode MPP, signed power.
P3: nonlinear voltage/Floquet/Franz-Keldysh response with propagation, RF driver and recovery, matched controls.
P4: carrier multiplication versus Auger/thermalisation/extraction at useful terminal voltage.
P5: thin-film optics, angular spectrum, polarisation and independent electrical channels.
P6: BH4-led photosystem bioengineering: original rate/species/flux to EET, fuel, catalysis and repairs.
P7: independent >50% demonstration with material, standard source, aperture, auxiliaries, product energy, stability and replication.
T: pre-existing thermal conditional stage dispatch and useful heat service, **secondary**.

**Acceptance:** Local 31/31 finite numerical optical tests PASS. All new Agda source, root imports and physical gates are unverified by Agda compiler in this environment. Nothing here proves solar >50% and no empirical optical absorption improvement has been established.

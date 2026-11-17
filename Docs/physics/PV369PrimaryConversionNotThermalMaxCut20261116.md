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


## Progress update — 17 November 2026: P1 Bir-Pikus [111] maximum cut

**Do not erase P0/P2–P7:** the programme remains PV-first with separate carrier multiplication, optical routing, active Stark/Floquet, BH4 photosystem engineering and only secondary heat recovery.

| P1 dependency | Latest completion status | Exact owner / fail-closed residue |
|---|---|---|
| P1a. Original p-shell ternary/charge-vs-spatial C3 | **Existing source owner already present**; representation-level | AtomicPeriodicTable369MagneticC3PhysicalRealizationExact; Atomic369GaAs111TrigonalCharacterExact |
| P1b. Cartesian [111] orbital Bir-Pikus axial matrix, E/A1 split, [001] negative control | **94 local finite/numerical checks** plus new Agda source-written entry-covariance proof | GaAs111BirPikusC3vFiniteExact; scripts/check_gaas_111_kane_birpikus_maxcut.py |
| P1c. Six spinful valence states with L·S, Kramers, C3v spin rotation, valence dipole polarization | **94 numerical + 37 independent exact symbolic local tests PASS**; closed-form three doublet energies and source-conditional polarization weights; total oscillator strength conserved | scripts/check_gaas_111_kane_birpikus_maxcut.py; scripts/check_gaas_111_birpikus_closed_form.py; full Bahder/atomistic source fitting OPEN |
| P1d. Actual 8-band strained GaAs device with measured spectral response | **OPEN** — present model omits valence LK dispersion, strain×k, strain relaxation, confinement and absorption strength vs energy | Bahder 1990 DOI 10.1103/PhysRevB.41.11992; Vurgaftman 2001 DOI 10.1063/1.1368156 |
| P1e. Real 369-derived advantage over unrelated C3v engineering | **OPEN** — same-character decomposition alone is generic group theory | unchanged original ternary→Bloch same-material gate |
| P2. Actual terminal PV gain | **OPEN** — transition weights cannot be identified with EQE or power without measurement | matched AM1.5G reflectance, thickness, transport, recombination, JV MPP |
| P3–P6. Driven quantum, multiplication, photonic and bioengineering branches | **OPEN / retained** — do NOT let strain/HV modelling absorb their scope | original owners/source and BH4-specific rate provenance |
| T. Thermal stage dispatch and heat co-products | **Previously documented; secondary** | existing conditional stage/ORC files |

**Numerical correction:** for the prescribed +0.5% [111] axial strain (transverse strain=0), the model gives 1.378, 1.405 and 1.734 eV interband edge transitions with transverse Kane strengths (Ep-normalized) 1.000, 0.391, 0.609 per two-spin multiplet. These do **not** establish added usable solar energy; full spectral strength is conserved. The fourfold zero-strain Γ8 degeneracy must be counted with a combined projector; pairing arbitrary eigenvectors gives spurious polarization anisotropy.

**Research max-cut next:** (1) same material measured strain/polarization/linewidth data, (2) source-consistent spinful finite-k Kane–Bir–Pikus including missing Bahder terms and geometry, (3) spectral absorptance and actual two-terminal power vs same irradiance and [001]/unstrained controls, (4) compare actual 369 prediction to a conventional no-369 model. Avoid advancing synthetic spectral outputs to device claims. Formal Agda Golden checker still unavailable; import graph alone is not acceptance.

See Docs/physics/PVGaAs111SALCKaneMassCorrection20261117.md for equations, source conventions and the 94-check result.

**17 Nov final P1 formal result:** `det(λI6-Hv)=(λ-(A-u))²[(λ-c)²-r²]²`, `c=A+u/2-Δ/2`, `r²=(3u/2+Δ/6)²+2Δ²/9`; analytic polarized weights `w±=(1±(3u/2+Δ/6)/r)/2`. These exact symbolic equations were independently tested against the full six-state numeric eigenvectors for six signed [111] strain values. The source-to-real-material and 369-to-specific-predictive-advantage walls remain open.


## 17 November P1d/P2 source-conditioned coherent [111] calibration update

**P1d finite film:** PASS **in model**, not experimental calibration. From nominal GaAs C11=118.8, C12=53.8, C44=59.4 GPa and zero normal traction on a coherent planar (111) layer, exact \`eps_out/eps_in=-269/580=-0.463793...\`; imported into \`GaAs111PseudomorphicElasticExact.agda\` with a checked cross-product identity. Source constructor and solver \`scripts/check_pv_111_pseudomorphic_kane.py\` (local independent equivalent: **72 local regression assertions pass**). This ratio **must not be applied as the actual internal strain field of finite, partially relaxed InGaAs/AlGaAs/GaAs-on-InP quantum dots** without growth/strain measurements.

**P1d finite-k:** The source's *six-band* gamma=(6.98,2.06,2.93) cannot be bolted onto the 8-band Kane conduction–valence block without subtracting \`Ep/(3Eg)\` from gamma1 and \`Ep/(6Eg)\` from gamma2 and gamma3 (specified near-Γ convention). With Eg(300 K)=1.422 eV and Ep=28.8 eV, the model 8-band gamma'=(0.228945,-1.315527,-0.445527). Explicit eigenspectrum reproduces the original six-band HH/LH curvatures along [001] and [111]. HH normal inverse-mass formulas give mass 0.350m0 along [001] and 0.893m0 along [111], **not a PV gain**. It remains a k² near-Γ truncation, **not complete Bahder**: conduction shear a',b', strain-induced SO terms, k×strain mixing with original source coefficients, electrostatic confinement and full nonuniform layer/defect geometry remain open. Bahder 1990 has a **1992 erratum** and both must be consulted: DOI 10.1103/PhysRevB.41.11992 and DOI 10.1103/PhysRevB.46.9913.

**P1d piezo:** For +0.5% in-plane (111) coherent film, eps_out=-0.2319%, the stipulated linear GaAs e14=-0.16 C/m² gives P111=+0.001352 C/m². Unscreeened infinite-interface assumption gives E111≈−11.84 MV/m (epsr=12.9). This is an *optional electrostatic boundary condition*, NOT a free PV voltage. Screening/nonlinear piezo/second-order strain and measured potential profile remain open.

**P2 model-only:** Reused actual 2002-row ASTM G173-03 irradiance plus the original source-projector 8-band near-Γ GaAs transitions, and computed a **radiative-diode JV with absorptance in both Jsc and J0**. Script \`scripts/check_pv_111_g173_radiative_jv.py\` runs with \`--spectrum <external four-column ASTM file>\`; original G173 source not vendored. Because alpha(E)=alpha0 Σ(wj sqrt(E-Ej)) has a *free* amplitude \`alpha0\` and neither angular optical escape nor collection/recombination is measured, these are **hypothetical model sensitivity** only. With alpha0=4e6 m^-1 eV^-1/2 and 2 micron lossless cell: 31.4037% radiative-only unstrained ideal versus 31.4523% +0.5% pseudomorphic (111), gross +0.4867 W/m². A **0.15097% collection loss** removes that entire advantage. This is a control **against** promoting optical redistribution as net electrical performance, not a published or achieved GaAs PCE.

**P1d experiment matching:** Hayakawa (111) GaAs/AlGaAs QW optical enhancement is a positive qualitative donor (DOI 10.1103/PhysRevLett.60.349). Karlsson 2010 (DOI 10.1103/PhysRevB.81.161307) and Sallen 2011 (DOI 10.1103/PhysRevLett.107.166604) measure **exciton fine structure/field-induced mixing**, not the same quantity as our single-particle Γ-state splittings. Yerino 2014 (DOI 10.1063/1.4904944) median exciton FSS=7.6 micro-eV for GaAs/InP(111)A dots, and likewise cannot be fitted as a tens-meV coherent-film band-edge gap.

**Source-convention blocker:** The inherited \`a_v,eff=-1.16\` eV can be used only with a documented valence-energy reference consistent with \`a_c=-7.17\` eV. Standard source tables also quote \`a_v=+1.16\` eV and \`a_g=a_c-a_v=-8.33\` eV; mixing sign definitions produces \`-6.01\` eV instead. **Before actual calibration**, reconcile these with source formulas, temperature and measured hydrostatic gaps, and repeat the P2 sensitivity study. Only then attempt quantitative spectroscopy fit and actual photovoltaic comparisons.

**TOE reuse:** \`DASHI/Unified/PVPrimaryTOESpliceExact.agda\` now imports \`GaAs111PseudomorphicElasticExact.agda\` and \`GaAs111OpticalDeviceSourceWeldExact.agda\`. The latter consumes original \`DriftDiffusionContinuityExact\`, \`SolarOpticalSiteFibreCrossPollinationExact\`, \`PVPrimaryConversionMaxCutExact\` and primary atomic/[111] owners. Its physical witnesses remain **UNINHABITED**, and Agda Golden typecheck remains OPEN. No ESD surface was edited.

**Remaining max-cut order:** (1) source/temperature-consistent bulk and layer parameters + complete Bahder terms with erratum; (2) measured actual strain and sample-constrained PL/PLE/absorptance across identical sample/conditions; (3) actual EQE, collection, dark IV and measured Pmax against unstrained/[001] and no-369 controls; (4) project measured physical device onto a proven **nontrivial 369-specific** mechanism; (5) only then pursue >50% aperture-net certification or integration into multi-junction architecture. Retain independent P3–P6 nonlinear, multiplication, optical routing and BH4 biology branches; heat remains secondary.

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


## 17 November external calibration and corrected-Bahder maximum cut

**Reuse-first physical result, not another abstract C3 claim:**
- Source experimental benchmark **Molenkamp et al., Phys. Rev. B 38, 4314(R) (1988), DOI 10.1103/PhysRevB.38.4314**: orientation-resolved high-resolution GaAs/(Al,Ga)As QW excitation spectra imply [001] HH 0.34m0, [001] LH 0.094m0, [111] HH 0.70m0. Original six-band gamma=(6.98,2.06,2.93) computes exact simple curvatures 50/143=0.34965, 10/111=0.09009, 25/28=0.89286; **[111] mismatch +27.55%**. This is NOT a comparison of identical same-physical-model quantities: empirical masses were extracted with a QW 8-band fit, while current simple values are bulk Γ curvatures. No QW spectrum regression yet. Source-audit module `GaAs111MeasuredMassAdversarialExact.agda`; local 27/27 exact tests in `scripts/check_gaas_1988_mass_and_bahder_erratum.py`.
- **Bahder's 1992 primary erratum inspected as one-page PDF** [Phys. Rev. B 46, 9913](https://doi.org/10.1103/PhysRevB.46.9913). It corrects the spin–orbit strain N1/N2/N3 matrices (Eqs 33–35), valence deformation-potential a sign (Eq30), the R valence mixing term (Eq16), and hbar squared powers in P,Q,R,S (Eq42). Its corrected SO matrices and independent formula controls are now transcribed in `scripts/check_bahder_1992_corrected_spin_strain_blocks.py` (36 local symbolic and numeric tests pass). **Full common-basis eight-band assembly, all four P/Q/R/S units and original 1990 source terms still OPEN.** Typed ledger `GaAsBahder1992ErratumGateExact.agda` prevents claiming completed Bahder.
- At illustrative +0.5% pseudomorphic coherent [111] in-plane strain, the omitted corrected SO strain operator has spectral norm **1.2816 meV**, not identically zero. Its full Γ8⊕Γ7 matrix is traceless and Hermitian. By Weyl, a *same-basis* additive Hermitian correction can shift each eigenvalue by at most its norm, but this is **not** a PV error bound without coupling/matching states and source-driven transport.
- `scripts/check_pv_111_g173_radiative_jv.py` now includes a **fixed-oscillator-weight, common-optical-edge perturbation**: ±1.2816 meV shifts its hypothetical 2 micron strained Pmax by about +0.116/−0.117 W/m² (roughly 24% of the original +0.487 W/m² gross advantage); deliberately mixing valence hydrostatic sign by ±17.82 meV moves it +1.618/−1.899 W/m². These are **sensitivity controls**, not experimental uncertainties, not a claim that eigenvector mixing has been solved.
- **369-specific no-free-gain:** `Atomic369BasisTransportNoFreeGainExact.agda` proves generic exact transported readouts and endomorphisms invariant under a finite label isomorphism; original charge transport and spatial character remain distinct. Reuse the existing CoTaSe₂ same-Wannier-basis covariance authority. Independent `scripts/check_gaas_369_same_basis_no_free_gain.py` 35 local tests pass: unitary conjugation of H, D, rho and charge readout cannot change actual same-system transition strengths/current expectations; a genuine source-powered material perturbation is a different operation. **No nontrivial physical 369 advantage has been established**.

**Updated strict priority:** (1) inspect the original Bahder 1990 full operator (PDF is APS-authorized in this environment) and integrate corrected SO strain in consistent Γ-basis with conduction a'/b', k×strain, source k² and Planck factors; (2) acquire the full Molenkamp sample-specific QW spectra, actual well widths/barriers, orientation/temperature and reproduce the measured 0.70m0 inference, with full QW confinement and exciton physics; (3) same-sample measured absorptance/EQE and terminal MPP; (4) an actual operator/geometry prediction unique to the claimed 369 construction rather than generic Td↓C3v, tested against conventional controls; (5) integrate into any >50% certified multijunction target only with correctly normalised standard solar source and losses. P3 driven RF, P4 multiplication, P5 optical films, P6 BH4 photosystems remain separate OPEN routes; thermal remains secondary.

Full source citations, exact arithmetic and nonpromotion boundaries: `Docs/physics/PV369GaAsBahder1992MolenkampMaxCut20261117.md`.

**Verification:** 27+35+36=**98 local tests** were run on source-independent equivalent scripts (not the full Agda proof kernel); source scripts committed to PR #1523 and source-checked, **Agda native acceptance OPEN**. Prior 131 local numeric/symbolic checks remain separate. This is not an empirical calibration fit or a >50% PCE theorem.


## 17 November P1d quantum-well confinement and P7 strict net-electric >50% closure

**Project goals (unchanged):** >50% **net measured solar-to-electric** aperture-normalized power, with any extra chemical, excitation or thermal product separately conserved and counted. Original 369/triadic input must deliver a *nontrivial, testable physical material/operator prediction* beyond a generic C3v relabeling. Maintain quantum-dot / full 8-band material optics (P1), actual EQE→loaded JV (P2), driven nonlinear/RF with signed power (P3), fission/multipair (P4), photonic thin films (P5), BH4-derived photosystem/redox/fuel engineering (P6). Thermal/ORC/ground remains AUXILIARY. ESD surfaces untouched. Reuse original physical constructors; source attribution preserved.

**New finite QW physical discriminator:** Source [Molenkamp et al., PRB 38 4314(R) 1988](https://doi.org/10.1103/PhysRevB.38.4314) infers *QW* [111] HH mass 0.70m0 by orientation-resolved PLE and 8-band confinement fitting. The nominal **bulk Γ** Luttinger gamma1=6.98, gamma3=2.93 instead gives m_HH[111]/m0=25/28≈0.892857. These are **not interchangeable physical observables**. Original [Eppenga & Schuurmans, Philips Technical Review 44(5) 137-149 (1988)](https://www.worldradiohistory.com/Archive-Company-Publications/Philips-Technical-Review/80s/Philips-Technical-Review-1988.pdf) discusses GaAs/AlGaAs QW 1–10 nm scale and mass-dependent envelope boundary matching. The article's text was accessible and original screenshot blocked (403), so no figure calibration is claimed.

To make the comparison **measurable** without fabricating paper sample geometry, the new \`scripts/check_gaas_111_qw_mass_confinement_cut.py\` solves an **illustrative symmetric finite square well** with BenDaniel–Duke interface matching \`tan(kL/2)=(m_w/m_b)(κ/k)\`. Stipulated barriers V=0.2 eV and m_barrier=0.9m0. The following are calculations, **not a fit to the original specimen or a predicted optical emission line**:

| width | E_hh finite (using QW-inferred 0.70m0) | E_hh finite (nominal bulk Γ 0.892857m0) | mismatch |
|---|---:|---:|---:|
| 5 nm | 14.023 meV | 11.949 meV | 2.074 meV |
| 8 nm | 6.366 meV | 5.279 meV | 1.087 meV |
| 10 nm | 4.294 meV | 3.525 meV | 0.769 meV |

The **40 local equivalent numerical checks passed**, including positive/finite barrier boundedness, mass dependence, well width, barrier-height monotonicity and explicit negative-input rejection. Exact \`GaAs111QuantumWellConfinementExact.agda\` imports the prior Molenkamp mass discrepancy proof and declares a required **same-specimen** source-backed well thickness, band offsets, interface flux matching, 8-band source, exciton PLE and collected current. No original experimental fit is asserted. Actual 8-band QW/exciton inference is P1d **OPEN**.

**P7 fix: strict conversion threshold.** Original \`MatchedDrivenPVGain\` in \`PVPrimaryConversionMaxCutExact.agda\` incorrectly called weak \`<=\` (allowing zero benefit) "positive." It now requires \`suc(original passive effective output) <= driven effective output\`, a strict +1 smallest-common-unit margin, with passive/driven RF input and recovered RF both signed consistently. No physical witness was inserted.

New \`PV369NetHalfThresholdExact.agda\` imports original motors' inductive natural-number bound, PV energy source, semiconductor continuity and site fibre. A net electrical meter ledger demands \`grossElectric + recoveredDrive = netExport + driveIn + auxDraw\`, then strict \`suc(incidentSolar) <= netExport + netExport\`. Chemical, heat and excitation energy **cannot** be relabelled as electrical output, and equal 50% is rejected by a generic Agda successor-not-less theorem. Entries must share aperture/spectrum/window and power/energy units; independent certification remains a source gate. Source-written; **Agda native kernel check still OPEN**.

**P7 quantified loss tolerance:** previous actual-G173 model optimum for a **3-junction 2-terminal ideal radiative** design 51.741% gives only \`51,741 − 50,000 = 1,741\` per 100,000 solar-power units of headroom before 50%. For a 1000.370656 W/m² AM1.5G input this is **17.416 W/m²**, or **3.3648% of the *ideal output***. The arithmetic is exact for the **model-reported rounded efficiency only**; the gap search was numerical and optical/contact/recombination/temperature losses unmeasured. It is NOT a physical certified multijunction performance claim. The focused formal module explicitly records this distinction and no instance of a real >50% device.

**Highest-alpha remaining gates:** (1) exact kernel verification of all revised import-closure modules and strict Nat inequalities; (2) actual QW specimen data, well thickness, alloy barrier and fitted PLE with exciton/band mixing; (3) full corrected Bahder 1990/1992 common-basis eight-band source, band reference, finite-film screening; (4) same-material measured absorption/EQE/recombination and loaded JV; (5) candidate 369-specific source-predictive operator vs unrelated C3v matched engineering; (6) independently certified >50% **net aperture solar-electric** stack. Continue P3/P4/P5/P6 independently; do not overindex on strained GaAs or heat.


## 17 November P1d finite-well confinement + P7 strict target follow-up

**What the goals actually require:** not just a GaAs [111] energy splitting, but **>50% net aperture solar-electric energy**, independently measured and honestly separated from RF drive/recovery, chemical/fuel, light/heat and other energy ports. The original 369/triadic construction must predict *something physically different* from a coordinate or ordinary C3v symmetry relabeling. Preserve and progress the P3 active/nonlinear/Floquet, P4 multiplication/fission, P5 films/multijunction/current matching and P6 BH4/photosynthetic branches. Thermal is only the supporting auxiliary leg.

**P1d:** Source-attached Molenkamp 1988 QW [111] HH 0.70m0 vs nominal bulk-Γ 25/28 m0 predicts an **illustrative finite-barrier 8nm confinement difference ≈1.087meV**, with 5nm ≈2.074meV and 10nm ≈0.769meV, using an explicitly hypothetical 0.2eV barrier and barrier mass 0.9m0. Original Philips Eppenga/Schuurmans 1988 QW envelope constructor is cited. 40/40 local equivalent numerical tests passed; no same-sample measured PLE fit or full 8-band QW solver, so **P1d empirical CLOSED? NO**. New owners `GaAs111QuantumWellConfinementExact.agda`, `scripts/check_gaas_111_qw_mass_confinement_cut.py`.

**P7 formal acceptance repaired:** earlier `MatchedDrivenPVGain.positiveNetElectricalGain` was *weak*, admitting ties. Now requires a strict successor-≤ margin. `PV369NetHalfThresholdExact.agda` requires same-source net electric port ledger `gross+recovered=net+drive+aux` and **strict** `suc(incidentSolar)<=2*netElectric`, and proves ties cannot satisfy it. Earlier G173 3-junction 2-terminal **ideal radiative model** optimum ~51.741% has only **1.741 percentage points (17.416 W/m²)** above the strict 50% power criterion under one-sun G173, or 3.365% of its ideal output for all losses; not a certified device result.

**369-specific acceptance separated:** `PV369MatchedDevicePhysicalAdvantageExact.agda` requires strict net-electric improvement against conventional same-source material controls AND >50% measured device on the *same candidate*. Reuses `Atomic369BasisTransportNoFreeGainExact`, proving that a mere coordinate transform with equal readout cannot satisfy a strict advantage. Source strings alone do not constitute any observed experimental evidence; no physical instance asserted.

**TOE import graph:** `DASHI/Unified/PVPrimaryTOESpliceExact.agda` imports the new QW, net threshold and matched 369 advantage owners, attached already to the three original TOE roots. No ESD surfaces edited. **Agda kernel acceptance OPEN**. See [Docs/physics/PV369Net50QuantumWellMaxCut20261117.md](PV369Net50QuantumWellMaxCut20261117.md) for formulas, source provenance and required real-device specimens.

**Max-cut next:** use source-specific full (111) quantum-well spectra/barrier profiles and corrected Bahder 8-band model; independently fit measured absorption and extraction, select 369 mechanism predicted by an *actual changed operator* rather than a relabel, and compare against a same-source conventional device. Treat P3–P6 as distinct routes in parallel. Do not call conditional radiative simulations >50% experiment.

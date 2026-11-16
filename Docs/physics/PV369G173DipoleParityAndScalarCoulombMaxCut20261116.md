# Atomic 369 -> optical PV maximum cut: actual ASTM G173, C3, E1 parity and p² scalar Coulomb (16 Nov 2026)

**Scope and priority:** photovoltaic/photochemical energy conversion remains primary; heat/ground/HP/ORC modules are separately referenced auxiliary consumers. Existing [draft PR #1523](https://github.com/chboishabba/dashi_agda/pull/1523). Source written, **Agda kernel check not run**. No real >50% device claim.

## P0: calibrated source, radiative model, rigorous comparison class

Reference ASTM G173-03 authoritative data: [National Laboratory of the Rockies, Reference Air Mass 1.5 Spectra](https://www.nlr.gov/grid/solar-resource/spectra-am1.5). Public GitHub mirror `frssp/atlc/ASTMG173.csv` Git blob `300821f0504ed3069a6af949056f60af378f6fc2`; 2002 spectral rows, 280-4000 nm. Source data not vendored or relicensed.

**Numerical source receipt:** ∫global = 1000.37065557344 W/m²; ∫direct-normal = 900.13932928421 W/m² (trapezoids). These check correctly against the standard, but byte-exact identity to the authoritative hosted XLS/ZIP has not been independently established in this runtime.

Model: independent radiative diode balance at 298.15 K, ideal step-absorber with gap Eg, perfect optical transfer, one front emission hemisphere (perfect rear mirror), `Jph=q ∫_{E>Eg} phi_sun(E) dE`; `J0=q 2π/(h³ c²)∫_{Eg}∞ E²/[exp(E/kT)-1] dE`; `J(V)=Jph-J0 (exp(qV/kT)-1)`. One cell chooses its own maximum power in 4T; 2T cells share ONE current and have independent gap-dependent voltages with perfectly connected series junctions. Perfect selective transfer and no shunts/nonradiative/cell series/contact/optical/RF/thermal losses are highly optimistic assumptions.

Multistart numerical gap search was run against all 2002 wavelength rows in GitHub connector script environment. **Optima not certified global maxima**; three-digit efficiencies are precise numeric receipts for the model/search, not measurement uncertainties. A separately written Python/SciPy verifier is committed at `scripts/check_pv_astm_g173_radiative.py`, requiring the G173 four-column CSV at runtime; its synthetic-source equivalent passed local checks, while full G173 Python rerun is unavailable in the present container.

| Number of junctions | 1 sun global, 4T ideal | 1 sun global, 2T ideal | 665x direct, 4T ideal | 665x direct, 2T ideal |
|---:|---:|---:|---:|---:|
| 1 | 33.773% | 33.773% | 40.437% | 40.437% |
| 2 | 46.177% | 45.824% | 54.188% | 53.911% |
| 3 | 51.867% | 51.741% | 61.354% | 61.126% |
| 4 | 56.077% | 52.162% | 65.590% | 58.286% |
| 5 | 58.532% | 53.553% | 68.566% | 61.485% |

Strong negative controls: 4T >= 2T **for the same gap vector**; do not misattribute separately optimised gaps to electrical wiring alone. At n=3, computed ideal one-sun 4T gaps ~1.995,1.336,0.707 eV, 2T ~1.900,1.367,0.933 eV. At n=4, the 665x DNI ideal 2T gives 58.286% vs 4T 65.59%; device-level output losses can easily change the choice, and the independent 4T ideal includes lossless spectral routing/contact assumption.

Independently certified real-world benchmarks: [Green et al. Solar Cell Efficiency Tables v68](https://doi.org/10.1016/j.joule.2026.102494), 35.2% perovskite/Si 1-cm² (ESTI 2026, one sun) and 47.6±2.6% bonded 4J concentrator at 665 suns (Fraunhofer ISE 2022 result). Do NOT compare direct-normal concentrated versus one-sun global denominators without converting correctly, or call either a current realised 50% photovoltaic device.

## P1a: source-owned C3 conditional optical selection

`Atomic369C3DipoleSelectionExact.agda` imports `AtomicPeriodicTable369MagneticC3PhysicalRealizationExact.agda` and `TriadicDepthOneCharacters.agda`. On the *same* material/optical state, if a dipole operator has (C_3) charge q and true optical covariance, a transition with (m_f ≠ m_i+q mod 3) has zero amplitude, **conditional** on a scalar amplitude representation separating different character phases on nonzero vectors (true in complex vector spaces, not proved here in the symbolic three-phase ring). Source-selected charge +1 cannot connect magnetic m=0 back to m=0. No nonzero-allowed transition follows.

## P1b: the existing interacting p² scalar is a NEGATIVE result for splitting

The source `AtomicPeriodicTable369P2CoulombExecutionExact.agda` produces an actual restricted hydrogenic common-spin (2p^2) Coulomb matrix (V_{ee}=(21/128) I_3), rather than an unconstrained parameter. `Atomic369P2ScalarCoulombOpticalNoGainExact.agda` imports its exact three-basis entries and proves every diagonal is the same source rational, selected off-diagonals vanish, and a general uniform additive energy shift cannot alter an intra-sector level gap.

**Therefore the known nonzero interaction cannot by itself split these selected three levels, modify their eigenvectors or produce a corresponding oscillator-strength advantage within the restricted p² sector.** This does NOT rule out transitions between different configurations, non-scalar terms, correlated states outside projection, crystal fields, defects, stronger driving or particle/hole transport. It identifies precisely why one existing 369 ingredient is insufficient.

## P1c: NIST E1 parity adds a second independent negative control

[NIST Atomic Spectroscopy selection rules](https://www.nist.gov/pml/atomic-spectroscopy-compendium-basic-ideas-notation-data-and-formulas/atomic-spectroscopy): an E1 transition requires a change of inversion parity; with negligible mixing a single electron has Δl=±1. All isolated hydrogenic p-shell (l=1) magnetic states are odd. The source selected two-p orbital configurations have even combined parity. Hence **p→p and p²→p² E1 transitions within fixed-parity isolated inversion-symmetric sectors have zero dipole matrix elements EVEN WHEN C3 charge/m angular rules would allow them.**

`Atomic369PTripletParityE1NoGoExact.agda` imports actual p and p² bases; it checks their parity equality by finite pattern exhaustion, and conditionally proves E1 amplitudes vanish under inversion-odd operator covariance over a characteristic≠2 complex amplitude field. This conditional theorem is stronger than the bare C3 Fourier square but does **not** apply to an inversion-breaking real crystal, interface, defect, parity-mixed state, opposite-parity valence/conduction bands or higher multipole transition. A real diamond NV C3v defect is a positive candidate for the *broken inversion* regime; [2025 NV optical readout report](https://pubs.aip.org/aip/apl/article/126/19/194003/3346962/Optical-and-electrical-readout-of-diamond-NV) reports genuine 637 nm A/E optical excitation and multi-step ionisation, not a solar-PCE measurement.

**Max-cut consequence:** the 369 p-shell C3 Fourier representation is a symmetry calculator, NOT a device absorber without physical opposite-parity, material band and dipole attachment. The precise viable path is to add an `s↔p`, `p↔d`, mixed-parity or crystal Bloch/defect valence↔conduction transition on the same source-resolved material carrier.

## Exact source-to-physical remaining lemmas, prioritised

- `atomic369PhysicalOpticalStateSpaceSameCarrier`: explicitly identify material and periodic/finite cell orbitals, complex amplitudes, Bloch/defect eigenstates; do not identify general C3 translation with literal spatial rotation in the same basis.
- `atomic369SourceSelectedOppositeParityDipoleNonzero`: a source-certified material band/defect eigenpair with nonzero dipole matrix element and calibrated oscillator strength satisfying proper point-group selection, not bare C3 and not purely same-shell p².
- `materialC3SymmetryBreakingComparatorSameSpectrum`: compare symmetry-preserving and broken states on SAME physical Hamiltonian/chemistry/geometry and same incident photon field; allow either increase or decrease in usable work.
- `materialAbsorptionToCollectedCarrierTransport`: actual EQE, trap/Auger/radiative and nonradiative rates, contact I–V and operating MPP, as defined by existing semiconductor continuity formalism.
- `fieldDrivenOpticalNetWorkWithRetardedSource`: actual time-resolved Stark/Floquet optical matrix, field amplitude, signed RF energy and PV work with matched static/dark/fixed-bias controls.
- `multiplicationVoltageWorkBound`: >1 collected carrier per photon is measured independently of electrical work; same photon spectrum, output voltage and energy inputs.
- `bioPhotosystemBH4RatesAndProductAllocation`: original photon->redox->EET/carbon/fuel/respiration/repair rates, imposed bias vs autonomous output, chemical energy and biological lifetime.
- `astmG173ApertureNetPCEAndBenchmark`: standard global vs DNI denominators, series vs independent extraction and actual optical/parasitic losses, independently checked >50% test.

**Local Agda Golden acceptance remains OPEN**: no Agda executable in current container, and importing the draft modules into TOE roots is not a typechecking receipt. Theoretical >50% from this radiative ideal model is NOT device efficiency and does not settle the optical+physics gates.

## Provenance and original authorship

- Existing atomic source owner: AtomicPeriodicTable369GenerativeExact, FourierSpatialRestrictionExact, P2CoulombExecutionExact, original PR #1194; NIST/DLMF original hydrogenic angular/radial authorities.
- Spectrum: NLR (formerly NREL) ASTM G173-03, original model Gueymard SMARTS 2.9.2, GitHub mirror `frssp/atlc` used as transport only; no implied endorsement.
- Independent PV efficiency: Green et al., 2026; Fraunhofer/ESTI certification, DOI above.
- Optical selection: NIST Atomic Spectroscopy; real NV defect source cited above.
- Earlier field-assisted QD, Franz–Keldysh, fission, engineered biology and thermal provenance remain in `PV369PrimaryConversionNotThermalMaxCut20261116.md` and original source files; no need to repeat or reattribute those to DASHI.

## P3 first source-spectrum break-even bound for Stark/RF modulation

Against the **actual G173 one-sun global spectrum**, the same radiative-only single-junction diode model gives the following gross idealised electrical output if (counterfactually) a field-induced *optical* gap shift could be treated as a **fully collected electrical absorption-edge** shift:

| Counterfactual effective gap | Baseline ideal W/m² | Shifted ideal W/m² | Most NET actuator + aux work allowable before gain disappears |
|---|---:|---:|---:|
| GaAs-like 1.424 -> 1.350 eV | 331.806 | 337.279 | **5.473 W/m²** |
| GaAs-like 1.424 -> 1.336 eV | 331.806 | 337.853 | **6.047 W/m²** |
| hypothetical dot 2.000 -> 1.800 eV | 228.845 | 272.119 | **43.274 W/m²** |
| hypothetical dot 2.000 -> 1.500 eV | 228.845 | 321.567 | **92.721 W/m²** |
| hypothetical dot 2.000 -> 1.400 eV | 228.845 | 334.988 | **106.142 W/m²** |
| control 2.000 -> 2.000 eV | 228.845 | 228.845 | **0.000 W/m²** |

These are **optimistic break-even thought experiments**, not real Stark-device predictions, and not a thermodynamic upper bound independent of the stipulated model. An observed THz optical Stark shift does **NOT** establish that a dot has acquired corresponding long-lived electrical states, useful contacts, or a new fully collecting step-absorption edge. Driving at a very large peak field during picosecond pulses does not mean those fields can be sustained with a small mean energy input under natural sunlight. The >0.5 eV observation is Pein et al. 2017, https://doi.org/10.1021/acs.nanolett.7b01837 , and must retain its actual transient optical character.

The useful discriminator is conditional:
`P_net,drive - P_net,passive = ΔP_radiative_ideal - P_RF,net - P_transport_and_spectral_loss - P_aux`.
If independently measured `P_RF,net` alone exceeds the optimistic gross `ΔP`, the driven device cannot win under that assumed material-output mapping. In a multijunction tandem, lowering one junction's gap can *steal* photons from another, so a single-junction positive number is **not** an additive tandem gain; recompute the whole transfer+series/4T system.

Reproducible source: `scripts/check_pv_astm_g173_radiative.py` now also emits `hypothetical_stark_gross_break_even` with the same specified ideal model. NIST E1 parity and scalar p²-Coulomb negative controls were separately added to `scripts/check_pv_c3_optical_discriminator.py`. Existing 31 local finite test claims refer to the earlier script; **three new negative-control assertions were exercised in an equivalent standalone local calculation, but the modified GitHub checker was not rerun from a working checkout**. Local proof-kernel acceptance remains open.

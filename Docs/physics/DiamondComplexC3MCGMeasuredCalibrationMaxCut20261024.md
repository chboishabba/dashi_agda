# Complex C3 optical-interference and **measured** NV MCG source-calibration cut

Date: 2026-10-24. Diamond PR #1238; related 369/YM, NS ABCD, Shor and TSFV work.

## Source coordinates, exact information known

Primary: Muhib Omar et al., *Human cardiac measurements with diamond magnetometers*, Science Advances 12(38), eaeg5281 (electronic 2026-09-16), DOI 10.1126/sciadv.aeg5281; NIH PMC13580569. Three independent instrument platforms.

- ZAQuant: reported **measured** aggregate magnetic-field sensitivity 7 pT/sqrt(Hz), time trace 60 s. Diamond 0.5 x 0.5 x 0.5 mm, approximately 1 mT static bias, MW frequency modulation. Subject ~1 cm from sensor head in MCG recording.
- Q.ANT: reported **measured** aggregate sensitivity 26 pT/sqrt(Hz), time trace 10 s. Diamond 1 x 1 x 0.5 mm, approximately 1 mT bias, MW amplitude modulation, approximately 100 mW optical pump power during those measurements.
- JGU: zero-bias field-modulation protocol (6.12 kHz), MW central frequency 2.87 GHz mixed with 2.16 MHz RF for hyperfine address; diamond 0.5 x 0.5 x 0.18 mm, head diameter ~12 mm. Do **not** attribute the ZAQuant/Q.ANT sensitivity figures to JGU.
- Optical collection described by diamond/concentrator and 695 nm long-pass, photodiode readout for the relevant implementation; source-specific applicability must be maintained.
- The quoted sensitivities are observed **system** noise figures and are not identical to theoretical photon shot noise.

Additional standard NV sensitivity reference: *Optimizing NV magnetometry for Magnetoneurography and Magnetomyography applications* (Frontiers in Neuroscience 2022/2023), explaining η≈P Δν/(γ_e C sqrt(R)). The 2026 Science Advances paper distinguishes geometries, optical and MW implementations, and environmental disturbances.

## Implementation

`DASHI/Physics/QuantumSensors/NVComplexC3NSBornExact.agda` derives three-channel complex Gaussian-rational coherent intensity, nonnegative-squared-norm *definition*, signed pair cross terms 2 Re(a conjugate b), C3 invariance, and the full algebraic intensity/cross-term decomposition; the NS ABCD signed pair-difference theorem is instantiated **on the generated complex cross terms**.

`scripts/check_nv_complex_ym369_c3_experiment.py` provides SymPy rational/exact-symbolic tests for the same complex/C3/NS identities, plus an ideal weak-contrast Lorentzian FWHM optical-sensitivity formula. Source-literal field sensitivities are encoded solely as observed anchors, never reverse-fitted to invented linewidth, photon rate or optical contrast.

For Lorentzian FWHM Δν, contrast C, off-resonance photon rate R, and |γ| in Hz/T:
  η_shot ≈ 4/(3 sqrt(3)) * Δν/(|γ| C sqrt(R)).
This is the conventional approximate CW-ODMR sensitivity, with assumptions: Poisson fluorescence counts, Lorentzian line, small contrast, stationary constant background, neglect of technical noise, operating near maximal slope. Actual sensitivity must use measured noise spectral density and empirical fluorescence-versus-B slope, e.g.
  η_system(f) = sqrt(S_signal(f)) / |d(signal)/dB|(f),
with carefully defined one-sided PSD/filter bandwidth conventions. For lock-in/frequency-modulation protocols, the transfer function is not simply the unmodulated CW Lorentzian derivative.

## Why the physical calibration frontier remains genuinely open
To reproduce reported system sensitivities from first principles, acquire exact instrument-specific measured photon/photo-current rate, optical filter and collection efficiency, ODMR spectral linewidth and contrast (or raw scan curves), bias and microwave modulation transfer, detector gain/nonlinearity, electronics noise/lock-in bandwidth, noise PSD and analysis window. Actual human cardiac time streams and pose/geometry are additionally required to reconstruct biological currents. Source report values constrain a model, but **do not independently determine these parameters** (nonidentifiable from one sensitivity scalar). Raw human data are not inferred from the public abstract.

A reproducible audit of the supplementary source (sciadv.aeg5281_sm.pdf, sections S1-S4, figs S1-S17, table S1) is a next acquisition target; its presence in the paper does not imply contents were inspected here.

## Attribution / firewall

- Classical complex interference, C3 permutation and QFT theory belong to established quantum optics/DFT mathematics; Shor/NS/YM/TSFV repo authorship maintained.
- NS ABCD signed work is an algebraic donor, not a borrowed Navier–Stokes PDE estimate or Clay result.
- 369/YM spatial C3 is a separate physical carrier; we proved symmetry on optical amplitudes, **not** a map between YM fields and diamond optics.
- Measured system figures attributed to Omar et al. 2026 rather than produced by the model.
- No assumption that Candidate256 TSFV action equals physical S/ℏ, or that optical interference proves optogenetic or mitochondrial quantum coherence.
- No CI or kernel check; files are source-written unless independently checked.

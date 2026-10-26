# Instrument-specific real-data calibration cut — 2026-10-24

## Public experimental source and status
Omar et al., *Human cardiac measurements with diamond magnetometers*, Science Advances (published 2026-09-16), DOI 10.1126/sciadv.aeg5281, PMC13580569.
The published paper reports full-system sensitivities ZAQuant 7 pT/sqrt(Hz), Q.ANT 26 pT/sqrt(Hz), and JGU approximately 13 pT/sqrt(Hz in the 20-30 Hz band); sensor architectures and demodulation protocols differ. The paper's arXiv preprint reports 6-26 pT/sqrt(Hz across platforms. The JGU 13 value is explicitly band-specific. Do not infer a universal calibration from these scalar summaries.

The raw-data repository catalog exists: Omar et al., *Human Cardiac Measurements with Diamond Magnetometers*, Figshare dataset DOI 10.6084/m9.figshare.32677068.v1, https://figshare.com/articles/dataset/Human_Cardiac_Measurements_with_Diamond_Magnetometers/32677068 . Dataset file content could not be inspected through available web access (HTTP 403), hence NO claim of having read measured ODMR/photo-current series.

## Exact executable forward/inverse instrumentation
`scripts/nv_mcg_instrument_calibration.py` ingests an instrument-specific *actual measured* `frequency_hz,signal` CSV and/or `time_s,signal` CSV.
- Fits baseline minus Lorentzian dip (positive depth), reporting center, FWHM, contrast, fit RMS and analytic maximal frequency derivative;
- Computes one-sided Welch PSD and median amplitude spectral density in an explicitly specified frequency band, Hann window; makes sampling/timing and minimum-data assumptions explicit;
- Converts ASD to pT/sqrt(Hz) **only when an independently measured instrument-specific output-per-tesla demodulated slope is provided**. MW frequency/amplitude modulation and JGU field modulation forbid substitution of a static ODMR derivative for this real measured transfer by default;
- Preserves original publication sensitivity anchors solely for comparison and emits null rather than inventing a predicted/calibrated sensitivity in their absence;
- Captures input domains, numbers of samples and numerical fit residuals in JSON output. No extrapolated medical waveform or retrospective invented detector time series.

`tests/test_nv_mcg_instrument_calibration.py` defines reproducible SYNTHETIC fixtures of Lorentzian fitting and noise PSD units, independently distinguishable from experiment. Test command:
`python -m unittest discover -s tests -p test_nv_mcg_instrument_calibration.py`.
Calibration needs numpy and scipy. CI skipped. Kernel check is not required for Python audit.

Example:
`python scripts/nv_mcg_instrument_calibration.py --instrument JGU --odmr real_jgu_odmr.csv --noise real_jgu_noise.csv --slope-signal-per-tesla MEASURED_VALUE --output calibration.json`
Never substitute a guessed slope for `MEASURED_VALUE`. For ZAQuant/Q.ANT give an appropriate `--band f0 f1`.

## Physics/math programme weld
The instrument calibration is a **boundary producer** for the repo's existing `NVFiveLevelOpticalMasterExact` radiative readout, `NVComplexC3NSBornExact` interference and the Shor/TSFV Fourier history owners. A fit to CW ODMR does not establish microscopic five-state rate constants uniquely. Quantum interference in a three-path toy model is not a substitute for the loss of spin coherence in actual NV fluorescence. Full material calibration remains conditional on data provenance, detector gain, photodiode response, demodulator phase and frequency, human field-source geometry, and measured system noise.

The next scientific discriminator is model-vs-real measured residuals *on the same source object*, with calibrated transfer, uncertainty estimates and held-out time/frequency segments. Data discovery is not data validation. Attribution preserves Omar et al. and original NV/optics/NS/YM/TSFV/QFT prior art.

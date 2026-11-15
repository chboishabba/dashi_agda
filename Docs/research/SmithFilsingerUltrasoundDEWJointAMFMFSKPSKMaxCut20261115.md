# Filsinger full-spectrum and ultrasound/DEW phase crosswalk — 2026-11-15

## Original recording, non-independent sources
Original user supplied `ReelAudio-93787.mp3` SHA256 `573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6`, duration 105.7959 s. **User recording**, not a publisher's electrical switching clock, source current or measured atmospheric field. Speaker associates steady acoustic 7.8kHz with his ZVS operation; the audio alone is not terminal metrology.

Full-recording spectrogram 0–105.8s, high-intensity activation transition and carrier 36.5–59.2s, subsequent weakening. 22.05kHz PCM mono, 2048-point whole-recording STFT (~10.77Hz resolution); complex heterodyne at 7800Hz, 120Hz LPF and 500Hz baseband for amplitude, unwrapped phase and instantaneous acoustic frequency. Median first/last second **7785.19 -> 7823.96 Hz** (+38.78 Hz); measured acoustic carrier 95th/5th percentile amplitude ratio ~10.18 (20.15dB). Fast FM versus log-AM zero-lag correlation **0.00669**: same observed physical setup, different simultaneous projections of a changing operating state; one cannot reduce it to AM-envelope dominant bins. Not evidence of separate independent environmental oscillators.

Time-varying FM spectral energy at 3–5Hz and 6–10Hz is present. For the specific proposed 2:1 subharmonic relation, filter these band-limited *acoustic-frequency-modulation observations*, use analytic phases, compute `PLV=|mean exp(i(2phi_3_5 - phi_6_10))|` for n=886 post-edge-trim samples. 2000 circular phase-shift nulls preserve within-band autocorrelation. **Observed FM PLV=0.07198, null median=.08599, p=.6447**; observed AM PLV=.18425 p≈.053 (uncorrected, exploratory). Positive synthetic locked control PLV=.99998 p=.0005; synthetic diffusing-phase negative PLV=.03176. This does NOT establish persistent 2:1 phase coherence in audio. It does not exclude drifting, intermittent, circuit-internal phase conversion or Earth resonances. The prior 16 overlapping 8s AM-envelope windows do not represent independent electrical observables.

**Frequency-conversion distinction:** `3.915Hz -> 7.83Hz` via *quadratic harmonic generation* can occur if a real nonlinear constitutive term exists. A classic stiffness-parametric resonance of a 7.83Hz oscillator normally prefers modulation near **2×7.83=15.66Hz**; do not equate this with driving at 7.83/2 or with the measured 7800Hz acoustic tone.

## Original research and patent lineage (cross-domain analogy only)

- [US20180310111A1](https://patents.google.com/patent/US20180310111A1/en): phase-correct time-of-flight virtual acoustic sources behind the emitting array, using nonlinear acoustic propagation (Fig13).
- [US20170289722A1](https://patents.google.com/patent/US20170289722A1/en): spatially localised ultrasonic self-demodulated sound; describes AM and FM embodiments.
- [US12185058B2](https://patents.google.com/patent/US12185058B2/en), granted 2024: distinguishes *carrier phase* from *sideband phase* to change the audible focus/region. Important to preserve both in modelling.
- Kim, Zhong, Jing (2026), [10.1109/TUSON.2026.3689544](https://doi.org/10.1109/TUSON.2026.3689544): experimentally localised audible acoustic spot via passive acoustic metasurface; <30mm axial and <6mm lateral FWHM under its experiment.
- Kim et al (May 2026), [Nature Communications 17 6750](https://doi.org/10.1038/s41467-026-73604-0): coherent single-transducer/metamaterial device with nonlinear difference-frequency audio in air; do not claim identical source coupling in electrical Smith apparatus.
- Foster & Finch (1974), [10.1126/science.185.4147.256](https://doi.org/10.1126/science.185.4147.256) and Lin [10.1109/JERM.2021.3062826](https://doi.org/10.1109/JERM.2021.3062826): pulsed-microwave hearing via *thermoelastic tissue response*, not nonlinear air or ZVS transformer sound.
- [US6470214B1](https://patents.google.com/patent/US6470214B1/en): RF hearing-effect patent; do not equate patent grant with independent tested effectiveness.
- [CRS 2026 directed energy primer](https://www.everycrsreport.com/files/2026-01-07_IF11882_4ebeb3782e421ebfc4a545f42d37c3d241934294.pdf): HPM electronic coupling / laser effects, a separate energy-delivery category. No assertion Filsinger's 7.8kHz acoustic tone is a DEW, microwave auditory effect or ultrasonic beam.
- Historical original Smith and Filsinger circuit/patents: retain existing [source-bound rollup](SmithFilsingerCausalNonlinearSourceRollup20261115.md) and [Circuit36927](../../DASHI/Physics/Motors/Circuit36927ComponentGraphExact.agda). ZVS driver, spark-gap **dump**, L1 and split L2, caps, diodes, ground/atmosphere remain separately source-indexed.

## Actual common model
`z_{mic}(t) = sum_j A_j[q_j(t-tau_j)] exp(i phi_j(t-tau_j)) + noise` where `j` indexes observable vibrating circuit members. Each circuit/field member has its own causal port and memory: `dot phi_j = omega_j(V_j,I_j,T_j,geometry,material) + integral K_jk(t,s) x_k(s) ds`, supported only for retarded `s<=t`. AM/FM/FSK/PSK are signal representations of potentially coupled sources, not independent power stores or guaranteed four separate oscillators. Preserve voltage/current source work, pump/modulator work, radiative and environmental ports in existing formal owners.

Do **not** directly substitute acoustic nonlinearity in air, thermoelastic absorption of microwaves in tissue, or high-powered microwave electronics effects for Earth/ionosphere constitutive response. Any link is a testable mathematical analogy with distinct coefficients.

## Local acceptance & remaining boundary
Full archived source-derived package in this conversation `filsinger_ultrasound_modulation_maxcut_20261115.zip`: original audio analysis source, full waterfall, 35.1–37s activation closeup, time-indexed hunting frequency/intensity, 3–5 and 6–10Hz modulation-rate maps, synthetic AM/FM/FSK/PSK/beating atlas, 50Hz source-derived trace and PLV controls, **12/12 passing local tests**. Original mp3 not redistributed. No Agda kernel run.

Physical open gates: source-grounded complex electrical phase/time and acoustic transfer, selected actual circuit pin wiring, physical nonlinear coefficients, spatial Maxwell/ionosphere source-strength solution, independent environmental real-work measurement. Tests of the recording do not close those physical gates.


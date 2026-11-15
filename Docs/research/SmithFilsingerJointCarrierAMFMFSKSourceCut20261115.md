# Filsinger sustained tone — joint AM/FM/PM/FSK inverse update (2026-11-15)

## Correction to earlier interpretation

Prior `filsinger_dynamic_modulation_audit` (16 overlapping eight-second windows, hop two seconds, 36–75 seconds) ranked **only the PSD of the amplitude envelope** of the bandpassed sound. The report's "13 windows strongest at 0.6–2Hz, three at 3–5Hz" **does not constrain the dominant rate of frequency or phase modulation**. In particular, weak-carrier 60–75s observations contaminate its spectrum. Never count those 16 windows as 16 independent controls. Nor does fitting envelope strength to a hypothetical 7.83Hz resonance test complex field coupling.

## Original source and extraction
Source: user-supplied original `ReelAudio-93787.mp3` (105.795875s, 44.1kHz stereo, local SHA256 `573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6`). New local source-derived analysis restricts to carrier-active **36.5–59.2s**. Decode to mono 22050Hz; complex demodulate near 7800Hz; low-pass 120Hz to remove image; resample to 500Hz complex baseband. Extract amplitude and unwrapped analytic phase, compute instantaneous frequency from time derivative of phase; remove slow (<0.3Hz) operating-point drift and calculate matched 8s Welch PSD for faster frequency and log-amplitude fluctuations.

| rate range (Hz) | AM log-amplitude-fluctuation power | FM fluctuation power (Hz²) |
|---|---:|---:|
| 0.6–2 | 0.07290 | 3.02 |
| 3–5 | 0.02765 | 3.17 |
| 6–10 | 0.01260 | 2.96 |

In **48–59.2s** only, 3–5Hz FM 5.66Hz² vs slow 0.6–2Hz FM 4.81Hz²; AM remains slow-dominant (.0872 vs .0294). The actual acoustic carrier near 7.8kHz moves ~7785.18 -> 7823.97Hz across the active window (~+38.78Hz; +0.498%). If frequency directly tracks ideal LC parameters this corresponds to **−0.989% effective LC product**, not a verified actual coil inductance change or ZVS electronic frequency. Strong falling carrier after ~60s means ridge pickers become unreliable if analysis continues indiscriminately.

These measured phase changes could result from **continuous FM/PM, phase-continuous FSK, multimode beating, load changes or combinations**. The acoustic phase is a net source-and-transducer observable, not a direct calibrated voltage/current or natural-source-work measurement.

## Correct full-system steelman and observation model
For component-specific causal states `z_j(t)` (driver, spark gap as dump, core, capacitance banks, rectifiers, earth return, atmospheric modes), treat the actual sound as a complex multicomponent observation rather than independent AM envelope peaks:
`mic(t)=Re Σ_j A_j(z_j(t−τ_j)) exp(i θ_j(t−τ_j))+ noise`, where
`dθ_j/dt = ω0j + α_j V_j(t)^2+β_j I_j(t)^2+γ_j M_j(t)+Σ_k K_jk[z_k](t−τ_jk)`.
Delay, nonlinear carrier pulling, time-modulated reactance, mode mixing and causal source backaction remain simultaneously active. A local microphone's slow-envelope air-flight lag can be negligible at ~1m while electrical/ground/planetary port delays are not.
A synthetic **single** complex oscillator with slow AM 1.125Hz and fast FM3.9Hz reproduces the old slow-AM/fast-FM ranking. Local `check_smith_filsinger_joint_am_fm_fsk.py`: **6/6 tests passed** (pure AM, pure FM, combined, phase-continuous FSK, multimode beating, chirp). It is a negative control against treating envelope bins as distinct natural modes.

## Consequences for formal and physical gates
- Previous `acousticAloneCannotIdentifyNaturalSource` remains valid for environmental power identity, but does not license throwing away phase history, modulation and relative carrier dynamics.
- Coupled dynamics and causal Maxwell port owners still needed to fit a **common time-indexed physical system**: `Circuit36927`, switch-state, recovery-energy bound, Smith/Filsinger BIDI and MaxwellExteriorCalculus.
- The audio observation law must be promoted to an explicit source-specific **complex signal** with measured/fitted mechanical transfer; output current/phase, environmental source work and actual electrical clock are not uniquely calibrated from this mono microphone recording.
- This does **not** validate Schumann capture or dismiss it: the previous 16-window amplitude-strength fit was inappropriate to distinguish time/phase-indexed external entrainment.
- Full local deliverable: `filsinger_joint_am_fm_20261115.zip` including original-audio processing code, time-stamped 50Hz complex derived features (no original audio redistribution), plot, band/segment controls and tests.
